/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Normalized

/-!
# The rescaled Frostman window has to be truncated at `1/4`

`Kakeya.ml1Boot.exists_fineNormalization_lower`(iv) and
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) assert, for **every** rescaled scale
`ρt ∈ [δ̃ ^ (1 - 5 ε), δ̃ ^ (5 ε)]`, the existence of an honest `ρt`-tube `Tρ` with
`Tρ ⊆ B(0,1)` carrying a Frostman lower bound.  This file shows that the range of `ρt` is
too wide for the *first* of those clauses, independently of anything Frostman:

* `Kakeya.ml1Boot.Tube.radius_le_half_of_carrier_subset` — a `ρ`-tube inside the closed unit
  ball has `ρ ≤ 1/2`.  A tube has core length exactly `1`, so both endpoint balls
  `B(x, ρ)`, `B(y, ρ)` sit inside `B(0,1)`, giving `‖x‖ + ρ ≤ 1`, `‖y‖ + ρ ≤ 1` and hence
  `1 = dist x y ≤ ‖x‖ + ‖y‖ ≤ 2 - 2 ρ`.
* `Kakeya.ml1Boot.item_iv_false_of_half_lt` — consequently item (iv) is **false** at any
  `ρt > 1/2` of its window, for any nonempty output index set.
* `Kakeya.ml1Boot.exists_scales_window_above_half` — and the window does reach above `1/2`
  inside the hypotheses of `Kakeya.ml1Boot.exists_fineNormalization_lower`:
  at `ε = 1/100`, `δ = (1/4) ^ 100`, `τ = 1/8`, `θ = 1/2` every scale hypothesis of that
  lemma holds, `δ̃ = fineScale τ θ = 1/4`, and the upper endpoint
  `δ̃ ^ (5 ε) = (1/4) ^ (1/20) = 2 ^ (-1/10) > 1/2` is itself in the window.
* `Kakeya.ml1Boot.conclusion_unsatisfiable_of_window_above_half` — the full conclusion of
  `Kakeya.ml1Boot.exists_fineNormalization_lower` is then unsatisfiable.

The two clause-level lemmas above quote item (iv) at its **pre-truncation** form, which is what
this repository asserted before the truncation described next was added; they are the reason the
truncation is there, and they are what any future widening of the window would have to contend
with.

So the statement of item (iv) has to be truncated.  The truncation to use is `ρt ≤ 1/4`:
that is exactly `Tube.IsRescalingSituation.out_le_quarter`, the hypothesis under which
`Tube.rescale_outer_tube` — through
`Kakeya.ml1Boot.exists_rescaled_source_container`, the only route to the container tube
`Tρ` — produces a tube in the unit ball at all.

The truncation costs the consumers nothing in the limit they are quantified in:
`Kakeya.ml1Boot.window_le_quarter_of_le_rpow` shows the whole window lies below `1/4`
as soon as `δ̃ ≤ (1/4) ^ (1 / (5 ε))`, and every call site quantifies `δ` through
`∀ᶠ δ in 𝓝[>] 0` with `δ̃ ≤ δ ^ ε`, so the hypothesis is eventually vacuous.  The defect
was therefore a statement defect in a range of scales the consumers do not use, and not a
defect of the mathematics.  The truncation is now in place: item (iv) of both
`Kakeya.ml1Boot.exists_fineNormalization_lower` and
`Kakeya.ml1Boot.exists_normalizedMiddleData` carries `ρt ≤ 1/4`, and both consumers discharge it
from one extra eventual clause `δ ^ ε ≤ (1/4) ^ (1 / (5 ε))` of
`Kakeya.ml1Boot.middleFactor_eventually` resp. `Kakeya.ml1Boot.middleAvg_scale_eventually`, so
their forwarded endgame hypotheses are unchanged.  At moderate scales — `dt` close to `1/4` with
`ε` small — the truncated clause is *vacuous*, its window being empty; at the scales the
consumers use it is not.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a closed ball `B(x, r)` of a normed space over `ℝ` sits inside `B(0, R)` then
`‖x‖ + r ≤ R`.  The point `x + r • x / ‖x‖` (or `r • u` for a unit vector `u`, when `x = 0`)
realises the bound; nontriviality of `E` is what supplies the unit vector. -/
theorem norm_add_le_of_closedBall_subset [Nontrivial E] {x : E} {r R : ℝ} (hr : 0 ≤ r)
    (h : Metric.closedBall x r ⊆ Metric.closedBall (0 : E) R) : ‖x‖ + r ≤ R := by
  by_cases hx : x = 0
  · subst hx
    obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E (by norm_num : (0:ℝ) ≤ 1)
    have hmem : r • u ∈ Metric.closedBall (0 : E) r := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, hu, abs_of_nonneg hr]
    have hthis := h hmem
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hr] at hthis
    simpa using hthis
  · have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    set u : E := (‖x‖)⁻¹ • x with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul]
      simp [inv_mul_cancel₀ (ne_of_gt hxn)]
    have hmem : x + r • u ∈ Metric.closedBall x r := by
      simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, hun, abs_of_nonneg hr]
    have hle := h hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hle
    have heq : x + r • u = (1 + r / ‖x‖) • x := by
      rw [hu, smul_smul, add_smul, one_smul]
      congr 1
    rw [heq, norm_smul] at hle
    have hpos : (0:ℝ) ≤ 1 + r / ‖x‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos] at hle
    calc ‖x‖ + r = (1 + r / ‖x‖) * ‖x‖ := by field_simp
      _ ≤ R := hle

/-- **A tube inside the closed unit ball has radius at most `1/2`.**

`Kakeya.Tube` fixes the core length at `dist x y = 1` (`Tube.dist_eq_one`) and the carrier
contains the two endpoint balls `B(x, ρ)` and `B(y, ρ)`.  If the carrier lies in `B(0,1)`
then `‖x‖ + ρ ≤ 1` and `‖y‖ + ρ ≤ 1`, while `1 = dist x y ≤ ‖x‖ + ‖y‖`. -/
theorem Tube.radius_le_half_of_carrier_subset [Nontrivial E] [ProperSpace E] {ρ : NNReal}
    (T : _root_.Tube ρ E) (h : T.carrier ⊆ Metric.closedBall (0 : E) 1) : (ρ : ℝ) ≤ 1 / 2 := by
  have hx : Metric.closedBall T.x (ρ : ℝ) ⊆ T.carrier := by
    rw [T.carrier_eq]
    exact Set.subset_biUnion_of_mem (u := fun z => Metric.closedBall z (ρ:ℝ))
      (left_mem_segment ℝ T.x T.y)
  have hy : Metric.closedBall T.y (ρ : ℝ) ⊆ T.carrier := by
    rw [T.carrier_eq]
    exact Set.subset_biUnion_of_mem (u := fun z => Metric.closedBall z (ρ:ℝ))
      (right_mem_segment ℝ T.x T.y)
  have hxb := norm_add_le_of_closedBall_subset (NNReal.coe_nonneg ρ) (hx.trans h)
  have hyb := norm_add_le_of_closedBall_subset (NNReal.coe_nonneg ρ) (hy.trans h)
  have hd : dist T.x T.y = 1 := T.dist_eq_one
  have h1 : (1:ℝ) ≤ ‖T.x‖ + ‖T.y‖ := by
    rw [← hd, dist_eq_norm]
    exact norm_sub_le _ _
  linarith

/-- **No tube of radius above `1/2` fits in the closed unit ball.** -/
theorem Tube.not_carrier_subset_closedBall_of_half_lt [Nontrivial E] [ProperSpace E]
    {ρ : NNReal} (hρ : 1 / 2 < (ρ : ℝ)) (T : _root_.Tube ρ E) :
    ¬ T.carrier ⊆ Metric.closedBall (0 : E) 1 := fun h =>
  absurd (Tube.radius_le_half_of_carrier_subset T h) (not_le.mpr hρ)


/-- **The segment of a tube stays in a ball its endpoints do.** -/
theorem Tube.segment_subset_closedBall [ProperSpace E] {dt : NNReal} (T : _root_.Tube dt E)
    {c : ℝ} (hx : ‖T.x‖ ≤ c) (hy : ‖T.y‖ ≤ c) :
    segment ℝ T.x T.y ⊆ Metric.closedBall (0 : E) c := by
  refine (convex_closedBall (0 : E) c).segment_subset ?_ ?_
  · simpa [Metric.mem_closedBall, dist_zero_right] using hx
  · simpa [Metric.mem_closedBall, dist_zero_right] using hy

/-- **A rescale of a tube whose endpoints are `c`-close to the origin lies in `B(0, c + ρt)`.**
The carrier of `Tube.rescale T ρt` is the `ρt`-thickening of the core of `T`, and the core
lies in `B(0,c)` by convexity of the ball. -/
theorem Tube.rescale_carrier_subset_closedBall [ProperSpace E] {dt ρt : NNReal}
    (T : _root_.Tube dt E) {c : ℝ} (hx : ‖T.x‖ ≤ c) (hy : ‖T.y‖ ≤ c) (h : c + (ρt : ℝ) ≤ 1) :
    (T.rescale ρt).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  have hseg := Tube.segment_subset_closedBall T hx hy
  intro w hw
  rw [(T.rescale ρt).carrier_eq] at hw
  simp only [Set.mem_iUnion, exists_prop] at hw
  obtain ⟨z, hz, hwz⟩ := hw
  have hzs : z ∈ segment ℝ T.x T.y := by
    simpa [_root_.Tube.rescale, _root_.Tube.mk'] using hz
  have hzc : ‖z‖ ≤ c := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hseg hzs
  have hwzd : ‖w - z‖ ≤ (ρt : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hwz
  have : ‖w‖ ≤ c + (ρt : ℝ) := by
    calc ‖w‖ = ‖z + (w - z)‖ := by abel_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ c + (ρt : ℝ) := by linarith
  simpa [Metric.mem_closedBall, dist_zero_right] using this.trans h

/-- **The container tube of item (iv), built from the member instead of from the source
container.**

The second obstruction recorded in the docstring of
`Kakeya.ml1Boot.exists_fineNormalization_lower` — "there is no `ρt`-tube to state the
conclusion at" — has a cheap resolution that needs neither `Tube.rescale_outer_tube` nor the
`centredExtension` of the source container: the *member* `T̃ k` is already a tube of core
length `1`, so its own rescale to radius `ρt ≥ dt` is an honest `ρt`-tube containing it.  What
this costs is positional information about the normalized member's core, `‖x‖, ‖y‖ ≤ c` with
`c + ρt ≤ 1`, which the construction has (it places `Ψ(T_θ)` inside `B(0,1/4)`) but which
`Kakeya.ml1Boot.exists_fineNormalization` does not currently expose; `T̃ k ⊆ B(0,1)` alone
gives only `‖x‖, ‖y‖ ≤ 1 - dt`, which is not enough once `ρt > dt`.

The `ρt`-tube produced here keeps the member's core, so it is *not* the source container's
image; the Frostman content of item (iv) then has to be transported from `Ψ(T_σ)` to the
`2`-dilate of this tube.  That is the one remaining leaf, and it is a container change between
two volume-comparable bodies, not a subfamily transfer. -/
theorem exists_container_tube_of_endpoints [ProperSpace E] {dt ρt : NNReal} (hdtρ : dt ≤ ρt)
    (T : _root_.Tube dt E) {c : ℝ} (hx : ‖T.x‖ ≤ c) (hy : ‖T.y‖ ≤ c) (h : c + (ρt : ℝ) ≤ 1) :
    ∃ Tρ : _root_.Tube ρt E, Tρ.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      T.toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧ Tρ.x = T.x ∧ Tρ.y = T.y :=
  ⟨T.rescale ρt, Tube.rescale_carrier_subset_closedBall T hx hy h,
    _root_.Tube.le_rescale T hdtρ, rfl, rfl⟩

/-- **The container tube at the truncated window, from a normalized core in `B(0,1/4)`.**

`Kakeya.ml1Boot.exists_container_tube_of_endpoints` at the two constants the repaired item (iv)
supplies: `ρt ≤ 1/4` is its truncation, and `‖x‖, ‖y‖ ≤ 1/4` is what the normalization's own
`Ψ(T_θ) ⊆ B(0,1/4)` gives for the core of `T̃ k` — once
`Kakeya.ml1Boot.exists_fineNormalization` is made to expose it.  The two together leave the
slack `1/4 + 1/4 ≤ 1`. -/
theorem exists_container_tube_of_quarter [ProperSpace E] {dt ρt : NNReal} (hdtρ : dt ≤ ρt)
    (hρ4 : (ρt : ℝ) ≤ 1 / 4) (T : _root_.Tube dt E)
    (hx : ‖T.x‖ ≤ 1 / 4) (hy : ‖T.y‖ ≤ 1 / 4) :
    ∃ Tρ : _root_.Tube ρt E, Tρ.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      T.toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧ Tρ.x = T.x ∧ Tρ.y = T.y :=
  exists_container_tube_of_endpoints hdtρ T hx hy (by linarith)

/-- The lower endpoint of the rescaled window is above the output scale itself:
`dt ≤ dt ^ (1 - 5 ε)` for `dt ≤ 1` and `0 ≤ ε`.  So the container radius `ρt` of item (iv) is
always at least `dt`, which is what `Kakeya.ml1Boot.exists_container_tube_of_endpoints` needs. -/
theorem le_window_lower {ε : ℝ} (hε : 0 ≤ ε) {dt : NNReal} (hdt0 : 0 < dt) (hdt1 : dt ≤ 1) :
    dt ≤ dt ^ (1 - 5 * ε) := by
  have h := NNReal.rpow_le_rpow_of_exponent_ge hdt0 hdt1 (by linarith : 1 - 5 * ε ≤ 1)
  simpa using h

end Geometry

section Window

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **Item (iv) of `Kakeya.ml1Boot.exists_fineNormalization_lower` is false above `1/2`.**

The clause is quoted verbatim; only its *first* conjunct `Tρ ⊆ B(0,1)` is used, so the
falsity is independent of the Frostman content and of the ambient family. -/
theorem item_iv_false_of_half_lt {δ dt : NNReal} {ε e n : ℝ}
    {ι : Type*} {u' un : Finset ι} {Ttil : ι → ShadedTube dt E} (hu' : u'.Nonempty)
    {ρt : NNReal} (hlo : dt ^ (1 - 5 * ε) ≤ ρt) (hhi : ρt ≤ dt ^ (5 * ε))
    (hhalf : 1 / 2 < (ρt : ℝ))
    (hiv : ∀ ρ : NNReal, dt ^ (1 - 5 * ε) ≤ ρ → ρ ≤ dt ^ (5 * ε) → ∀ k ∈ u',
      ∃ Tρ : _root_.Tube ρ E, Tρ.carrier ⊆ Metric.closedBall 0 1 ∧
        (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
        (fineFactor.C : ENNReal)⁻¹ * (δ : ENNReal) ^ e
            * ((ρ / dt : NNReal) : ENNReal) ^ n
          ≤ frostmanConstIn
              (familyIn un (fun k' => (Ttil k').toConvexSpaceBody) (Kakeya.Tube.dilate Tρ 2))
              (fun k' => (Ttil k').toConvexSpaceBody) (Kakeya.Tube.dilate Tρ 2)) :
    False := by
  obtain ⟨k, hk⟩ := hu'
  obtain ⟨Tρ, hball, -, -⟩ := hiv ρt hlo hhi k hk
  exact Tube.not_carrier_subset_closedBall_of_half_lt hhalf Tρ hball

/-- **The whole conclusion of `Kakeya.ml1Boot.exists_fineNormalization_lower` is
unsatisfiable once its window reaches above `1/2`.**

The conclusion is quoted verbatim from `Kakeya.ml1Boot.exists_fineNormalization_lower`;
`Kakeya.ml1Boot.item_iv_false_of_half_lt` is applied to its last clause at the output index
set, whose nonemptiness the conclusion itself asserts. -/
theorem conclusion_unsatisfiable_of_window_above_half {δ dt : NNReal} {ε e n : ℝ}
    {Λ Cunif : NNReal} {θ τ : NNReal} {ι : Type*} {u un : Finset ι}
    (Tθ : _root_.Tube θ E) (U : ι → ShadedTube τ E)
    {ρt : NNReal} (hlo : dt ^ (1 - 5 * ε) ≤ ρt) (hhi : ρt ≤ dt ^ (5 * ε))
    (hhalf : 1 / 2 < (ρt : ℝ)) :
    ¬ ∃ u' ⊆ u, u'.Nonempty ∧ ∃ Ttil : ι → ShadedTube dt E,
      (u' : Set ι).Pairwise
          (fun k k' => IsEssentiallyDistinct (Ttil k).carrier (Ttil k').carrier) ∧
        (∀ k ∈ u', (Ttil k).carrier ⊆ Metric.closedBall 0 1) ∧
        Nonempty (IsFlatPrismUniform u' Ttil
          (_root_.Tube.ssfGridLen dt) (normalizedUnif.C Cunif Λ)) ∧
        ShadedBody.multiplicity u (fun k => (U k).toShadedBody)
            ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * (Λ : ENNReal) ^ 2
              * ShadedBody.multiplicity u' (fun k => (Ttil k).toShadedBody) ∧
        ShadedBody.fullness u (fun k => (U k).toShadedBody)
            ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * (Λ : ENNReal) ^ 2
              * ShadedBody.fullness u' (fun k => (Ttil k).toShadedBody) ∧
        frostmanConstIn u' (fun k => (Ttil k).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * frostmanConstIn u (fun k => (U k).toConvexSpaceBody) Tθ.toConvexSpaceBody ∧
        ∀ ρ : NNReal, dt ^ (1 - 5 * ε) ≤ ρ → ρ ≤ dt ^ (5 * ε) → ∀ k ∈ u',
          ∃ Tρ : _root_.Tube ρ E, Tρ.carrier ⊆ Metric.closedBall 0 1 ∧
            (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
            (fineFactor.C : ENNReal)⁻¹ * (δ : ENNReal) ^ e
                * ((ρ / dt : NNReal) : ENNReal) ^ n
              ≤ frostmanConstIn
                  (familyIn un (fun k' => (Ttil k').toConvexSpaceBody)
                    (Kakeya.Tube.dilate Tρ 2))
                  (fun k' => (Ttil k').toConvexSpaceBody) (Kakeya.Tube.dilate Tρ 2) := by
  rintro ⟨u', -, hu'ne, Ttil, -, -, -, -, -, -, hiv⟩
  exact item_iv_false_of_half_lt (δ := δ) (e := e) (n := n) (un := un) hu'ne hlo hhi hhalf hiv

/-- **The hypotheses of `Kakeya.ml1Boot.exists_fineNormalization_lower` do reach a window
above `1/2`.**

Witness: `ε = 1/100`, `δ = (1/4) ^ 100`, `τ = 1/8`, `θ = 1/2`, so `δ ^ ε = 1/4`,
`fineScale τ θ = min (τ/θ) (1/4) = 1/4`, and the upper window endpoint
`(1/4) ^ (5 ε) = (1/4) ^ (1/20) = 2 ^ (-1/10)` exceeds `1/2` because
`(1/2) ^ 20 = 2 ^ (-20) < 2 ^ (-2) = 1/4`.  Every scale hypothesis of that lemma
(`hε0`, `hε1`, `hδ0`, `hδτ`, `hτθ`, `hθ1`, `hsep`, `hquarter`, `hdt`) is discharged here;
what this witness does not construct is the *family* data (`hunif`, `hED`, `hdens`, `hFb`),
which item (iv)'s falsity does not use. -/
theorem exists_scales_window_above_half :
    ∃ (ε : ℝ) (δ τ θ dt ρt : NNReal),
      0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ τ ∧ τ ≤ θ ∧ θ ≤ 1 ∧
      τ ≤ δ ^ ε * θ ∧ δ ^ ε ≤ 1 / 4 ∧ dt = fineScale τ θ ∧
      dt ^ (1 - 5 * ε) ≤ ρt ∧ ρt ≤ dt ^ (5 * ε) ∧ 1 / 2 < (ρt : ℝ) := by
  have hq1 : (1/4 : NNReal) ≤ 1 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hq0 : (0 : NNReal) < 1/4 := by rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have hδε : ((1/4 : NNReal) ^ (100:ℝ)) ^ ((1:ℝ)/100) = 1/4 := by
    rw [← NNReal.rpow_mul]; norm_num
  refine ⟨1/100, (1/4 : NNReal) ^ (100:ℝ), 1/8, 1/2, 1/4, (1/4 : NNReal) ^ ((1:ℝ)/20),
    by norm_num, by norm_num, NNReal.rpow_pos hq0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : ((1:NNReal)/4) ^ (100:ℝ) ≤ ((1:NNReal)/4) ^ (2:ℝ) :=
      NNReal.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
    refine h.trans ?_
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, NNReal.rpow_natCast]
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  · rw [← NNReal.coe_le_coe]; push_cast; norm_num
  · rw [← NNReal.coe_le_coe]; push_cast; norm_num
  · rw [hδε, ← NNReal.coe_le_coe]; push_cast; norm_num
  · rw [hδε]
  · rw [fineScale]; norm_num
  · rw [show (1:ℝ) - 5 * (1/100) = 19/20 by norm_num]
    exact NNReal.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
  · rw [show (5:ℝ) * (1/100) = 1/20 by norm_num]
  · have hc : (((1/4 : NNReal) ^ ((1:ℝ)/20) : NNReal) : ℝ) = (1/4 : ℝ) ^ ((1:ℝ)/20) := by
      push_cast [NNReal.coe_rpow]; norm_num
    rw [hc]
    have h1 : ((1/2:ℝ)) ^ (20:ℝ) < (1/4:ℝ) := by
      rw [show (20:ℝ) = ((20:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have h2 : (((1/2:ℝ)) ^ (20:ℝ)) ^ ((1:ℝ)/20) < (1/4:ℝ) ^ ((1:ℝ)/20) :=
      Real.rpow_lt_rpow (by positivity) h1 (by norm_num)
    have h3 : (((1/2:ℝ)) ^ (20:ℝ)) ^ ((1:ℝ)/20) = 1/2 := by
      rw [← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h3] at h2
    exact h2

/-- **The truncation is vacuous at small scales.**  If `δ̃ ≤ (1/4) ^ (1 / (5 ε))` then the
whole window `[δ̃ ^ (1 - 5 ε), δ̃ ^ (5 ε)]` lies below `1/4`, so a consumer of the truncated
item (iv) discharges `ρt ≤ 1/4` for free.  Every call site has `δ̃ ≤ δ ^ ε` with `δ`
quantified through `∀ᶠ δ in 𝓝[>] 0`, so the bound holds eventually. -/
theorem window_le_quarter_of_le_rpow {ε : ℝ} (hε : 0 < ε) {dt ρt : NNReal}
    (hdt : dt ≤ (1 / 4 : NNReal) ^ (1 / (5 * ε))) (hρ : ρt ≤ dt ^ (5 * ε)) :
    ρt ≤ 1 / 4 := by
  have h5 : 0 < 5 * ε := by linarith
  refine hρ.trans ?_
  calc dt ^ (5 * ε) ≤ ((1 / 4 : NNReal) ^ (1 / (5 * ε))) ^ (5 * ε) :=
        NNReal.rpow_le_rpow hdt (le_of_lt h5)
    _ = 1 / 4 := by
        rw [← NNReal.rpow_mul, one_div_mul_cancel (ne_of_gt h5), NNReal.rpow_one]

end Window

end ml1Boot

end Kakeya
