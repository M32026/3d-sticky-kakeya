/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimatesWindowed

/-!
# Named thresholds for the windowed Katz–Tao multiplicity bound

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` produces its fullness exponent
`η_KT` and its radius threshold `ρ₀` *existentially*.  Every Section-9 consumer of it has to
compare those two quantities with data of a `Kakeya.VeryNotSticky` configuration — the exponent
with `2 * cfg.η`, the radius with the node scale `ρ` — and an existentially produced quantity
cannot be compared with anything by a statement that does not itself produce it.  That is what
made
`Kakeya.VeryNotSticky.coarseKatzTaoBound` false: the comparison was pushed under the
`∀ ν` binder of the consumer, where it reads `∀ ν > 0, 2 * cfg.η ≤ cfg.exscal * η_KT(ν)`, and
`η_KT(ν) → 0` as `ν → 0`.

This file removes the existential by Skolemizing it.  `Kakeya.windowFourData E β ε` is a
*named* pair `(η_KT, ρ₀)` depending on the ambient space, the Katz–Tao exponent `β` and the
loss exponent `ε` **and on nothing else** — in particular not on any configuration, and not on
`cfg.η` or `cfg.δ`.  `Kakeya.VeryNotSticky.coarseKTEta` and
`Kakeya.VeryNotSticky.coarseKTRadius` are its two components read at the loss exponent `ν/180`
attached to a gain `ν`.

With those names available, the two thresholds

* `2 * cfg.η ≤ cfg.exscal * coarseKTEta cfg.β ν`,
* `cfg.δ ^ (cfg.exscal / 2 - cfg.η) ≤ coarseKTRadius cfg.β ν`,

are ordinary comparisons of terms fixed *before* the corresponding field of the configuration:
the first bounds `2 * cfg.η` by a quantity depending only on `(β, ν)`, and `η` is chosen after
`β, ζ, exscal, ϱ, τ, τ'` and is bounded from above by every clause of
`Kakeya.VeryNotSticky.CaseParams`; the second is a smallness condition on `cfg.δ`, which is
chosen last of all.  The factor `2` on `cfg.η` is not slack: the fullness the coarse
Katz–Tao path has available is `δ^{2η}` (the field `Kakeya.VeryNotSticky.lam_ge`), so the
bridge to `cfg.a^{ηKT}` through `cfg.a ≤ cfg.δ^{exscal}` needs `2η ≤ exscal · ηKT`.  Both are
therefore of the shape `Kakeya.VeryNotSticky.CaseScale` already carries (compare its clause
`transverse_radius`), and neither is quantified over the gain.

## Main declarations

* `Kakeya.WindowFour` — the conclusion of the windowed bound at window radius `4`, with both
  thresholds named;
* `Kakeya.exists_windowFour` — that conclusion holds for *some* pair, from `KatzTaoEstimate`;
* `Kakeya.windowFourData` — the Skolem function, and `Kakeya.windowFourData_spec`;
* `Kakeya.VeryNotSticky.coarseKTEta`, `Kakeya.VeryNotSticky.coarseKTRadius`, and the three
  facts `coarseKTEta_pos`, `coarseKTRadius_pos`, `coarseKT_windowFour` that a Section-9
  consumer needs.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody Metric Set

namespace Kakeya

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The windowed Katz–Tao multiplicity bound at window radius `4`, with both thresholds
named.**

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` at `R = 4`, with the `∃ η > 0`
replaced by the parameter `ηKT` and the `∀ᶠ ρ in 𝓝[>] 0` replaced by the explicit threshold
`ρ ≤ ρ₀`.  Nothing is weakened: `Kakeya.exists_windowFour` below produces a pair for which this
holds, and `Kakeya.WindowFour.toEventually` recovers the `∀ᶠ` form. -/
def WindowFour (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (β ε ηKT : ℝ) (ρ₀ : NNReal) : Prop :=
  ∀ ρ : NNReal, 0 < ρ → ρ ≤ ρ₀ → ∀ τ : NNReal, 0 < τ → τ ≤ ρ →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube ρ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 (4 : ℝ)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ ηKT →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
          (s.card : ENNReal) ^ β

/-- **The windowed bound holds at some named pair of thresholds.**

This is the whole content of `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`,
repackaged: the produced `η` becomes the first component and a radius below which the
neighbourhood filter statement holds becomes the second. -/
theorem exists_windowFour [Nontrivial E] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧ WindowFour.{u} E β ε p.1 p.2 := by
  obtain ⟨ηKT, hηKT, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize_window (E := E) hβ0 hβ1 h
      (R := 4) (by norm_num) ε hε
  obtain ⟨v, hv0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨(ηKT, min v (1 / 2 : NNReal)), hηKT, lt_min hv0 (by norm_num),
    min_le_right _ _, ?_⟩
  intro ρ hρ0 hρv τ hτ0 hτρ ι s T hball hfull
  refine (hsub ⟨hρ0, le_trans hρv (min_le_left _ _)⟩) τ hτ0 hτρ s T ?_ hfull
  intro i
  have h4 : (((4 : NNReal)) : ℝ) = (4 : ℝ) := by norm_num
  rw [h4]
  exact hball i

open Classical in
/-- **The Skolemized thresholds of the windowed Katz–Tao bound at window radius `4`.**

A *named* pair `(η_KT, ρ₀)`, a function of the ambient space, the Katz–Tao exponent `β` and the
loss exponent `ε` alone.  The default value `(1, 1)` in the degenerate branch is never read: the
only consumer supplies `Kakeya.KatzTaoEstimate`, which by `Kakeya.exists_windowFour` makes the
branch condition true. -/
noncomputable def windowFourData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (β ε : ℝ) : ℝ × NNReal :=
  if h : ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧ WindowFour.{u} E β ε p.1 p.2
  then h.choose else (1, 1 / 2)

/-- The radius threshold never exceeds `1/2`, in both branches of the definition.  This is not
decoration: the Section-9 consumer builds an auxiliary `ρ`-tube inside the unit ball for the
indices outside its family, and `Kakeya.VeryNotSticky.exists_tube_subset_closedBall` needs
`ρ ≤ 1/2` for that.  Carrying it here rather than as one more clause on the configuration keeps
the consumer's hypotheses to the three that are genuinely about the configuration. -/
theorem windowFourData_snd_le_half (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (β ε : ℝ) :
    (windowFourData.{u} E β ε).2 ≤ 1 / 2 := by
  classical
  rw [windowFourData]
  split
  · rename_i h
    exact h.choose_spec.2.2.1
  · norm_num

/-- **The fullness exponent is positive in *both* branches of the definition**, hence
unconditionally — no `Kakeya.KatzTaoEstimate` needed.  This is not a convenience: the
Section-9 parameter package chooses `η` at a point where the Katz–Tao hypothesis of the
induction is not yet in scope (`Kakeya.VeryNotSticky.exists_caseParams` takes only `0 < β`),
so an upper bound on `η` of the form `2η ≤ exscal · ηKT` is arrangeable there only if `ηKT` is
known positive *without* that hypothesis.  It is: the `else` branch is the explicit pair
`(1, 1/2)` and the `then` branch carries `0 < p.1` by construction. -/
theorem windowFourData_fst_pos (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (β ε : ℝ) :
    0 < (windowFourData.{u} E β ε).1 := by
  classical
  rw [windowFourData]
  split
  · rename_i h
    exact h.choose_spec.1
  · norm_num

/-- The radius threshold is positive in both branches, hence unconditionally.  Companion of
`Kakeya.windowFourData_fst_pos`; see that docstring for why the unconditional form is the one
the parameter package needs. -/
theorem windowFourData_snd_pos (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (β ε : ℝ) :
    0 < (windowFourData.{u} E β ε).2 := by
  classical
  rw [windowFourData]
  split
  · rename_i h
    exact h.choose_spec.2.1
  · norm_num

/-- The defining property of `Kakeya.windowFourData`. -/
theorem windowFourData_spec [Nontrivial E] {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    0 < (windowFourData.{u} E β ε).1 ∧ 0 < (windowFourData.{u} E β ε).2 ∧
      WindowFour.{u} E β ε (windowFourData.{u} E β ε).1 (windowFourData.{u} E β ε).2 := by
  classical
  have hex : ∃ p : ℝ × NNReal, 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 / 2 ∧
      WindowFour.{u} E β ε p.1 p.2 := exists_windowFour hβ0 hβ1 h hε
  have hval : windowFourData.{u} E β ε = hex.choose := by
    rw [windowFourData, dif_pos hex]
  rw [hval]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2.1, hex.choose_spec.2.2.2⟩

namespace VeryNotSticky

/-- **The fullness exponent of the coarse Katz–Tao input at gain `ν`.**

`Kakeya.windowFourData` read at the loss exponent `ε₀ = ν/180`, which is the exponent at which
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` invokes the windowed bound.  It is a
function of `(β, ν)` alone; in particular it does not move with `cfg.η`, which is what lets the
threshold `2 * cfg.η ≤ cfg.exscal * coarseKTEta cfg.β ν` be a genuine upper bound on `cfg.η`
rather than a circularity. -/
noncomputable def coarseKTEta (β ν : ℝ) : ℝ :=
  (windowFourData.{u} (EuclideanSpace ℝ (Fin 3)) β (ν / 180)).1

/-- **The radius threshold of the coarse Katz–Tao input at gain `ν`.**

The companion of `Kakeya.VeryNotSticky.coarseKTEta`: the windowed bound is available for
families of `ρ`-tubes with `ρ ≤ coarseKTRadius β ν`.  It is a function of `(β, ν)` alone, so
`cfg.δ ^ (cfg.exscal / 2 - cfg.η) ≤ coarseKTRadius cfg.β ν` is a smallness condition on
`cfg.δ`. -/
noncomputable def coarseKTRadius (β ν : ℝ) : NNReal :=
  (windowFourData.{u} (EuclideanSpace ℝ (Fin 3)) β (ν / 180)).2

theorem coarseKTEta_pos {β ν : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) (hν : 0 < ν) :
    0 < coarseKTEta.{u} β ν :=
  (windowFourData_spec hβ0 hβ1 h (by linarith : (0 : ℝ) < ν / 180)).1

theorem coarseKTRadius_pos {β ν : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) (hν : 0 < ν) :
    0 < coarseKTRadius.{u} β ν :=
  (windowFourData_spec hβ0 hβ1 h (by linarith : (0 : ℝ) < ν / 180)).2.1

/-- The radius threshold is at most `1/2`, unconditionally. -/
theorem coarseKTRadius_le_half (β ν : ℝ) : coarseKTRadius.{u} β ν ≤ 1 / 2 :=
  windowFourData_snd_le_half (EuclideanSpace ℝ (Fin 3)) β (ν / 180)

/-- **`coarseKTEta` is positive unconditionally.**  `Kakeya.VeryNotSticky.coarseKTEta_pos` above
is the same fact under the Katz–Tao hypothesis; this form is what
`Kakeya.VeryNotSticky.exists_caseParams` can use, since it chooses `η` before that hypothesis
is available.  See `Kakeya.windowFourData_fst_pos`. -/
theorem coarseKTEta_pos' (β ν : ℝ) : 0 < coarseKTEta.{u} β ν :=
  windowFourData_fst_pos (EuclideanSpace ℝ (Fin 3)) β (ν / 180)

/-- **`coarseKTRadius` is positive unconditionally.**  Companion of
`Kakeya.VeryNotSticky.coarseKTEta_pos'`; it is what makes the radius threshold
`cfg.δ ^ e ≤ coarseKTRadius cfg.β ν` a plain smallness condition on `δ`, arrangeable inside the
`∀ᶠ δ` the case split already carries. -/
theorem coarseKTRadius_pos' (β ν : ℝ) : 0 < coarseKTRadius.{u} β ν :=
  windowFourData_snd_pos (EuclideanSpace ℝ (Fin 3)) β (ν / 180)

theorem coarseKT_windowFour {β ν : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (h : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) (hν : 0 < ν) :
    WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) β (ν / 180)
      (coarseKTEta.{u} β ν) (coarseKTRadius.{u} β ν) :=
  (windowFourData_spec hβ0 hβ1 h (by linarith : (0 : ℝ) < ν / 180)).2.2

end VeryNotSticky

end Kakeya
