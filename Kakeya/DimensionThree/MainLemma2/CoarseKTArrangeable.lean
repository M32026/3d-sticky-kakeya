/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyUniform
public import Kakeya.DimensionThree.MainLemma2.KTWindowThresholds
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption

/-!
# What it costs to retire `coarseKatzTaoBound`: the three thresholds, priced

That replacement asks for
exactly three things the refuted statement did not, and this file prices each of them.

Write `ν` for the gain, which is `cfg.ϱ cfg.β τ / 8` on the thick branch and `τ' cfg.β / 2` on
the transverse branch.  The three are

1. `hηbudget : 3 η (1 - β) ≤ exscal · (ν / 180)` — an upper bound on `η`;
2. `hηKT     : 2 η ≤ exscal · coarseKTEta β ν`  — an upper bound on `η`;
3. `hρ₀      : ρ ≤ coarseKTRadius β ν`          — a smallness condition on the node radius,
   which reduces to one on `δ` through `ρ ≤ δ^{-η} r` once `r` is known small.

## The prices

* **(1) and (2) are free at a single `β`.**  `Kakeya.VeryNotSticky.exists_eta_coarseKT_caseParams`
  produces, from any `Kakeya.VeryNotSticky.CaseParams`, a smaller `η` satisfying the same
  `CaseParams` *and* all four instances of (1)–(2) — both gains at once.  Every field of
  `CaseParams` bounds `η` from above (`Kakeya.VNSUniform.CaseParams.mono_eta`), and `η` is
  chosen last, so a ninth upper bound costs nothing.  Crucially this needs **no** Katz–Tao
  hypothesis: `Kakeya.VeryNotSticky.coarseKTEta_pos'` is unconditional, so the bound can be
  imposed at `Kakeya.VeryNotSticky.exists_caseParams`, which takes only `0 < β`.
  *This is what dissolves the landmine recorded against putting these clauses on a
  configuration-indexed bundle*: there `η` is an outer binder of the producer and the clause is
  not arrangeable, whereas here `η` is the thing being chosen.
* **(3) is free.**  `Kakeya.VeryNotSticky.eventually_rpow_le_coarseKTRadius` says
  `δ^e ≤ coarseKTRadius β ν` holds for all small `δ` at every `e > 0`, so it is dischargeable
  inside the `∀ᶠ δ` that `Kakeya.VNSUniform.vnsBody_of_params` already carries — no field, and
  no strengthening of `Kakeya.VeryNotSticky.exists_setup_caseSideData`.
* **The one thing that is not free is `β`-uniformity.**  `Kakeya.ML2Assembly.Lemma91Uniform`
  needs *one* `η` for every `β` in a window, and (2) then asks for a positive lower bound on
  `coarseKTEta β (c β)` uniform over the window.  `coarseKTEta` is a `Classical.choose` value,
  so no such bound is derivable — exactly as for
  `Kakeya.VeryNotSticky.plankFrostmanExponent`, whose uniform floor is already isolated as
  `Kakeya.VNSUniform.UniformPlankExponent`.  `Kakeya.VNSUniform.UniformCoarseKTEta` below is the
  companion residual, and `Kakeya.VNSUniform.exists_uniform_bound_of_uniform_coarseKT` shows it
  is *exactly* the missing budget rather than an over-approximation of it, while
  `Kakeya.VNSUniform.uniformCoarseKTEta_of_not_windowFour` shows it is not a disguised `False`.

## VERDICT: the trade was priced here and **declined**

That the target of that lemma is load-bearing is not an assumption; it is measured.
`Kakeya.ML2Assembly.Lemma91Uniform` is no longer a *hypothesis* of the live two-obligation
assembly — `Kakeya.ML2Ptw.protected_statement_via_envelope` asks only for
`Kakeya.ML2Assembly.PointwiseCore` and `Kakeya.ML2Assembly.SmallCardHyp` — but it is the **only
proved supplier of `PointwiseCore`** that the Section-9 case split has
(`Kakeya.ML2Assembly.pointwiseCore_of_lemma91Uniform_of_geometricCore`).  Degrading its only
producer therefore degrades the only bridge.

**So `Kakeya.VNSUniform.UniformCoarseKTEta` below is the record of a REJECTED trade, not an
accepted obligation.**  Nothing in the tree depends on it, and nothing should be built on it
without re-opening the verdict.
-/

@[expose] public section

open Filter Topology Set

namespace Kakeya

universe u

namespace VeryNotSticky

/-- **Both coarse Katz–Tao `η`-thresholds are arrangeable by shrinking `η`, at both gains, with
no cost to `Kakeya.VeryNotSticky.CaseParams`.**

Given any admissible parameter package, a smaller `η` satisfies the same package and in
addition the budget clause and the fullness clause at the thick gain `ϱβτ/8` *and* at the
transverse gain `τ'β/2`.  This is the certificate that (1) and (2) of the module docstring are
free at the point where `η` is chosen, i.e. inside
`Kakeya.VeryNotSticky.exists_caseParams`.

The proof is a `min` of four explicit upper bounds, exactly as `exists_caseParams` already
takes a `min` of eight; `Kakeya.VNSUniform.CaseParams.mono_eta` carries the package down. -/
theorem exists_eta_coarseKT_caseParams {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ') :
    ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧ CaseParams β ζ exscal ϱ η' τ τ' ∧
      3 * η' * (1 - β) ≤ exscal * (ϱ * β * τ / 8 / 180) ∧
      2 * η' ≤ exscal * coarseKTEta.{u} β (ϱ * β * τ / 8) ∧
      3 * η' * (1 - β) ≤ exscal * (τ' * β / 2 / 180) ∧
      2 * η' ≤ exscal * coarseKTEta.{u} β (τ' * β / 2) := by
  have hτ : 0 < τ := params.hτ
  have hτ' : 0 < τ' := lt_trans params.hτ params.hτ'
  have hKT1 : 0 < coarseKTEta.{u} β (ϱ * β * τ / 8) := coarseKTEta_pos' _ _
  have hKT2 : 0 < coarseKTEta.{u} β (τ' * β / 2) := coarseKTEta_pos' _ _
  have h1mβ : 0 ≤ 1 - β := by linarith
  set b1 : ℝ := exscal * (ϱ * β * τ / 8 / 180) / 3 with hb1
  set b2 : ℝ := exscal * coarseKTEta.{u} β (ϱ * β * τ / 8) / 2 with hb2
  set b3 : ℝ := exscal * (τ' * β / 2 / 180) / 3 with hb3
  set b4 : ℝ := exscal * coarseKTEta.{u} β (τ' * β / 2) / 2 with hb4
  have hb1pos : 0 < b1 := by rw [hb1]; positivity
  have hb2pos : 0 < b2 := by rw [hb2]; positivity
  have hb3pos : 0 < b3 := by rw [hb3]; positivity
  have hb4pos : 0 < b4 := by rw [hb4]; positivity
  refine ⟨min η (min b1 (min b2 (min b3 b4))), ?_, min_le_left _ _, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min hη (lt_min hb1pos (lt_min hb2pos (lt_min hb3pos hb4pos)))
  · exact VNSUniform.CaseParams.mono_eta (min_le_left _ _) params
  · have hle : min η (min b1 (min b2 (min b3 b4))) ≤ b1 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hnn : 0 ≤ min η (min b1 (min b2 (min b3 b4))) :=
      le_of_lt (lt_min hη (lt_min hb1pos (lt_min hb2pos (lt_min hb3pos hb4pos))))
    nlinarith [hb1, hle, hnn, h1mβ]
  · have hle : min η (min b1 (min b2 (min b3 b4))) ≤ b2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [hb2] at hle
    linarith
  · have hle : min η (min b1 (min b2 (min b3 b4))) ≤ b3 :=
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hnn : 0 ≤ min η (min b1 (min b2 (min b3 b4))) :=
      le_of_lt (lt_min hη (lt_min hb1pos (lt_min hb2pos (lt_min hb3pos hb4pos))))
    nlinarith [hb3, hle, hnn, h1mβ]
  · have hle : min η (min b1 (min b2 (min b3 b4))) ≤ b4 :=
      le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    rw [hb4] at hle
    linarith

/-- **The budget clause is genuinely a new constraint: it does *not* follow from
`Kakeya.VeryNotSticky.CaseParams`.**

A compiled witness — an admissible parameter package at which
`3 η (1 - β) ≤ exscal · (ν / 180)` is **false** at the thick gain `ν = ϱβτ/8`.  So clause (1) of
the module docstring has to be *imposed*, not derived, and the only place it can be imposed for
free is where `η` is chosen.

The witness is `β = 10⁻²`, `ζ = 10¹³`, `exscal = 10⁻⁴`, `ϱ = 2⁻⁴⁰`, `η = 10⁻²⁵`, `τ = 10⁻⁴`,
`τ' = 1`.  Its shape is forced: every bound `CaseParams` puts on `η` is of the form
`η < ϱβτ / 2²⁰` or weaker, so `3η(1-β) < 3ϱβτ/2²⁰`, while the budget asks for
`exscal · ϱβτ / 1440`; the two compare as `exscal` against `3 · 1440 / 2²⁰ ≈ 4.1 · 10⁻³`, and
`Kakeya.VeryNotSticky.CaseParams.slab` forces `exscal < β/20`, which is smaller than that at
every `β < 0.083`.  Since `Kakeya.katzTaoEstimateDimensionThree` drives `β` towards `0`, the
failure is in the regime the development actually uses, not at an artificial corner. -/
theorem not_coarseKTBudget_of_caseParams :
    ∃ β ζ exscal ϱ η τ τ' : ℝ, 0 < β ∧ β ≤ 1 ∧ 0 < ζ ∧ 0 < exscal ∧ 0 < ϱ ∧ 0 < η ∧
      CaseParams β ζ exscal ϱ η τ τ' ∧
      ¬ (3 * η * (1 - β) ≤ exscal * (ϱ * β * τ / 8 / 180)) := by
  refine ⟨1 / 100, 10 ^ 13, 1 / 10 ^ 4, 1 / 2 ^ 40, 1 / 10 ^ 25, 1 / 10 ^ 4, 1,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  exact
    { hτ := by norm_num
      hτ' := by norm_num
      scale := by norm_num
      thinScale := by norm_num
      thinHalf := by norm_num
      densityBias := by simp only [parameterSeparationConstant]; norm_num
      slabDensity := by norm_num
      slabBias := by simp only [parameterSeparationConstant]; norm_num
      thick := by simp only [parameterSeparationConstant]; norm_num
      slab := by norm_num
      smallMultiplicity := by norm_num
      transverse := by norm_num
      tangential := by simp only [parameterSeparationConstant]; norm_num
      rhoLeTau := by norm_num }

/-- **The radius threshold is a plain smallness condition on `δ`.**

At every positive exponent `e`, `δ^e ≤ coarseKTRadius β ν` for all small `δ`.  So clause (3) of
the module docstring can be discharged inside the `∀ᶠ δ in 𝓝[>] 0` that
`Kakeya.VNSUniform.vnsBody_of_params` already conjoins facts into (it does exactly this for
positivity of `δ`), and needs neither a new field nor a strengthening of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`.

The consumer uses it at `e = cfg.exscal - cfg.η`, which is positive because
`Kakeya.VeryNotSticky.CaseParams.slabDensity` gives `3η < exscal`. -/
theorem eventually_rpow_le_coarseKTRadius (β ν : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, d ^ e ≤ coarseKTRadius.{u} β ν := by
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 (coarseKTRadius.{u} β ν)
    (coarseKTRadius_pos' β ν) he] with d hd
  simpa using hd

end VeryNotSticky

namespace VNSUniform

open VeryNotSticky

/-- **The second `β`-uniform residual**: the coarse Katz–Tao fullness exponent is bounded below
by a positive constant, uniformly over the window `[β₀, 1]`, along the ray of gains `ν = c·β` at
which the case split reads it.

This is the exact analogue of `Kakeya.VNSUniform.UniformPlankExponent`, and it arises for the
exact same reason: `Kakeya.VeryNotSticky.coarseKTEta` is produced by `Classical.choose`, the
only fact available about it is positivity at a *single* `(β, ν)`
(`Kakeya.VeryNotSticky.coarseKTEta_pos'`), and `Kakeya.ML2Assembly.Lemma91Uniform` needs one
`η` for a continuum of `β`.

The gain is `c·β` and not an arbitrary function of `β` because both branches read it there:
`c = ϱτ/8` on the thick branch and `c = τ'/2` on the transverse branch.

**This residual is NOT assumed anywhere, and must not be.**  See the verdict in the module
docstring: it is the price of deleting `Kakeya.VeryNotSticky.coarseKatzTaoBound`, that price was
judged too high, and the refuted statement was kept instead.  It is recorded so the price stays
on file. -/
def UniformCoarseKTEta (β₀ : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ p : ℝ, 0 < p ∧
    ∀ β ∈ Set.Icc β₀ 1, p ≤ coarseKTEta.{u} β (c * β)

/-- **The residual is exactly the missing budget, not an over-approximation of it.**

A `β`-uniform fullness clause and a `β`-uniform positive lower bound on
`Kakeya.VeryNotSticky.coarseKTEta` are interderivable, so nothing is lost by isolating the
latter.  Compare `Kakeya.VNSUniform.exists_uniform_bound_of_uniform_budget`, the same statement
for `Kakeya.VeryNotSticky.plankFrostmanExponent`. -/
theorem exists_uniform_bound_of_uniform_coarseKT {β₀ exscal c η : ℝ}
    (hexscal : 0 < exscal) (hη : 0 < η)
    (H : ∀ β ∈ Set.Icc β₀ 1, 2 * η ≤ exscal * coarseKTEta.{u} β (c * β)) :
    ∃ p : ℝ, 0 < p ∧ ∀ β ∈ Set.Icc β₀ 1, p ≤ coarseKTEta.{u} β (c * β) := by
  refine ⟨2 * η / exscal, by positivity, fun β hβ ↦ ?_⟩
  rw [div_le_iff₀ hexscal]
  calc 2 * η ≤ exscal * coarseKTEta.{u} β (c * β) := H β hβ
    _ = coarseKTEta.{u} β (c * β) * exscal := mul_comm _ _

/-- The converse direction: given the residual, the fullness clause can be arranged at every
`β` of the window by shrinking `η` once, at the threshold.  This is the step
`Kakeya.VNSUniform.exists_uniform_caseParams` would take for the new clause. -/
theorem exists_eta_uniform_coarseKT {β₀ exscal c p η : ℝ}
    (hexscal : 0 < exscal) (hp : 0 < p) (hη : 0 < η)
    (hfloor : ∀ β ∈ Set.Icc β₀ 1, p ≤ coarseKTEta.{u} β (c * β)) :
    ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧
      ∀ β ∈ Set.Icc β₀ 1, 2 * η' ≤ exscal * coarseKTEta.{u} β (c * β) := by
  refine ⟨min η (exscal * p / 2), lt_min hη (by positivity), min_le_left _ _, fun β hβ ↦ ?_⟩
  have h1 : 2 * min η (exscal * p / 2) ≤ exscal * p := by
    have := min_le_right η (exscal * p / 2)
    linarith
  exact le_trans h1 (mul_le_mul_of_nonneg_left (hfloor β hβ) hexscal.le)

/-- **The residual is consistent**: it holds outright in any world in which the windowed
Katz–Tao bound is unavailable on the window, since the canonical exponent is then the default
value `1`.  This rules out `Kakeya.VNSUniform.UniformCoarseKTEta` being a disguised `False`,
which is the failure mode a `Classical.choose` residual invites.  Compare
`Kakeya.VNSUniform.uniformPlankExponent_of_not_plankFrostmanVolume`. -/
theorem uniformCoarseKTEta_of_not_windowFour {β₀ : ℝ}
    (h : ∀ β ∈ Set.Icc β₀ 1, ∀ c : ℝ, 0 < c → ¬ ∃ q : ℝ × NNReal, 0 < q.1 ∧ 0 < q.2 ∧
      q.2 ≤ 1 / 2 ∧ WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) β (c * β / 180) q.1 q.2) :
    UniformCoarseKTEta.{u} β₀ := by
  refine fun c hc ↦ ⟨1, one_pos, fun β hβ ↦ ?_⟩
  have hval : coarseKTEta.{u} β (c * β)
      = (windowFourData.{u} (EuclideanSpace ℝ (Fin 3)) β (c * β / 180)).1 := rfl
  rw [hval, windowFourData, dif_neg (h β hβ c hc)]

end VNSUniform

end Kakeya
