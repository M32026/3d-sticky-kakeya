/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupSideData
public import Kakeya.DimensionThree.MainLemma2.SetupThresholdsGeneral
public import Kakeya.DimensionThree.MainLemma2.BallDataGeneral
public import Kakeya.DimensionThree.MainLemma2.SlabMultKTGeneral
public import Kakeya.DimensionThree.MainLemma2.TangentialSlabDegenerate
public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCountDischargeGeneral
public import Kakeya.DimensionThree.MainLemma2.BallDataGeneralProducer
public import Kakeya.DimensionThree.MainLemma2.ThickBundleGeneral
public import Kakeya.DimensionThree.MainLemma2.ThickDensityRecut
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.DimensionThree.MainLemma2.TangentialSlabBridge
public import Kakeya.DimensionThree.MainLemma2.CanonicalCapsulesProducer

/-!
# G12 — the boundary theorem of `MainLemma2/SetupSideData.lean`, re-cut at general `(a, b)`

`Kakeya.VeryNotSticky.sideDataResidue_of_obligations_general` is the general-`(a, b)` twin of the
existing `Kakeya.VeryNotSticky.sideDataResidue_of_sideDataObligations`
(`MainLemma2/SetupSideData.lean`): the same conclusion
`Kakeya.VeryNotSticky.SideDataResidue β ζ exscal ϱ η τ τ'`, the same steps 1–4, but from step 5 on
the construction runs over `cfg'' := cfg'.withDims a b h` for the dimensions `(a, b)` that the
general producer of GWZ §9.3 steps 5–7 chooses (`gwz.txt` l.2036–2041: "by pigeonholing, we can
suppose that for each `B`, the convex sets `W ∈ 𝕎_B` have dimensions `a × b × r₁`"), instead of
over `cfg'` at the degenerate `a = b = δ`. **Nothing in `MainLemma2/SetupSideData.lean` is
touched**: the existing degenerate boundary theorem stays exactly as it is, and this is a new leaf.

steps G12 /§4.1.

## What is threaded through `withDims`, and what it costs

Steps 1–4 (the slack family, the island cut, `Kakeya.VeryNotSticky.exists_config_of_slackCut_at`,
the cover transported along `e'`) are byte-for-byte the existing proof's, because none of them reads
`cfg.a` or `cfg.b`. Step 5 then applies conjunct 1's general contract
`Kakeya.VeryNotSticky.BallDataGeneralTarget` and obtains `(a, b, h)` together with a
`Kakeya.VeryNotSticky.BallData (cfg'.withDims a b h)`.

Re-deriving the residue's four bookkeeping facts across `withDims` is **free**: `withDims` replaces
`a`, `b`, `hdims` and copies every other field, so `cfg''.δ`, `cfg''.β`, `cfg''.ζ`, `cfg''.η`,
`cfg''.exscal`, `cfg''.ϱ`, `cfg''.r₁`, `cfg''.ι`, `cfg''.s` and `cfg''.T` are *definitionally* those
of `cfg'` (row G1's `rfl` lemmas in `MainLemma2/SetupWithDims.lean`). Consequently `hparams'`,
`href'`, `hc'` and `hse'` are re-used at `cfg''` with no transport at all — they typecheck by
`Eq.refl`-level defeq, which is what tripwire 3 below records in its sharpest form
(`cfg.withDims cfg.a cfg.b cfg.hdims = cfg` by `rfl`, and a `BallData cfg` *is* a
`BallData (cfg.withDims cfg.a cfg.b cfg.hdims)`).

## The conjunct wiring: three discharged, four carried

`Kakeya.VeryNotSticky.nonempty_caseSideData` guards its `tangential` field by
`cfg.a ≤ cfg.δ^{1-τ} → cfg.b ≤ cfg.δ^{2 exscal} →`, so conjuncts 3–6 are needed **only** under
those two guards, and the general twins of conjuncts 4 and 5 want exactly the second of them.

* **conjunct 1** (T4, tier `BallData` + the (A1') margin) — **DISCHARGED**, by row G5's existing
  `Kakeya.VeryNotSticky.ballDataGeneralTarget`, which has no hypothesis binders at all. The
  binder `hballData` is gone. * **conjunct 2** (thresholds: `ThinConfig`, `SlabScale`, `CaseScale`, the tangential density
  threshold) — **discharged** by `Kakeya.VeryNotSticky.eventually_thresholds_general_of_O5` below,
  which is `Kakeya.VeryNotSticky.eventually_thresholds_general`
  (`MainLemma2/SetupThresholdsGeneral.lean`, rows G6/G7/G7b) with the thin guard replaced by O5 as
  an input — see the next section. * **conjunct 3** (`TangentialInputs.slab`, the slab package) — **carried**, as `hslabPackage`, in
  the shape  row G9 states: the existing conjunct 3 with the pins
  `cfg.a = cfg.δ → cfg.b = cfg.δ` replaced by G5's margin guard `cfg.a ≤ cfg.δ^{1-τ}` and the
  non-slab guard `cfg.b ≤ cfg.δ^{2 exscal}`. Owner: row **G9**
  (`TangentialSlabFamily.lean`, `exists_slabPackage_general`). * **conjunct 4** (`SlabMultKT.estimate` at `η₁ = 9η`) — **discharged** by the existing
  `Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab`
  (`MainLemma2/SlabMultKTGeneral.lean`, row G8) at the guard `cfg.b ≤ cfg.δ^{2 exscal}`. * **conjunct 5** (R17, `SplitInputs.fibreScaleCount`) — **discharged** by the existing
  `Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_nonslab`
  (`MainLemma2/SplitInputsGeneral.lean`, row G8b) at the same guard; the splitting level itself
  comes from `Kakeya.VeryNotSticky.eventually_exists_splitInputs_nonslab`. * **conjunct 6** (R18, the angular clause `SplitInputs.angularFibre_le_fibreMult`) — **carried**,
  as `hAngular`, the existing conjunct 6 with `cfg.b = cfg.δ` replaced by
  `cfg.b ≤ cfg.δ^{2 exscal}`. * **conjunct 7** (`ThickDensityThresholds`, which the degenerate route got vacuously from
  `Kakeya.VeryNotSticky.eventually_exists_thickDensityThresholds_degenerate_of_budget` at
  `cfg.a = cfg.δ`) — **DISCHARGED** by
  `Kakeya.VeryNotSticky.eventually_exists_thickDensityThresholds_of_ED` below, **modulo the degree bound**: the binder
  `hThickBundle` is replaced by the strictly smaller non-ED **degree bound** on the ball-core segments. Owner of what is left: the canonical-capsule core, C7-b.

## The one obligation the general branch adds: O5 off the thin branch (row **G6b**)

`Kakeya.VeryNotSticky.CaseSideData.caseScale` is **not** guarded, so a `CaseScale` is needed at
every `(a, b)` the producer may pick; and the O5 field
`Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness` has, at this tip, exactly two producers:
it is vacuous at `a = b` (`Kakeya.VeryNotSticky.not_transverseGuard_of_a_eq_b`, the degenerate
route), and `Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` (row G6) proves it under the
**thin guard** `cfg.a ≤ cfg.δ^{1-τ}`. Since `Kakeya.VeryNotSticky.BallDataGeneralTarget` promises
only `cfg.δ ≤ a ≤ b ≤ cfg.δ^{exscal}`, and `CaseParams.thinHalf` gives `exscal < 1 - τ`, the thick
branch `cfg.δ^{1-τ} ≤ cfg.a` — non-empty together with the transverse guard, since
`δ^{1-τ} ≤ a ≤ δ^{τ'}b ≤ δ^{τ'+exscal}` only asks `τ' + exscal ≤ 1 - τ` and `thinHalf` gives
`1 - τ - exscal ≥ 1/2` — has no O5 producer.

The theorem is **total in `(a, b)`, and since E-L1 existing it is so with no binder at all.**
It used to take `hO5thick`, the mirror image of `eventually_caseScale_O5_of_C_le` with
`cfg.a ≤ cfg.δ^{1-τ}` replaced by `cfg.δ^{1-τ} ≤ cfg.a`, and to split on the guard with one
`rcases le_or_gt`. The thin guard is an antecedent of the named proposition `Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`
(`MainLemma2/CaseScaleNonslabRefute.lean`), so row **G6**'s
`Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` now supplies that `Prop` for **every**
`(a, b)`: the binder is **deleted, not discharged**, and the dichotomy is gone.

**Two compiled facts price that binder** (section G6b below):

* `Kakeya.VeryNotSticky.o5_transverse_budget_forces_large_zeta` — re-running G6's chain at the
  transverse guard instead of the thin guard needs `6η ≤ 16η τ'`, and `CaseParams` buys that only
  at `ζ > 18·2²⁰`. So there is no constant at which row G6's route closes on the thick branch.
* `Kakeya.VeryNotSticky.o5_dims_meet_thickPlank_dims_only_selfdual` — and it is **not** a
  `Kakeya.VeryNotSticky.ThickPlankPresentation` output either: §9.4's thick planks are pinned to
  the *dual* dimensions `(δ/b, δ/a)` (`short_upper`, `long_upper`) while O5 pins `a'` to `a/r₁`,
  and an `a'` meeting both forces the self-dual locus `a·b ≤ C₀·CP·δ·r₁`. In particular
  `ThickPlankPresentation.fullness_ge` is a statement about a different plank family.

The guard corresponds to GWZ §9.5's own
sentence — "**9.5. The thin case.** Now we consider the thin case when `a ∈ [δ, δ^{1-τ}]`"
(`gwz.txt` l.2176) — and **licenses E-L1**: prepend `cfg.a ≤ cfg.δ ^ (1 - τ) →` to the field
`transverseFill_fullness`, in the byte-exact shape the neighbouring field
`Kakeya.VeryNotSticky.CaseScale.plank_small` already uses, with
`statement_of_universal_caseScale_O5` updated in lockstep (condition E-C1) and the two producers
absorbing the binder (E-C2). O5 is a thin-case object by the source's own definition of the case.
E-L1 has existing (pack **F26**): `eventually_caseScale_of_C_le_O5`'s O5 input **is** the guarded
clause, which row G6 supplies for every `(a, b)`, so `hO5thick` is gone from the binder list.

## Why the existing degenerate boundary theorem is *not* an instance of this one

`sideDataResidue_of_sideDataObligations`'s type is
`… → Kakeya.VeryNotSticky.SideDataObligations … → SideDataResidue …`, so recovering it would need
`SideDataObligations` to imply the five binders above. It does not, and the obstruction is
conjunct 1: `BallDataGeneralTarget` asserts its `∃ (a, b, h, bd)` for **every** configuration at
the pins, whereas `SideDataObligations`'s conjunct 1 asserts a `BallData cfg` only for
configurations with `cfg.a = cfg.b = cfg.δ` — it says nothing at any other `cfg`, so it cannot
produce the general contract. (The converse direction is fine and is not the tripwire that was
asked for: `BallDataGeneralTarget` plus a `δ`-free `Cg` bound *does* give the existing conjunct 1's
`cfg.a = cfg.b = cfg.δ` instance, by tripwire 3's eta.) The two theorems therefore stand side by
side, with the same conclusion, and tripwire 1 records that this one reaches the frozen target
`Kakeya.VeryNotSticky.exists_setup_caseSideData` through the frozen consumer exactly as the existing
one does. Tripwire 2 records the piece of the degenerate recovery that *is* available: the
general conjunct-3 binder implies the existing degenerate conjunct 3 verbatim.

Nothing here changes an existing statement; every declaration is new.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal
open Produce

universe u

/-! ### G6b — why the thick branch has no O5 producer, compiled

`hO5thick` was the only one of the five binders with no owning row, and it is not a hypothesis of the guarded construction. These two theorems are kept as the price record of the
route E-L1 replaced: they say exactly what a thick-branch O5 producer would have cost. -/

/-- **Running G6's budget at the transverse guard instead of the thin guard forces
`ζ > 18 · 2²⁰`.**

`Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` closes O5 because the thin guard gives
`a' ≤ C₀ δ^{1-τ-exscal}` and `Kakeya.VeryNotSticky.o5_budget_of_thinHalf` turns
`CaseParams.thinHalf` into `6η + ε < 16η(1-τ-exscal)`. Off the thin branch the only upper bound
left on `a'` is the transverse guard's `a/r₁ ≤ a/b ≤ δ^{τ'}`, so the same chain needs
`6η ≤ 16η τ'`, i.e. `τ' ≥ 3/8`. This theorem shows that `Kakeya.VeryNotSticky.CaseParams` buys
that only at `ζ > 18 · 2²⁰ = 18874368`: `CaseParams.tangential` reads
`2²⁰(ϱ + τ') < exscal·β·ζ/2` and `CaseParams.slab` forces `exscal < β/24`, so
`2²⁰ · 3/8 < β²ζ/48 ≤ ζ/48`.

`ζ` is GWZ's ρ-count exponent in `ρ^{-2-ζ} ≤ #tρ` (Lemma 9.1's hypothesis), where a *larger* `ζ`
is a *stronger* demand on the input family; `ζ > 1.8·10⁷` is not a regime the source or the tree
intends. So the thick branch's O5 is not reachable by G6's route, at any constant.

The firing control is in `S9G12_priv/probe/`: the same statement at `18874369` fails, so the
numeral is what the chain yields and not slack. -/
theorem o5_transverse_budget_forces_large_zeta {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') (hβ1 : β ≤ 1) (hη : 0 < η)
    (hbud : 6 * η ≤ 16 * η * τ') : (18874368 : ℝ) < ζ := by
  have hP : parameterSeparationConstant = 2 ^ 20 := rfl
  have hτ : 0 < τ := params.hτ
  have hτ'0 : 0 < τ' := lt_trans hτ params.hτ'
  have hϱ : 0 < ϱ := by
    have h := params.densityBias
    rw [hP] at h
    nlinarith [h, hη]
  have hβ0 : 0 < β := by
    by_contra hc
    push Not at hc
    nlinarith [params.transverse, hτ, hη, hτ'0, hc]
  have hτ'38 : (3 : ℝ) / 8 ≤ τ' := by nlinarith [hbud, hη]
  have hex0 : 0 < exscal := by nlinarith [params.slabDensity, hη]
  have hex : exscal < β / 24 := by nlinarith [params.slab, hτ, hη]
  have htang := params.tangential
  rw [hP] at htang
  have hpos : 0 < exscal * β := mul_pos hex0 hβ0
  have hζ0 : 0 < ζ := by
    by_contra hc
    push Not at hc
    nlinarith [htang, hϱ, hτ'0, mul_nonneg hpos.le (neg_nonneg.mpr hc)]
  have h1 : (393216 : ℝ) ≤ 2 ^ 20 * (ϱ + τ') := by nlinarith [hτ'38, hϱ]
  have h2 : exscal * β * ζ / 2 < β / 24 * β * ζ / 2 := by
    nlinarith [hex, hβ0, hζ0]
  have hb2 : β * β ≤ 1 := by nlinarith [hβ1, hβ0]
  have h3 : β / 24 * β * ζ / 2 ≤ ζ / 48 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb2) hζ0.le]
  linarith [htang, h1, h2, h3]

/-- **O5's plank dimensions and the thick case's plank dimensions are dual, and agree only on the
self-dual locus.**

The answer to "is the thick branch's O5 a `ThickPlankPresentation` output?" is **no**, and this is
the arithmetic reason. O5 pins its short plank dimension to the *ball-rescaled* body dimension,
`C₀⁻¹(a/r₁) ≤ a' ≤ C₀(a/r₁)` (`Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`), while
`Kakeya.VeryNotSticky.ThickPlankPresentation.short_upper` / `.long_upper` pin it to the *dual*
dimension, `a' ≤ CP·(δ/b)`, `b' ≤ CP·(δ/a)` — GWZ §9.4's thick planks are the polar bodies of
§9.5's rescaled slabs, not the same family. An `a'` satisfying both therefore forces
`a·b ≤ C₀·CP·δ·r₁`, the self-dual locus; in particular
`Kakeya.VeryNotSticky.ThickPlankPresentation.fullness_ge` is a statement about a different plank
family and cannot discharge O5. Stated over `ℝ` at abstract positive scales, since that is all the
argument uses. -/
theorem o5_dims_meet_thickPlank_dims_only_selfdual {a b r₁ d a' C₀ CP : ℝ}
    (hr₁ : 0 < r₁) (hC₀ : 0 < C₀)
    (hlow : C₀⁻¹ * (a / r₁) ≤ a') (hup : a' ≤ CP * (d / b)) (hb : 0 < b) :
    a * b ≤ C₀ * CP * (d * r₁) := by
  have h : C₀⁻¹ * (a / r₁) ≤ CP * (d / b) := le_trans hlow hup
  have h2 : a / r₁ ≤ C₀ * (CP * (d / b)) := by
    rw [inv_mul_le_iff₀ hC₀] at h
    linarith
  have h3 : a ≤ C₀ * (CP * (d / b)) * r₁ := by
    rw [div_le_iff₀ hr₁] at h2
    linarith
  have h4 : a * b ≤ C₀ * (CP * (d / b)) * r₁ * b := by nlinarith [h3, hb]
  have h5 : C₀ * (CP * (d / b)) * r₁ * b = C₀ * CP * (d * r₁) := by
    field_simp
  linarith [h4, h5.le, h5.ge]


/-! ### `CaseScale` at general `(a, b)` with O5 as an explicit input -/

/-- **`Kakeya.VeryNotSticky.CaseScale` at general `(a, b)`, with O5 supplied from outside.**

Byte-for-byte `Kakeya.VeryNotSticky.eventually_caseScale_of_C_le_general`
(`MainLemma2/SetupThresholdsGeneral.lean`, row G7) except that the thin guard
`cfg.a ≤ cfg.δ^{1-τ}` — which that theorem spends *only* on
`Kakeya.VeryNotSticky.eventually_caseScale_O5_of_C_le` — is replaced by the O5 clause itself, at
the pinned named `Prop` `Kakeya.VeryNotSticky.statement_of_universal_caseScale_O5`. The fourteen
non-O5 clauses are unchanged and are still `Kakeya.VeryNotSticky.eventually_caseScale_clauses`'s.

This is what makes the general boundary theorem below total in `(a, b)`: on the thin branch O5 is
row G6's theorem, on the thick branch it is an explicit binder. The `example` after it re-derives
the existing general theorem verbatim, so this is a generalisation and not a divergence. -/
theorem eventually_caseScale_of_C_le_O5 (C₀ Cbias : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' ν ε : ℝ} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthinScale : τ + exscal < 1) (hε : 5 * ε < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (thr : ScaleThresholds) (C : NNReal),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias →
        statement_of_universal_caseScale_O5.{u} cfg bd τ τ' C →
        1 ≤ C → C ≤ d ^ (-ε) →
        cfg.δ ≤ thr.aScale ν → cfg.δ ≤ thr.typical →
        CaseScale cfg bd τ τ' ν C thr := by
  filter_upwards [eventually_caseScale_clauses C₀ Cbias 1 hC₀ hexscal hexscal1 hη hϱ hτ' hthinScale,
    eventually_transverseFill_threshold (exscal := exscal) (ϱ := ϱ) hη hexscal1,
    eventually_multiplicity_large (η := 16 * η) (exscal := exscal)
      (by linarith : (0:ℝ) < 16 * η) hexscal1,
    eventually_typicalAngle_const.{u} (exscal := exscal) hη hϱ hexscal1,
    eventually_nnreal_mul_pow_le_rpow_neg (1000 * (8 * netPolyConstant C₀)) 5 (ε := ε)
      (ν := η) (by push_cast; linarith),
    self_mem_nhdsWithin] with d hcl hfill hmult htyp hball hd0
  intro cfg bd thr C hδ hex hη' hϱ' hC hCb hO5 h1C hCle hthrA hthrT
  obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9⟩ := hcl cfg bd hδ hex hη' hϱ' hC hCb
  exact
    { rho2Star_le_one := c1
      body_fits_ball := c2
      plank_small := c3
      multiplicity_large := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη']
        exact hmult
      transverse_radius := c4
      transverse_fill := c5
      transverse_ballFill := by
        rw [hC, hδ, hη']
        calc 1000 * ThinCase.transferConstant C C₀
            ≤ 1000 * (8 * netPolyConstant C₀ * C ^ 5) := by
              gcongr
              exact transferConstant_le_mul_pow h1C
          _ = 1000 * (8 * netPolyConstant C₀) * C ^ 5 := by ring
          _ ≤ d ^ (-η) := hball C hCle
      aScaleData_threshold := hthrA
      typicalAngle_threshold := hthrT
      typicalAngle_const := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη', hϱ', hδ]
        refine htyp (plankEnclosureConstant bd.C₀ * bd.Cbias) ?_
        rw [← hδ, ← hϱ']
        exact c7
      plankCard_bias := c7
      transverseFill_threshold := hfill cfg bd hδ hex hη' hϱ'
      transverseFill_fullness := hO5
      typicalAngle_selection := c8
      typicalAngle_cap := c9 }

/-- Control: the existing `eventually_caseScale_of_C_le_general` is the thin-guard instance. -/
example (C₀ Cbias : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' ν ε : ℝ} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthinScale : τ + exscal < 1) (hε : 5 * ε < η)
    (hbud : 6 * η + ε < 16 * η * (1 - τ - exscal)) :
    type_of% (eventually_caseScale_of_C_le_general.{u} C₀ Cbias hC₀ hexscal hexscal1 hη hϱ hτ'
      hthinScale hε (ν := ν) hbud) := by
  filter_upwards [eventually_caseScale_of_C_le_O5.{u} C₀ Cbias hC₀ hexscal hexscal1 hη hϱ hτ'
      hthinScale hε (ν := ν),
    eventually_caseScale_O5_of_C_le.{u} C₀ hC₀ (exscal := exscal) (η := η) (τ := τ) (τ' := τ')
      (ε := ε) hη hbud] with d hgen hO5
  intro cfg bd thr C hδ hex hη' hϱ' hC hCb _hthin h1C hCle hthrA hthrT
  exact hgen cfg bd thr C hδ hex hη' hϱ' hC hCb
    (hO5 cfg bd C hδ hex hη' hC h1C (by rw [hδ]; exact hCle)) h1C hCle hthrA hthrT

/-! ### Conjunct 2's thresholds at general `(a, b)`, with O5 as an explicit input -/

/-- **Conjunct 2's three thresholds at general `(a, b)`, with O5 supplied from outside.**

`Kakeya.VeryNotSticky.eventually_thresholds_general` (row G7 + G7b) with the same single change:
its thin guard becomes the hypothesis
`∀ C, 1 ≤ C → C ≤ δ^{-ε} → statement_of_universal_caseScale_O5 cfg bd τ' C`
at `ε = Kakeya.VeryNotSticky.thresholdExponent β exscal η τ`, the exponent at which the
thin constant is produced. Everything else — the thin configuration from
`Kakeya.VeryNotSticky.eventually_exists_thinConfig_le_general`,
`Kakeya.VeryNotSticky.eventually_slabScale_of_C_le` for `SlabScale`,
`Kakeya.VeryNotSticky.eventually_densityConstant_of_C_le` for the tangential density threshold —
is untouched and was already general in `(a, b)`. -/
theorem eventually_thresholds_general_of_O5 {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    {εg : ℝ} (hεg : εg < thresholdExponent β exscal η τ) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
    cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
    (∀ C : NNReal, 1 ≤ C → C ≤ cfg.δ ^ (-thresholdExponent β exscal η τ) →
      statement_of_universal_caseScale_O5.{u} cfg bd τ τ' C) →
    bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil ≤ Cdil → bd.c₁ = c₁ → bd.D = D →
    bd.Cg ≤ cfg.δ ^ (-εg) → bd.Cm = 1 →
    (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
      (fibreMassConstant : ENNReal) * (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) →
    cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
    ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
      SlabScale cfg bd tc τ ∧
      CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  set ε := thresholdExponent β exscal η τ with hεdef
  have hε := thresholdExponent_pos hη params
  have hεd := thresholdExponent_le_density β exscal η τ
  have hεf := thresholdExponent_le_final β exscal η τ
  have hεη := thresholdExponent_le_eta β exscal η τ
  rw [← hεdef] at hε hεd hεf hεη
  have hslabDensity := params.slabDensity
  have hslab := params.slab
  have hscale := params.scale
  have hτ := params.hτ
  have hτ' := params.hτ'
  have hanti : 2 * ϱ < exscal := by
    have h := params.slabBias
    rw [parameterSeparationConstant] at h
    nlinarith
  filter_upwards [eventually_exists_thinConfig_le_general.{u} ε εg η ϱ hεg
      (params.eta_le_one hη) params.rho_le_one C₀bd Cbias CF c₁ D,
    eventually_slabScale_of_C_le.{u} (β := β) (exscal := exscal) (η := η) (ϱ := ϱ) (τ := τ)
      (ε := ε) C₀bd Cbias Cdil (by linarith) hanti (by linarith),
    eventually_caseScale_of_C_le_O5.{u} C₀bd Cbias hC₀bd (exscal := exscal) (η := η)
      (ϱ := ϱ) (τ := τ) (τ' := τ') (ν := τ' * β / 2) (ε := ε) hexscal (by linarith) hη hϱ
      (by linarith) params.thinScale (by linarith),
    eventually_densityConstant_of_C_le (η := η) (ε := ε) (by linarith)] with
    d hC hslabS hcaseS hdens
  intro cfg bd hδ hβ hη' hex hϱ' hO5 hC₀ hCb hCF hCdil hc₁ hD hCg hCm hSPH hδw₁ hw₁
  obtain ⟨tc, htc⟩ := hC cfg bd hδ hη' hϱ' hC₀ hCb hCF hc₁ hD hCg hCm hδw₁ hw₁
  rw [hδ] at htc
  have h1C : 1 ≤ tc.C := by
    obtain ⟨B, hB⟩ := bd.bs_nonempty
    exact (tc.tb B hB).one_le_C
  refine ⟨tc, unitScaleThresholds, ?_, ?_, ?_⟩
  · exact hslabS cfg bd tc hδ hβ hex hη' hϱ' hC₀ hCb hCdil hSPH h1C htc
  · rw [hβ]
    exact hcaseS cfg bd unitScaleThresholds tc.C hδ hex hη' hϱ' hC₀ hCb
      (hO5 tc.C h1C (by rw [hδ]; exact htc)) h1C htc
      (by simpa using cfg.hδ1) (by simpa using cfg.hδ1)
  · rw [hδ, hη']
    exact hdens tc.C htc

/-- Control: the existing `eventually_thresholds_general` is the thin-guard instance. -/
example {β ζ exscal ϱ η τ τ' : ℝ}
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    {C₀bd Cbias CF Cdil c₁ : NNReal} (hC₀bd : 1 ≤ C₀bd) {D : ℕ}
    {εg : ℝ} (hεg : εg < thresholdExponent β exscal η τ) :
    type_of% (eventually_thresholds_general.{u} hexscal hϱ hη params (C₀bd := C₀bd)
      (Cbias := Cbias) (CF := CF) (Cdil := Cdil) (c₁ := c₁) hC₀bd (D := D) (εg := εg) hεg) := by
  have hbud : 6 * η + thresholdExponent β exscal η τ <
      16 * η * (1 - τ - exscal) :=
    o5_budget_of_thinHalf hη params.thinHalf
      (le_trans (thresholdExponent_le_eta β exscal η τ) (by linarith))
  filter_upwards [eventually_thresholds_general_of_O5.{u} hexscal hϱ hη params (C₀bd := C₀bd)
      (Cbias := Cbias) (CF := CF) (Cdil := Cdil) (c₁ := c₁) hC₀bd (D := D) (τ' := τ') hεg,
    eventually_caseScale_O5_of_C_le.{u} C₀bd hC₀bd (exscal := exscal) (η := η) (τ := τ)
      (τ' := τ') (ε := thresholdExponent β exscal η τ) hη hbud] with d hgen hO5
  intro cfg bd hδ hβ hη' hex hϱ' _hthin hC₀ hCb hCF hCdil hc₁ hD hCg hCm hSPH hδw₁ hw₁
  exact hgen cfg bd hδ hβ hη' hex hϱ'
    (fun C h1C hCle => hO5 cfg bd C hδ hex hη' hC₀ h1C hCle)
    hC₀ hCb hCF hCdil hc₁ hD hCg hCm hSPH hδw₁ hw₁

/-! ### Conjunct 7 folded: the thick bundle from the ED segments alone

`hThickBundle` was the boundary theorem's fourth binder. With F33's re-cut of
`Kakeya.VeryNotSticky.ThickDensityThresholds.density` the eighth field is
a plain absorption, so the whole bundle is assembled here from
`Kakeya.VeryNotSticky.thickDensityThresholds_canonical` at row G10f's
`Kakeya.VeryNotSticky.thickPlankPresentable_of_ballData`. **The one input left over is the non-ED degree bound**
on the ball-core segments at the `δ`-free `edMultiplicityConstant` — the canonical-capsule core's
debt (C7-b).** -/

/-- **Conjunct 7 at general `(a, b)`, from the produced ball data's non-ED degree bound — the last
conjunct of `ballDataGeneralTarget_edDegree`, taken pointwise — and a plank-Frostman budget.** -/
theorem eventually_exists_thickDensityThresholds_of_ED {β exscal ϱ η τ : ℝ}
    (C₀bd c₁ : NNReal)
    (hτ : 0 < τ) (hϱ : 0 < ϱ) (hc₁0 : 0 < c₁) (hgap : 0 < ϱ * β * τ / 8 - η)
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      bd.C₀ = C₀bd → bd.Cbias = lemma92Bias C₀bd ϱ → bd.c₁ = c₁ →
      (∀ B ∈ bd.bs, ∀ p ∈ bd.segs B,
        {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
          ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤
            edMultiplicityConstant) →
      ∃ (CP Θ C_NC : NNReal) (ηF : ℝ), ThickDensityThresholds cfg bd τ CP Θ C_NC ηF := by
  obtain ⟨ηF, hηF, hbudget, C_NC, hC_NC, b₀, hb₀, hvol⟩ := hplankF
  filter_upwards [
    eventually_thick_bias (lemma92Bias C₀bd ϱ) C₀bd hτ hϱ,
    eventually_plankFrostman_thresholds (thickPlankCP C₀bd) b₀ c₁ hb₀ hc₁0 hτ hbudget,
    eventually_thickDensity_bare_of_gap.{u} C₀bd (lemma92Bias C₀bd ϱ) (thickPlankCP C₀bd)
      (thickPlankΘ C₀bd C_NC ϱ) (β := β) (τ := τ) hgap]
    with d hbias hthr hbare
  intro cfg bd hδ hβ hηc _hex hϱc hC₀ hCbias hc₁' hed
  refine ⟨thickPlankCP bd.C₀, thickPlankΘ bd.C₀ C_NC cfg.ϱ, C_NC, ηF, ?_⟩
  subst hδ hβ hηc hϱc hC₀
  exact thickDensityThresholds_canonical (one_le_thickPlankCP bd.hC₀)
    (one_le_thickPlankΘ bd.hC₀ hC_NC cfg.hϱ.le) hηF hbudget (by rw [hCbias]; exact hbias)
    (fun _ => thickPlankPresentable_of_ballData cfg bd hed C_NC hC_NC)
    hvol hthr.1 (by rw [hc₁']; exact hthr.2)
    (hbare cfg bd rfl rfl rfl rfl rfl hCbias)


/-! ### The boundary theorem at general `(a, b)` -/

/-- **Residue 2 at general working dimensions `(a, b)` — the boundary theorem of
`MainLemma2/SetupSideData.lean`, re-cut** (steps G12).

Conclusion: `Kakeya.VeryNotSticky.SideDataResidue β ζ exscal ϱ η τ τ'`, the existing boundary
theorem's conclusion verbatim. Steps 1–4 are the existing proof's; step 5 obtains `(a, b, h)` and a
`Kakeya.VeryNotSticky.BallData (cfg'.withDims a b h)` from conjunct 1's general contract, and
steps 6–10 run over `cfg'' := cfg'.withDims a b h`.

The **three** explicit binders and their owners, in the module docstring's order:

(`hballData` — conjunct 1 — is gone: row G5's `Kakeya.VeryNotSticky.ballDataGeneralTarget` is
  a binder-free theorem and is applied in place.
  `hO5thick`, the O5 clause on the thick branch, was the second of five; the guarded construction supplies O5 at every `(a, b)`.
  `o5_transverse_budget_forces_large_zeta` below is the price record of the route it replaced.)
(, final assembly: **all three are theorems now and the binders are gone** — `hslabPackage`
is `eventually_slabPackage_general_of_lattice'` , `hAngular` is `eventually_hAngular_general_of_centred`
(`Conjunct6LineED.lean`), `hEDdeg` is the last conjunct of `ballDataGeneralTarget_edDegree` . The list
below is kept as the record of what they were.)

The list is **three**, not five.

Conjuncts 2, 4 and 5 are **discharged**, by `eventually_thresholds_general_of_O5` above,
`Kakeya.VeryNotSticky.eventually_ktRho2ScaleData_nonslab` and
`Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount_nonslab` respectively; the last two, and
the splitting level `Kakeya.VeryNotSticky.eventually_exists_splitInputs_nonslab`, are used under
the guard `cfg.b ≤ cfg.δ^{2 exscal}` that
`Kakeya.VeryNotSticky.nonempty_caseSideData` already carries on its `tangential` field. -/
theorem sideDataResidue_of_obligations_general {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    {C₀bd c₁ : NNReal} (hC₀bd : edSegmentsConstant ≤ C₀bd) {D : ℕ}
    (hD : ballCoverConstant ≤ D)
    (hc₁ : 0 < c₁) (hc₁' : edDensityConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1)
    {εg : ℝ} (hεg0 : 0 < εg) (hεg : εg < thresholdExponent β exscal η τ) :
    SideDataResidue.{u} β ζ exscal ϱ η τ τ' := by
  classical
  intro params hplankF
  -- parameter facts from `params`
  have hτ : 0 < τ := params.hτ
  have hslab := params.slab
  have hη1 : η ≤ 1 := by linarith
  have hexscal12 : exscal ≤ 1 / 2 := params.scale.le
  have hexscal1 : exscal < 1 := by linarith [params.scale]
  have hex3 : 3 * exscal < 1 := by linarith
  have hϱ1 : ϱ ≤ 1 := by
    have h := params.slabBias
    have hP : parameterSeparationConstant = 2 ^ 20 := rfl
    rw [hP] at h
    nlinarith
  have hm : 1 + 2 * η < (1 - exscal) * (2 + ζ) :=
    card_margin_of_caseParams hβ1 hζ.le hexscal.le hϱ hη.le params
  have hη' : 0 < η / 16 := by positivity
  have h8 : 8 * (η / 16) < η := by linarith
  have hC₀bd4 : 4 ≤ C₀bd := le_trans four_le_edSegmentsConstant hC₀bd
  have hC₀bd1 : 1 ≤ C₀bd := le_trans (by norm_num) hC₀bd4
  have hbud : 6 * η + thresholdExponent β exscal η τ < 16 * η * (1 - τ - exscal) :=
    o5_budget_of_thinHalf hη params.thinHalf
      (le_trans (thresholdExponent_le_eta β exscal η τ) (by linarith))
  filter_upwards [
    eventually_exists_localMassRefinement_slack.{u} hη' h8 hη1,
    eventually_exists_lightPieceCut.{u} hη hexscal hex3,
    eventually_card_of_count.{u} hexscal.le hexscal12 hm,
    eventually_sixteen_mul_le_rpow hexscal1,
    eventually_nnreal_mul_rpow_le_rpow edRadiusConstant (p := 1) (q := exscal)
      (by linarith),
    eventually_gridFine hη,
    eventually_aScaleData_absorb_of_le 1 h8,
    eventually_coarseLoss_absorb (η := η) (K := (4 : ℝ)) hη (by norm_num),
    Kakeya.ML2Assembly.eventually_card_thresholds,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal))
      ENNReal.coe_ne_top hη,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((Tube.coverCountLoss 3 : NNReal) : ENNReal)) ENNReal.coe_ne_top hη',
    eventually_nnreal_mul_rpow_le_const 2 1 one_pos (half_pos hη),
    eventually_exists_splitInputs_nonslab.{u} C₀bd hC₀bd1 hη hexscal hexscal12 hϱ1,
    eventually_exists_fibreScaleCount_nonslab.{u} exscal η C₀bd hC₀bd1 hexscal12 hη,
    eventually_ktRho2ScaleDataAt_nonslab.{u} (β := β) hη hϱ hϱ1 hexscal hexscal12
      (latticeRescaleConstant C₀bd) (one_le_latticeRescaleConstant hC₀bd1),
    eventually_caseScale_O5_of_C_le.{u} C₀bd hC₀bd1 (exscal := exscal) (η := η) (τ := τ)
      (τ' := τ') (ε := thresholdExponent β exscal η τ) hη hbud,
    eventually_thresholds_general_of_O5.{u} hexscal hϱ hη params (C₀bd := C₀bd)
      (Cbias := lemma92Bias C₀bd ϱ) (CF := lemma92Constant ϱ)
      (Cdil := capsuleDilationConstant)
      (c₁ := c₁) hC₀bd1 (D := D) (τ' := τ') hεg,
    ballDataGeneralTarget_edDegree.{u} β ζ exscal ϱ η τ τ' C₀bd D c₁ εg params hC₀bd hD hc₁ hc₁'
      hεg0,
    eventually_slabPackage_general_of_lattice' hβ hβ1 hexscal hϱ hη hC₀bd params,
    eventually_hAngular_general_of_centred hη C₀bd,
    eventually_exists_thickDensityThresholds_of_ED.{u} (exscal := exscal) C₀bd c₁ hτ hϱ hc₁
      (by
        have h := params.thick
        have hP : parameterSeparationConstant = 2 ^ 20 := rfl
        rw [hP] at h
        linarith)
      hplankF] with
    δ hslack hcut hcard h16 hrad0 hgrid habs hcoarse hthr hindloss hLcap hhalf hsplitδ hfscδ hktδ
    hO5thinδ hthrδ hbdδ hslabδ hangδ hthickδ
  intro ι s T hball hcen _huni hmax hfull hcount cfg _e _c hparams _href _hc
  -- the Katz–Tao / Frostman estimates and the K_KT window come from `cfg`
  obtain ⟨hβc, -, hδc, hexc, hϱc, hηc⟩ := hparams
  have hKT : KatzTaoEstimate.{u} E3 β := hβc ▸ cfg.ktEstimate
  have hF : FrostmanEstimate.{u} E3 β := hβc ▸ cfg.fEstimate
  have hckt : Kakeya.CoarseKTData.{u} β ϱ η exscal δ := by
    have h := cfg.ckt
    rw [hβc, hϱc, hηc, hexc, hδc] at h
    exact h
  -- step 1: the slack family (residue 1 re-run at `η' = η/16`)
  have hcard' := hcard s T hcount
  obtain ⟨s', T', hs', htube, hsh, huniC, hfloor, htc, hmass, hlm⟩ :=
    hslack s T hball hmax hfull hcard'
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcar : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcar i]; exact hball i (hs' hi)
  -- step 2: the island cut (T1/T1b), exporting the eight cover clauses
  obtain ⟨Light, hL, bι, bs, ctr, P, hbsne, hcb, hdisj, -, hcov, hover, -, h16b, hmeas, hne,
    hii, hiii, hiv⟩ := hcut s' T' hball' hfloor htc hlm
  -- step 3: the configuration `cfg'` (T2b), still at `a = b = δ`
  obtain ⟨cfg', e', c', hparams', href', hc', hse', hshade, ha, hb, hcen'⟩ :=
    exists_config_of_slackCut_at.{u} hβ hβ1 hζ hexscal hϱ hη hη' h8 params hKT hF
      hckt.toCoarseKTWindow hckt.hδrad hgrid habs hcoarse hthr hindloss hLcap hhalf
      s T hball hcen _huni hmax hfull hcount s' T' Light hL hs' htube hsh huniC htc hmass hii hiii hiv
  obtain ⟨hβ', hζ', hδ', hex', hϱ', hη''⟩ := hparams'
  -- step 4: the cover, transported along `e'` and the shade identity to `cfg'`
  have hr₁' : cfg'.r₁ = δ ^ exscal := by simp only [VeryNotSticky.r₁, hδ', hex']
  have hδr : 16 * (cfg'.δ : ℝ) ≤ (cfg'.r₁ : ℝ) := by rw [hδ', hr₁']; exact h16
  have hrad : ((edRadiusConstant : NNReal) : ℝ) * (cfg'.δ : ℝ) ≤ (cfg'.r₁ : ℝ) := by
    rw [hδ', hr₁']
    have h := hrad0
    rw [NNReal.rpow_one] at h
    exact_mod_cast h
  have hPball16 : ∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg'.r₁ : ℝ) / 16) := by
    rw [hr₁']; exact h16b
  have hPball : ∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg'.r₁ : ℝ) := by
    rw [hr₁']; exact hcb
  have hoverlap : ∀ (x : E3) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg'.r₁ : ℝ)) → t.card ≤ ballCoverConstant := by
    rw [hr₁']; exact hover
  have hmem : ∀ j, j ∈ cfg'.s ↔ e' j ∈ s' := by
    intro j; rw [← hse', Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hPcov : ∀ j ∈ cfg'.s, (cfg'.T j).shade ⊆ ⋃ B ∈ bs, P B := by
    intro j hj
    have h1 : (cfg'.T j).shade = (T' (e' j)).shade \ Light := by
      have := hshade (e' j); rwa [Equiv.symm_apply_apply] at this
    rw [h1]; exact hcov (e' j) ((hmem j).1 hj)
  have hunion : (⋃ i ∈ s', ((T' i).shade \ Light)) ⊆ ⋃ j ∈ cfg'.s, (cfg'.T j).shade := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    refine ⟨e'.symm i, ?_, ?_⟩
    · rw [hmem, Equiv.apply_symm_apply]; exact hi
    · rw [hshade i]; exact hxi
  have hPne : ∀ B ∈ bs, (P B ∩ ⋃ j ∈ cfg'.s, (cfg'.T j).shade).Nonempty :=
    fun B hB => (hne B hB).mono (Set.inter_subset_inter_right _ hunion)
  -- step 5: the ball data at general `(a, b)` (conjunct 1, row G5) and the re-dimensioned `cfg''`
  obtain ⟨a, b, hdims, hbdrest⟩ :=
    hbdδ cfg' hδ' hη'' hex' hϱ' hrad bs ctr P hbsne hPball16 hPball hdisj hmeas hPcov
      hoverlap hPne
  set cfg'' : VeryNotSticky.{u} := cfg'.withDims a b hdims with hcfg''
  obtain ⟨bd, hbdC₀, hbdCbias, hbdCF, hbdCdil, hbdc₁, hbdD, hbdCg, hbdCm, hbdSPH,
    hδw₁, hw₁one, -, -, hmarginG, hEDbd⟩ := hbdrest
  -- O5 on both branches of the thin/thick dichotomy
  have hO5 : ∀ C : NNReal, 1 ≤ C → C ≤ cfg''.δ ^ (-thresholdExponent β exscal η τ) →
      statement_of_universal_caseScale_O5.{u} cfg'' bd τ τ' C := by
    -- The thin guard is the clause's own first antecedent, so
    -- row G6 supplies O5 for **every** `(a, b)` and the thin/thick dichotomy disappears.
    exact fun C h1 h2 => hO5thinδ cfg'' bd C hδ' hex' hη'' hbdC₀ h1 h2
  -- step 6: the thin configuration and the thresholds (conjunct 2, rows G6/G7/G7b)
  obtain ⟨tc, thr₀, hslabScale, hcaseScale, hdens⟩ :=
    hthrδ cfg'' bd hδ' hβ' hη'' hex' hϱ' hO5 hbdC₀ hbdCbias hbdCF hbdCdil hbdc₁ hbdD hbdCg
      hbdCm hbdSPH hδw₁ hw₁one
  -- step 7: the thick bundle (conjunct 7, rows G13 → G10 → G11)
  obtain ⟨CP, Θ, C_NC, ηF, thick⟩ :=
    hthickδ cfg'' bd hδ' hβ' hη'' hex' hϱ' hbdC₀ hbdCbias hbdc₁ hEDbd
  -- steps 8–9: the tangential inputs, under the two guards `nonempty_caseSideData` carries
  have htangential : cfg''.a ≤ cfg''.δ ^ (1 - τ) → cfg''.b ≤ cfg''.δ ^ (2 * cfg''.exscal) →
      Nonempty (TangentialInputs cfg'' tc τ') := by
    intro hthinG hbG
    obtain ⟨k, hk, hge, hle, hbuild⟩ := hsplitδ cfg'' bd hδ' hη'' hex' hϱ' hbdC₀ hbG
    obtain ⟨Ccnt, hCcnt, hfsc⟩ := hfscδ cfg'' bd hδ' hη'' hex' hbG hbdC₀ k hk hge hle
    obtain ⟨Cang, hCang, hangular⟩ := hangδ cfg'' bd hδ' hη'' hex' hϱ' hbG hbdC₀ hcen' k hk hge hle
    obtain ⟨split⟩ := hbuild Cang hCang hangular Ccnt hCcnt hfsc
    have hest : cfg''.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
        (4 * cfg''.ϱ) (9 * cfg''.η) (3 * cfg''.ϱ) := by
      have h := hktδ cfg'' bd hδ' hβ' hη'' hex' hϱ' hbG
      rwa [hbdC₀]
    exact
      ⟨{ slab := fun hB ta =>
           (hslabδ cfg'' bd tc hδ' hβ' hη'' hex' hϱ' hthinG hbG hbdC₀ hbdCbias
             (hmarginG (by exact_mod_cast hthinG)) hB ta).some
         slabMult :=
           { η₁ := 9 * cfg''.η
             fullness_threshold := le_rfl
             estimate := hest
             densityConstant := hdens }
         split := split.toPB }⟩
  -- step 10: assemble
  exact ⟨cfg'', bd, e', c', ⟨hβ', hζ', hδ', hex', hϱ', hη''⟩, href', hc',
    nonempty_caseSideData thick tc hslabScale hcaseScale
      (fun hthinG hbG => (htangential hthinG hbG).some)⟩

/-! ### Tripwires -/

/-- **Tripwire 1 — the general boundary composes through the frozen consumer to the frozen
target.** Given the five binders at one admissible parameter set, the type of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` at that parameter set follows. The binder texts
are reproduced here verbatim, so this `example` also pins them: if the theorem's binder list
drifts, the application below stops elaborating. This is the compiled statement of "the distance
between the general branch and the last Section-9 leaf". -/
theorem exists_setup_caseSideData_general {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    {C₀bd c₁ : NNReal} (hC₀bd : edSegmentsConstant ≤ C₀bd) {D : ℕ}
    (hD : ballCoverConstant ≤ D)
    (hc₁ : 0 < c₁) (hc₁' : edDensityConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1)
    {εg : ℝ} (hεg0 : 0 < εg) (hεg : εg < thresholdExponent β exscal η τ) :
    SetupCaseSideDataAt.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w :=
  exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
    (sideDataResidue_of_obligations_general.{u} hβ hβ1 hζ hexscal hϱ hη hC₀bd hD hc₁ hc₁'
      hεg0 hεg)

/-- **T12 tripwire — the general leaf really has `exists_setup_caseSideData`'s type.**
`Kakeya.VeryNotSticky.exists_setup_caseSideData_general` is applied here at *exactly* the
argument list of `Kakeya.VeryNotSticky.exists_setup_caseSideData` and nothing else, and its result is checked against `type_of%` of the frozen leaf. If either the
protected statement or the general theorem's conclusion drifts, this stops elaborating. -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    {C₀bd c₁ : NNReal} (hC₀bd : edSegmentsConstant ≤ C₀bd) {D : ℕ}
    (hD : ballCoverConstant ≤ D)
    (hc₁ : 0 < c₁) (hc₁' : edDensityConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1)
    {εg : ℝ} (hεg0 : 0 < εg) (hεg : εg < thresholdExponent β exscal η τ) :
    SetupCaseSideDataAt.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w :=
  exists_setup_caseSideData_general.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
    hC₀bd hD hc₁ hc₁' hεg0 hεg


/-- **Tripwire 2 — the general conjunct-3 binder subsumes the existing degenerate conjunct 3.**
Its conclusion is the type of `Kakeya.VeryNotSticky.sideDataObligations_conjunct3_of_margin`
verbatim; the proof is the two-goal specialisation
`cfg.a = cfg.δ ⇒ cfg.a ≤ cfg.δ^{1-τ}` (`Kakeya.VeryNotSticky.CaseParams.hτ`) and
`cfg.b = cfg.δ ⇒ cfg.b ≤ cfg.δ^{2 exscal}`
(`Kakeya.VeryNotSticky.notslab_of_b_eq_delta`). -/
example {β ζ exscal ϱ η τ τ' : ℝ} (hη : 0 < η) (hexscal : 0 ≤ exscal) (hϱ : 0 < ϱ)
    (hητ' : η < τ') (C₀bd : NNReal) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hslabPackage : CaseParams β ζ exscal ϱ η τ τ' →
      ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
        (tc : ThinConfig cfg bd),
        cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
        cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
        bd.C₀ = C₀bd → bd.Cbias = lemma92Bias C₀bd ϱ →
        (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
          Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
            Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
        ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
          Nonempty (SlabPackage cfg ta)) :
    type_of% (sideDataObligations_conjunct3_of_margin.{u} (β := β) hη hexscal hϱ hητ'
      C₀bd (lemma92Bias C₀bd ϱ)) := by
  have hτ := params.hτ
  have hhalf : exscal ≤ 1 / 2 := params.scale.le
  filter_upwards [hslabPackage params] with d hgen
  intro cfg bd tc hδ hβ hη' hex hϱ' ha hb hC₀ hCb hmargin B hB ta
  refine hgen cfg bd tc hδ hβ hη' hex hϱ' ?_ ?_ hC₀ hCb hmargin hB ta
  · rw [ha]
    nth_rewrite 1 [show cfg.δ = cfg.δ ^ (1 : ℝ) from (NNReal.rpow_one _).symm]
    exact NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith)
  · exact notslab_of_b_eq_delta cfg (by rw [hex]; exact hhalf) hb

/-- **Tripwire 3 — `withDims` is definitionally transparent at the configuration's own
dimensions.** Every `Kakeya.VeryNotSticky.BallData cfg` is a `BallData (cfg.withDims cfg.a cfg.b
cfg.hdims)` by structure eta, and the two configurations are `rfl`-equal. This is the sense in
which the degenerate route is the `(a, b) = (cfg.a, cfg.b)` instance of the re-cut: the type
`BallData (cfg.withDims a b h)` of conjunct 1's output is not a new kind of object. -/
example (cfg : VeryNotSticky.{u}) : cfg.withDims cfg.a cfg.b cfg.hdims = cfg := rfl

example (cfg : VeryNotSticky.{u}) (bd : BallData cfg) :
    BallData (cfg.withDims cfg.a cfg.b cfg.hdims) := bd

end Kakeya.VeryNotSticky

end
