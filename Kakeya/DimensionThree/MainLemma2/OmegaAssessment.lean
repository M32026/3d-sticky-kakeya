/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimatesOmega
public import Kakeya.DimensionThree.MainLemma1

/-!
# An assessment of `Kakeya/PartialEstimatesOmega.lean`, in compiled form

`Kakeya/PartialEstimatesOmega.lean` is an alternative *outer* scheme for the Kakeya bootstrap: it
carries a second parameter `ω` — a budget standing in the same power of `δ` as the accuracy, but
quantified **before** it — and its headline
`Kakeya.katzTaoEstimate_of_mainLemma2Omega` derives the one-parameter `K_KT(β)` from an `ω`-form
of Main Lemma 2 (`hML2`) and an `ω`-form of Main Lemma 1 (`hML1`).  Neither hypothesis has a
producer in this tree.  This module records, as compiler-checked statements rather than prose,
what is actually available, what would have to be true for the scheme to be usable, and where the
budget helps and where it hurts.

## What is here

* `Kakeya.OmegaAssessment.ML1OmegaHyp` / `ML2OmegaHyp` and
  `Kakeya.OmegaAssessment.assembly_signature_pin`: the two hypothesis slots of
  `Kakeya.katzTaoEstimate_of_mainLemma2Omega`, named, and pinned to that theorem by application.
  If either binder drifts, this file stops compiling.

* `Kakeya.OmegaAssessment.ml1Omega_forall_of_tree`: what Section 8 **does** supply — the
  *"for every budget"* reading of `hML1`.  It is a consequence of
  `Kakeya.KatzTaoEstimate.frostmanEstimate` and
  `Kakeya.katzTaoEstimate_iff_forall_omega_pos`, and it is strictly weaker than `hML1`, which
  asks for `K_F(γ, ω)` from `K_KT(β, ω)` at **one** budget.

* `Kakeya.OmegaAssessment.katzTaoEstimate_of_mainLemma2Omega_of_uniformDrop`: **`hML1` is
  removable.**  If the `ω`-form of Main Lemma 2 comes with a drop that is bounded below,
  uniformly in the budget, by a positive monotone function of `β` alone, then the whole outer
  scheme runs on the *one-parameter* Main Lemma 1 that this tree already has, and no `ω`-uniform
  Main Lemma 1 is needed at all.  So the missing consumer-side input is not "an `ω`-uniform Main
  Lemma 1"; it is "a budget-uniform floor on the `ω`-drop".

* `Kakeya.OmegaAssessment.no_uniform_floor_of_starved_drop`: and that floor is exactly what the
  donor's `ω`-route does not have.  Its `Kakeya.ML2Reduction.omegaDrop_spec` proves
  `ν(β, ω) ≤ 7 (ω/250) ^ 4097`, and a drop with that bound admits **no** positive lower bound
  uniform in `ω`.  This is the precise sense in which the two-parameter route needs a
  two-parameter Main Lemma 1: its drop is starved by the budget, so the descent cannot be run at
  `ω → 0`.

* `Kakeya.OmegaAssessment.omega_pays_fixed_loss` versus
  `Kakeya.OmegaAssessment.oneParam_fixed_loss_fails` /
  `oneParam_fixed_loss_forces_card`: the arithmetic behind the claim that the `ω`-route "buys no
  cardinality split".  A loss that is a fixed power of `δ` is payable out of the budget at
  accuracy `0` and with no cardinality factor; against the one-parameter estimate the same loss
  is **not** payable out of the accuracy, and any repair forces a lower bound
  `|𝕋| ^ b ≥ δ ^ -(c - ε)` on the cardinality.  That forced lower bound is the origin of the
  `|𝕋| ≥ δ⁻¹` threshold of `Kakeya.ML2Assembly` and hence of its `SmallCard` residue.

* `Kakeya.OmegaAssessment.squeeze_budget_obstruction` and
  `squeeze_closes_at_zero_budget`: the budget is **rigid under rescaling** and the accuracy is
  not.  An affine squeeze that presents a `ρ`-family at a scale `δ = ρ ^ k` with `k ≥ 2` — the
  mechanism by which the band hypothesis `|𝕋| < δ⁻¹` is claimed to be vacuous — multiplies the
  exponent of every factor by `k`.  On the accuracy that is free (`k · (ε/4) ≤ ε` for `k ≤ 4`);
  on a positive budget it is not, and the bookkeeping closes only at accuracies **above** the
  budget.

* `Kakeya.OmegaAssessment.plank_budget_overshoots` and `plank_budget_telescopes_at_b`: the same
  rigidity, with the opposite sign.  `Kakeya.FrostmanEstimate.plankEstimate` charges its accuracy
  at the **short** plank scale `a`; the two nested applications inside Main Lemma 1 then multiply
  to `δ ^ (-ω) · (b/a) ^ ω`, which overshoots `δ ^ (-ω)`, while the `b`-placement — the one that
  would telescope — undershoots it.  This is why the `ω`-budget passes through Main Lemma 1's
  tube seams and fails at its plank seam.

Nothing in this module is imported by anything, and nothing here changes
`Kakeya/PartialEstimatesOmega.lean` or any Main Lemma file.  It is an check artifact.
-/

@[expose] public section

open MeasureTheory Topology Filter

namespace Kakeya.OmegaAssessment

universe u

/-! ### 1. The two hypothesis slots of the assembly, named and pinned -/

/-- The `hML1` slot of `Kakeya.katzTaoEstimate_of_mainLemma2Omega`, verbatim: an `ω`-uniform Main
Lemma 1, reading `K_KT(β, ω)` and returning `K_F(γ, ω)` at the **same** budget `ω`. -/
def ML1OmegaHyp : Prop :=
  ∀ β γ ω : ℝ, 0 ≤ β → β < γ → γ ≤ 1 → 0 < ω →
    KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω →
    FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ ω

/-- The `hML2` slot of `Kakeya.katzTaoEstimate_of_mainLemma2Omega`, verbatim: an `ω`-form of Main
Lemma 2 whose drop `g` is produced before the accuracy. -/
def ML2OmegaHyp (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ β ω : ℝ, 0 < β → β ≤ 1 → 0 < ω →
    KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω →
    FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω →
    KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β (ω - g β ω)

/-- **Fidelity pin.**  The two `def`s above really are the two hypothesis slots of
`Kakeya.katzTaoEstimate_of_mainLemma2Omega`: this theorem is that theorem applied to them.  If a
binder in either slot moves, this application stops elaborating. -/
theorem assembly_signature_pin (g : ℝ → ℝ → ℝ)
    (hg_pos : ∀ β ω : ℝ, 0 < β → β ≤ 1 → 0 < ω → 0 < g β ω)
    (hg_mono : ∀ ω : ℝ, 0 < ω → MonotoneOn (fun β ↦ g β ω) (Set.Ioc (0 : ℝ) 1))
    (hML2 : ML2OmegaHyp.{u} g) (hML1 : ML1OmegaHyp.{u})
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β :=
  katzTaoEstimate_of_mainLemma2Omega.{u} g hg_pos hg_mono hML2 hML1 hβ hβ1

/-! ### 2. What Section 8 supplies for the `hML1` slot -/

/-- **The tree supplies the "for every budget" reading of `hML1`, and only that.**

`Kakeya.KatzTaoEstimate.frostmanEstimate` (Main Lemma 1) plus
`Kakeya.katzTaoEstimate_iff_forall_omega_pos` give `K_F(γ, ω)` at every budget from `K_KT(β, ω)`
at **every** budget.  `Kakeya.OmegaAssessment.ML1OmegaHyp` asks for it from `K_KT(β, ω)` at
**one** budget, and no route in `Kakeya/PartialEstimatesOmega.lean` closes that gap: the only
budget-absorption there, `Kakeya.KatzTaoEstimateOmega.of_forall_gt`, consumes `∀ ω' > ω`. -/
theorem ml1Omega_forall_of_tree {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β < γ) (hγ1 : γ ≤ 1)
    (h : ∀ ω > (0 : ℝ), KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) β ω) :
    ∀ ω : ℝ, 0 ≤ ω → FrostmanEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ ω := by
  intro ω hω
  exact FrostmanEstimate.toOmega hω
    (KatzTaoEstimate.frostmanEstimate.{u} hβ hβγ hγ1
      (katzTaoEstimate_iff_forall_omega_pos.{u}.mpr h))

/-! ### 3. `hML1` is removable, at the price of a budget-uniform floor on the drop -/

/-- **The outer scheme without an `ω`-uniform Main Lemma 1.**

Suppose the `ω`-form of Main Lemma 2 holds with a drop `g` that is bounded below, *uniformly in
the budget*, by a function `ĝ` of the exponent alone which is positive and monotone on `(0, 1]`.
Then `K_KT(β)` follows for every `β ∈ (0, 1]` using only the **one-parameter** Main Lemma 1
`Kakeya.KatzTaoEstimate.frostmanEstimate` that this tree already has: the hypothesis `hML1` of
`Kakeya.katzTaoEstimate_of_mainLemma2Omega` is not needed.

The mechanism is that with a budget-uniform floor the descent can be run on the *one-parameter*
predicate `K_KT(·)`, re-entering the budget only for the single application of `hML2` and the
trade, and leaving it again through `Kakeya.katzTaoEstimate_iff_forall_omega_pos`.  It is
`Kakeya.katzTaoEstimate_of_mainLemma2Omega`'s proof with the invariant moved one level out.

**What this says about the module.**  The consumer-side obligation is *not* "an `ω`-uniform Main
Lemma 1".  It is "a floor on the `ω`-drop that does not vanish with the budget", and
`Kakeya.OmegaAssessment.no_uniform_floor_of_starved_drop` shows the donor's drop has none. -/
theorem katzTaoEstimate_of_mainLemma2Omega_of_uniformDrop
    (g : ℝ → ℝ → ℝ) (ĝ : ℝ → ℝ)
    (hĝ_pos : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, 0 < ĝ γ)
    (hĝ_mono : MonotoneOn ĝ (Set.Ioc (0 : ℝ) 1))
    (hĝ_le : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, ∀ ω : ℝ, 0 < ω → ĝ γ ≤ g γ ω)
    (hML2 : ML2OmegaHyp.{u} g)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  set S : Set ℝ := {γ | KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ} with hSdef
  have key : Set.Ioc (0 : ℝ) 1 ⊆ S := by
    refine ioc_subset_of_sub_mem_of_monotoneOn (β := 0) (s := S) (f := fun γ ↦ ĝ γ / 6)
      ?_ ?_ ?_ ?_ ?_
    · intro γ γ' hle hγ
      exact KatzTaoEstimate.mono hle hγ
    · exact KatzTao_one
    · intro γ hγ hS
      -- `hS : K_KT(γ)`; goal `K_KT(γ - ĝ γ / 6)`.
      have hγ0 : 0 < γ := hγ.1
      have hγ1 : γ ≤ 1 := hγ.2
      have hĝγ : 0 < ĝ γ := hĝ_pos γ hγ
      have hSγ : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ := hS
      -- The target exponent `γ'`: `γ + ĝ γ / 6` when that is below `1`, and `1` otherwise.
      -- Frostman at `γ'` comes from Main Lemma 1 in the first case and from `K_F(1)` in the
      -- second; **only the one-parameter Main Lemma 1 is used**.
      obtain ⟨γ', hγ'1, hγ'ge, hγ'le, hF⟩ :
          ∃ γ' : ℝ, γ' ≤ 1 ∧ γ ≤ γ' ∧ γ' ≤ γ + ĝ γ / 6 ∧
            FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ' := by
        rcases lt_or_ge (γ + ĝ γ / 6) 1 with hlt | hge
        · exact ⟨γ + ĝ γ / 6, hlt.le, by linarith, le_rfl,
            KatzTaoEstimate.frostmanEstimate.{u} hγ0.le (by linarith) hlt.le hSγ⟩
        · exact ⟨1, le_rfl, hγ1, hge, frostmanEstimate_one⟩
      have hγ'0 : 0 < γ' := lt_of_lt_of_le hγ0 hγ'ge
      have hγ'Ioc : γ' ∈ Set.Ioc (0 : ℝ) 1 := ⟨hγ'0, hγ'1⟩
      have hKT' : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) γ' :=
        KatzTaoEstimate.mono hγ'ge hSγ
      -- run the budget for each `ω > 0` and leave it again
      rw [hSdef]
      simp only [Set.mem_setOf_eq]
      rw [katzTaoEstimate_iff_forall_omega_pos]
      intro ω hω
      have hgpos : 0 ≤ g γ' ω := le_trans (hĝ_pos γ' hγ'Ioc).le (hĝ_le γ' hγ'Ioc ω hω)
      have hstep : KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3)) γ' (ω - g γ' ω) :=
        hML2 γ' ω hγ'0 hγ'1 hω (KatzTaoEstimate.toOmega hω.le hKT')
          (FrostmanEstimate.toOmega hω.le hF)
      have htraded : KatzTaoEstimateOmega.{u} (EuclideanSpace ℝ (Fin 3))
          (γ' - g γ' ω / 3) ω := KatzTaoEstimateOmega.trade hn hgpos hstep
      refine KatzTaoEstimateOmega.mono ?_ htraded
      have h1 : ĝ γ ≤ ĝ γ' := hĝ_mono hγ hγ'Ioc hγ'ge
      have h2 : ĝ γ' ≤ g γ' ω := hĝ_le γ' hγ'Ioc ω hω
      linarith
    · intro x hx y hy hxy
      have := hĝ_mono hx hy hxy
      simpa using by linarith
    · intro γ hγ
      have := hĝ_pos γ hγ
      simpa using by linarith
  exact key ⟨hβ, hβ1⟩

set_option exponentiation.threshold 5000 in
/-- **The `ω`-route's own drop has no budget-uniform floor.**

`Kakeya.ML2Reduction.omegaDrop_spec` of the donor branch proves
`ν(β, ω) ≤ 7 (ω / 250) ^ 4097` for `0 < ω ≤ 1`, and `omegaDropMono ≤ omegaDrop` at the capped
budget.  A drop obeying that bound admits no positive `c` with `c ≤ g γ ω` for all small `ω`, so
`Kakeya.OmegaAssessment.katzTaoEstimate_of_mainLemma2Omega_of_uniformDrop` is **not** applicable
to it, and the `ω`-route genuinely needs the `ω`-uniform Main Lemma 1 it does not have. -/
theorem no_uniform_floor_of_starved_drop {g : ℝ → ℝ → ℝ} {γ c : ℝ} (hc : 0 < c)
    (hstarve : ∀ ω : ℝ, 0 < ω → ω ≤ 1 → g γ ω ≤ 7 * (ω / 250) ^ 4097) :
    ¬ (∀ ω : ℝ, 0 < ω → ω ≤ 1 → c ≤ g γ ω) := by
  intro hfloor
  set ω : ℝ := min 1 (c * 250 / 14) with hωdef
  have hω0 : 0 < ω := lt_min one_pos (by positivity)
  have hω1 : ω ≤ 1 := min_le_left _ _
  have hωc : ω ≤ c * 250 / 14 := min_le_right _ _
  have hbase0 : 0 ≤ ω / 250 := by positivity
  have hbase1 : ω / 250 ≤ 1 := by linarith
  have hpow : (ω / 250) ^ 4097 ≤ ω / 250 :=
    pow_le_of_le_one hbase0 hbase1 (by norm_num)
  have h1 : g γ ω ≤ 7 * (ω / 250) := le_trans (hstarve ω hω0 hω1) (by linarith)
  have h2 : c ≤ g γ ω := hfloor ω hω0 hω1
  linarith

/-! ### 4. Why the budget buys no cardinality split, and the accuracy cannot -/

/-- **A fixed power of `δ` is payable out of the budget, at accuracy zero and with no
cardinality factor.**

This is the arithmetic core of the donor's
`Kakeya.ML2Reduction.multiplicity_le_of_le_rpow_neg_half_omega`: the every-scale branch's output
`μ ≤ δ ^ (-ω/2)` already implies the conclusion clause of `K_KT(β, ω - g)` at every accuracy
`ε ≥ 0`, so the branch spends none of the accuracy and never consults `|𝕋|`. -/
theorem omega_pays_fixed_loss {δ ω g ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hg : g ≤ ω / 2) (hε : 0 ≤ ε) :
    δ ^ (-(ω / 2)) ≤ δ ^ (-(ω - g) - ε) :=
  Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)

/-- **Against the one-parameter estimate the same loss is not payable out of the accuracy.**

For a loss `c` fixed before the accuracy, `δ ^ (-c) ≤ δ ^ (-ε)` is false at every `ε < c` and
every `0 < δ < 1`.  This is why the one-parameter route has to route the fixed loss through the
cardinality factor. -/
theorem oneParam_fixed_loss_fails {δ c ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hcε : ε < c) :
    ¬ (δ ^ (-c) ≤ δ ^ (-ε)) := by
  intro h
  have := Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (show -c < -ε by linarith)
  linarith

/-- **…and any repair through the cardinality factor forces a lower bound on the cardinality.**

If `δ ^ (-c) ≤ δ ^ (-ε) * N` then `N ≥ δ ^ (-(c - ε))`.  With `N = |𝕋| ^ b` and `c - ε` bounded
below by a fixed positive constant, that is a lower bound on `|𝕋|` which is a fixed power of `δ`:
the origin of `Kakeya.ML2Assembly`'s threshold `δ⁻¹ ≤ |𝕋|`, of its case split, and hence of the
`SmallCard` residue on the small side. -/
theorem oneParam_fixed_loss_forces_card {δ c ε N : ℝ} (hδ0 : 0 < δ)
    (h : δ ^ (-c) ≤ δ ^ (-ε) * N) : δ ^ (-(c - ε)) ≤ N := by
  have hsplit : δ ^ (-c) = δ ^ (-ε) * δ ^ (-(c - ε)) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hpos : (0 : ℝ) < δ ^ (-ε) := Real.rpow_pos_of_pos hδ0 _
  rw [hsplit] at h
  exact le_of_mul_le_mul_left h hpos

/-! ### 5. The budget is rigid under rescaling; the accuracy is not -/

/-- **An affine squeeze cannot be run at a positive budget.**

The squeeze that presents a family of `ρ`-tubes as a family of `δ`-tubes with `δ = ρ ^ k`
multiplies every exponent by `k`, and `k ≥ 2` is forced (a Katz–Tao family of `ρ`-tubes in `ℝ³`
can have `ρ ^ (-2)` members, and the band asks for fewer than `δ⁻¹`).  Its bookkeeping asks for
`k (ω + ε₀) ≤ ω + ε`, where `ε₀` is the accuracy at which the band statement is read.  At a
positive budget that forces `ε ≥ ω + 2 ε₀`: the squeeze closes only at accuracies **above** the
budget, where the budget conveys nothing. -/
theorem squeeze_budget_obstruction {k ω ε ε₀ : ℝ} (hk : 2 ≤ k) (hω : 0 < ω) (hε₀ : 0 < ε₀)
    (h : k * (ω + ε₀) ≤ ω + ε) : ω + 2 * ε₀ ≤ ε := by nlinarith

/-- **…and at budget zero it closes with room.**  At `ω = 0` the same bookkeeping is
`k (ε/4) ≤ ε`, true for every `k ≤ 4`.  The contrast with
`Kakeya.OmegaAssessment.squeeze_budget_obstruction` is the whole point: the accuracy is elastic
under rescaling because it is re-chosen at each application, and the budget is not, because it is
fixed before the accuracy. -/
theorem squeeze_closes_at_zero_budget {k ε : ℝ} (hk : k ≤ 4) (hε : 0 < ε) :
    k * ((0 : ℝ) + ε / 4) ≤ 0 + ε := by nlinarith

/-- **The budget does not telescope through Main Lemma 1's plank seam.**

`Kakeya.FrostmanEstimate.plankEstimate` (GWZ Lemma 6.4) charges its accuracy at the **short**
plank scale `a`.  Inside branch (ii) of GWZ Lemma 8.1 the estimate is applied twice, at the outer
scales `(a, b)` and the inner scales `(δ/b, δ/a)`; charging the budget where the accuracy is
charged, the two losses multiply to `δ ^ (-ω) · (b/a) ^ ω`, which **exceeds** `δ ^ (-ω)`, strictly
whenever `a < b` and `ω > 0`. -/
theorem plank_budget_overshoots {a b δ ω : ℝ} (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (_hω : 0 ≤ ω) :
    a ^ (-ω) * (δ / b) ^ (-ω) = δ ^ (-ω) * (b / a) ^ ω := by
  rw [Real.div_rpow hδ.le hb.le, Real.div_rpow hb.le ha.le, Real.rpow_neg ha.le,
    Real.rpow_neg hδ.le, Real.rpow_neg hb.le]
  have h1 : a ^ ω ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha ω)
  have h2 : b ^ ω ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb ω)
  have h3 : δ ^ ω ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hδ ω)
  field_simp

/-- The overshoot of `Kakeya.OmegaAssessment.plank_budget_overshoots` is strict. -/
theorem plank_budget_overshoots_strict {a b δ ω : ℝ} (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hω : 0 < ω) :
    δ ^ (-ω) < a ^ (-ω) * (δ / b) ^ (-ω) := by
  have hb : 0 < b := lt_trans ha hab
  rw [plank_budget_overshoots ha hb hδ hω.le]
  have hbig : (1 : ℝ) < b / a := (one_lt_div ha).mpr hab
  have : (1 : ℝ) < (b / a) ^ ω := Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr
    (Or.inl ⟨hbig, hω⟩)
  nlinarith [Real.rpow_pos_of_pos hδ (-ω)]

/-- **The placement that would telescope is the long one — and it is the one GWZ Lemma 6.4 does
not have.**  Charged at `b` instead, the two applications multiply to `δ ^ (-ω) · (a/b) ^ ω`,
which is at most `δ ^ (-ω)`. -/
theorem plank_budget_telescopes_at_b {a b δ ω : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : 0 < b)
    (hδ : 0 < δ) (hω : 0 ≤ ω) :
    b ^ (-ω) * (δ / a) ^ (-ω) = δ ^ (-ω) * (a / b) ^ ω ∧
      b ^ (-ω) * (δ / a) ^ (-ω) ≤ δ ^ (-ω) := by
  have heq : b ^ (-ω) * (δ / a) ^ (-ω) = δ ^ (-ω) * (a / b) ^ ω :=
    plank_budget_overshoots hb ha hδ hω
  refine ⟨heq, ?_⟩
  rw [heq]
  have hle : a / b ≤ 1 := (div_le_one hb).mpr hab
  have h0 : (0 : ℝ) ≤ a / b := by positivity
  have : (a / b) ^ ω ≤ 1 := Real.rpow_le_one h0 hle hω
  nlinarith [Real.rpow_pos_of_pos hδ (-ω)]

end Kakeya.OmegaAssessment

end
