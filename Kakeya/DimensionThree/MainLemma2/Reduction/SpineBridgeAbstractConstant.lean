/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineBridgeCoverMap

/-!
# The covering bridge, abstract in its fibre constant

 The direct route of `Reduction/SpineBridgeCoverMap.lean` **is** the
source's (l.4823–4826 pulls back and reads the original family's essential distinctness at its own
radius; it never pushes through `ϖ`), so the named `max` does not bind on the critical path and the
push route's four-orders excess is cost, not fidelity — it is `δ`-free.  The constants are therefore parameterized below.

## The change: the constant becomes a parameter

`Kakeya.ML2Core.defectCoveringBridge` hard-codes `5000⁶` in `hAfib` and `10³⁰` in `htest`.
`Kakeya.ML2Core.push_constant_not_below_source` shows `hAfib` is **false** on the push route and
true on the direct one — a hypothesis that silently depends on which producer the caller used.
`defectCoveringBridge'` takes the fibre constant `F` and the scale-test constant `C` as
parameters, linked by the single row

  `hlink : bridgeScaleTestConstant F ≤ C`,   `bridgeScaleTestConstant F = 2·F·56³`

which is exactly the numeric slack the source's proof uses at l.5666–5669 (`2+4ζ ≤ 3`, so `56^E`
is at most `56³`).  `bridgeScaleTestConstant_le_of_source` is the record that the
source's own pair `(F₀, C) = (5000⁶, 10³⁰)` satisfies it.

**Nothing existing changes.**  `defectCoveringBridge_of_abstract` is the existing statement,
character for character, derived from `defectCoveringBridge'` in one application at
`F := 5000⁶`, `C := 10³⁰`; and `BridgeStatement` is that statement written once, with two
`example`s inhabiting it — one by the existing theorem, one by the derived one.  If the two differed
in a single binder, one of those two `example`s would fail to elaborate.  That is the pin.

## The two routes, both * `defectCoveringBridge_of_abstract` — the **direct** route, at the source's `F₀ = 5000⁶` and
  `10³⁰`.  This is the route l.4823–4826 takes and the one `coverMap_fills_bridge_binders`
  supplies.
* `defectCoveringBridge_pushRoute` — the **push** route, at `coverFibreConstant 3 1 20` and the
  scale-test constant that constant forces.  It compiles; the only difference is the size of the
  two numbers, which is a cost independent of `δ`.

`coverMap_fills_bridge_binders'` is the cover map re-tied to the abstract form: the direct route
gives `Afib = A`, so the bound holds for **every** `F ≥ 1`, the source's `F₀` included.
`bridgeSourceFibreConstant` names `F₀` where the caller supplies it, as  asks.

## `hED_of_geometricSupplier_of_bridge` needs no re-tie — measured

That theorem's binders are `hsup` (the count row `θ ρ · ρ^{-2-2ζ'} ≤ #t`), `hρ0` and `hord`.
Neither `5000⁶` nor `Afib` nor any fibre constant occurs anywhere in its statement: the fibre
constant is consumed inside `defectCoveringBridge` and never reaches the sites' `hED` slot.  So
there is nothing to abstract there, and it is left exactly as existing.
-/

@[expose] public section

open Real

namespace Kakeya.ML2Core


/-- The scale test's constant that a fibre constant `F` forces: `2·F·56³`. -/
noncomputable def bridgeScaleTestConstant (F : ℝ) : ℝ := 2 * F * 56 ^ (3 : ℝ)

theorem bridgeScaleTestConstant_le_of_source :
    bridgeScaleTestConstant ((5000 : ℝ) ^ 6) ≤ 10 ^ 30 := by
  unfold bridgeScaleTestConstant
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- Layer A, abstract in the fibre constant `F` and the scale-test constant `C`. -/
theorem bridge_absorb_of_scale_test'
    {σ q θ θ₀ A A₁ ζ N F C : ℝ}
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hA : 1 ≤ A) (hA₁ : 1 ≤ A₁) (hF0 : 0 < F)
    (hlink : bridgeScaleTestConstant F ≤ C)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ) / (C * A * A₁))
    (hcount : θ * θ₀ / (2 * F * A * A₁) * (q / (56 * σ)) ^ (2 + 4 * ζ) ≤ N) :
    θ * σ ^ (-2 - 2 * ζ) ≤ N := by
  refine le_trans ?_ hcount
  set E : ℝ := 2 + 4 * ζ with hEdef
  have hE3 : E ≤ 3 := by rw [hEdef]; linarith
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA
  have hA₁0 : (0:ℝ) < A₁ := lt_of_lt_of_le one_pos hA₁
  have hσE : (0:ℝ) < σ ^ E := Real.rpow_pos_of_pos hσ0 _
  have hqE : (0:ℝ) < q ^ E := Real.rpow_pos_of_pos hq0 _
  have h56E : (0:ℝ) < (56:ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) _
  have hlhs : σ ^ (-2 - 2 * ζ) = σ ^ (2 * ζ) * (σ ^ E)⁻¹ := by
    rw [← Real.rpow_neg hσ0.le, ← Real.rpow_add hσ0]
    congr 1
    rw [hEdef]; ring
  have hrhs : (q / (56 * σ)) ^ E = q ^ E * ((56:ℝ) ^ E)⁻¹ * (σ ^ E)⁻¹ := by
    rw [Real.div_rpow hq0.le (by positivity), Real.mul_rpow (by norm_num) hσ0.le]
    field_simp
  have hq3E : q ^ (3:ℝ) ≤ q ^ E := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hE3
  have h56 : (56:ℝ) ^ E ≤ (56:ℝ) ^ (3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hE3
  have hCpos : (0:ℝ) < C := by
    have : (0:ℝ) < bridgeScaleTestConstant F := by
      unfold bridgeScaleTestConstant; positivity
    linarith
  have hden : 2 * F * A * A₁ * (56:ℝ) ^ E ≤ C * A * A₁ := by
    have h1 : 2 * F * (56:ℝ) ^ E ≤ C := by
      refine le_trans ?_ hlink
      unfold bridgeScaleTestConstant
      nlinarith [hF0, h56]
    nlinarith [mul_pos hA0 hA₁0]
  have hnum : θ * θ₀ * q ^ (3:ℝ) ≤ θ * θ₀ * q ^ E := by
    have := mul_le_mul_of_nonneg_left hq3E (mul_pos hθ0 hθ₀0).le
    linarith
  have key : θ * σ ^ (2 * ζ) ≤ θ * θ₀ / (2 * F * A * A₁) * q ^ E * ((56:ℝ) ^ E)⁻¹ := by
    have h1 : θ * σ ^ (2 * ζ) ≤ θ * θ₀ * q ^ (3:ℝ) / (C * A * A₁) := by
      have := mul_le_mul_of_nonneg_left htest hθ0.le
      calc θ * σ ^ (2 * ζ) ≤ θ * (θ₀ * q ^ (3:ℝ) / (C * A * A₁)) := this
        _ = θ * θ₀ * q ^ (3:ℝ) / (C * A * A₁) := by ring
    have h2 : θ * θ₀ * q ^ (3:ℝ) / (C * A * A₁)
        ≤ θ * θ₀ * q ^ E / (2 * F * A * A₁ * (56:ℝ) ^ E) := by
      gcongr
    calc θ * σ ^ (2 * ζ) ≤ θ * θ₀ * q ^ (3:ℝ) / (C * A * A₁) := h1
      _ ≤ θ * θ₀ * q ^ E / (2 * F * A * A₁ * (56:ℝ) ^ E) := h2
      _ = θ * θ₀ / (2 * F * A * A₁) * q ^ E * ((56:ℝ) ^ E)⁻¹ := by
          field_simp
  calc θ * σ ^ (-2 - 2 * ζ) = (θ * σ ^ (2 * ζ)) * (σ ^ E)⁻¹ := by rw [hlhs]; ring
    _ ≤ (θ * θ₀ / (2 * F * A * A₁) * q ^ E * ((56:ℝ) ^ E)⁻¹) * (σ ^ E)⁻¹ :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = θ * θ₀ / (2 * F * A * A₁) * (q / (56 * σ)) ^ E := by rw [hrhs]; ring

open scoped Classical in
theorem defectCoveringBridge'
    {ιU ιV ιM ιW : Type*}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (W : Finset ιW) (chg : ιM → ιW)
    (Afib A₁ D : ℕ) {θ θ₀ σ q A F C ρa ρm ζ : ℝ}
    -- `eq:defect-bridge-retention` (l.5496–5499) : owner `w325gen`, pair `(p,b)`
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    -- `eq:defect-bridge-cover-map` (l.5512–5515) : the canonical exact cover, level `b`
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hAfib : (Afib : ℝ) ≤ F * A)
    (hF0 : 0 < F)
    (hlink : bridgeScaleTestConstant F ≤ C)
    -- the retained sub-cover `𝕍₀ ⊆ 𝕍` (l.5541–5542)
    (hV0 : V0 ⊆ V)
    (hV0card : θ * (V.card : ℝ) ≤ (V0.card : ℝ))
    -- descendant regularity (l.5528–5530) : owner `w325gen`, pair `(m,b)`
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    -- the charging map (l.5653–5658) : `BridgeTransversePlacement` + line-ED supply these
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ W)
    (hA₁fib : ∀ w ∈ W,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    -- `eq:defect-bridge-floor` (l.5518–5521) = `eq:ml2-count-floor` (l.4478–4481), pair `(a,m)`
    (hfloor : (ρa / ρm) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ))
    -- the window location of `m` (l.5590–5622) : `ρ_a/ρ_m > δ^{1/M}/(56σ)`
    (hgrid : q / (56 * σ) ≤ ρa / ρm)
    -- the second scale test, `eq:defect-bridge-scale-tests` (l.5538–5539)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ) / (C * A * A₁))
    -- ranges
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hA1 : 1 ≤ A) :
    θ * σ ^ (-2 - 2 * ζ) ≤ (W.card : ℝ) := by
  classical
  have hA₁R : (1:ℝ) ≤ A₁ := by exact_mod_cast hA₁0
  have hA₁R0 : (0:ℝ) < A₁ := lt_of_lt_of_le one_pos hA₁R
  have hAfibR : (0:ℝ) < Afib := by exact_mod_cast hAfib0
  have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA1
  -- the counting core
  have hcore := bridge_cellCount_chain Tb U V V0 ϖ Tm anc W chg Afib A₁ D hUsub hret
    hϖmaps hϖsurj hϖfib hV0 hV0card hancmaps hDlo hDhi hchg hA₁fib hD0 hAfib0 hA₁0 hθ0 hθ₀0
  -- the count floor, transported through the grid bound
  have hqσ0 : (0:ℝ) < q / (56 * σ) := by positivity
  have hexp : (0:ℝ) ≤ 2 + 4 * ζ := by linarith
  have hgridpow : (q / (56 * σ)) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ) :=
    le_trans (Real.rpow_le_rpow hqσ0.le hgrid hexp) hfloor
  -- the constant comparison `Afib ≤ 5000⁶ A`
  have hconst : θ * θ₀ / (2 * F * A * A₁) ≤ θ * θ₀ / (2 * (Afib : ℝ) * A₁) := by
    have hd1 : (0:ℝ) < 2 * (Afib : ℝ) * A₁ := by positivity
    have hd2 : 2 * (Afib : ℝ) * A₁ ≤ 2 * F * A * A₁ := by nlinarith
    exact div_le_div_of_nonneg_left (by positivity) hd1 hd2
  have hcount : θ * θ₀ / (2 * F * A * A₁) * (q / (56 * σ)) ^ (2 + 4 * ζ)
      ≤ (W.card : ℝ) := by
    refine le_trans ?_ hcore
    refine le_trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hqσ0.le _)) ?_
    exact mul_le_mul_of_nonneg_left hgridpow (by positivity)
  exact bridge_absorb_of_scale_test' hσ0 hζ0 hζ hq0 hq1 hθ0 hθ₀0 hA1 hA₁R hF0 hlink htest hcount

open scoped Classical in
theorem defectCoveringBridge_of_abstract
    {ιU ιV ιM ιW : Type*}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (W : Finset ιW) (chg : ιM → ιW)
    (Afib A₁ D : ℕ) {θ θ₀ σ q A ρa ρm ζ : ℝ}
    -- `eq:defect-bridge-retention` (l.5496–5499) : owner `w325gen`, pair `(p,b)`
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    -- `eq:defect-bridge-cover-map` (l.5512–5515) : the canonical exact cover, level `b`
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hAfib : (Afib : ℝ) ≤ 5000 ^ 6 * A)
    -- the retained sub-cover `𝕍₀ ⊆ 𝕍` (l.5541–5542)
    (hV0 : V0 ⊆ V)
    (hV0card : θ * (V.card : ℝ) ≤ (V0.card : ℝ))
    -- descendant regularity (l.5528–5530) : owner `w325gen`, pair `(m,b)`
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    -- the charging map (l.5653–5658) : `BridgeTransversePlacement` + line-ED supply these
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ W)
    (hA₁fib : ∀ w ∈ W,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    -- `eq:defect-bridge-floor` (l.5518–5521) = `eq:ml2-count-floor` (l.4478–4481), pair `(a,m)`
    (hfloor : (ρa / ρm) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ))
    -- the window location of `m` (l.5590–5622) : `ρ_a/ρ_m > δ^{1/M}/(56σ)`
    (hgrid : q / (56 * σ) ≤ ρa / ρm)
    -- the second scale test, `eq:defect-bridge-scale-tests` (l.5538–5539)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ) / (10 ^ 30 * A * A₁))
    -- ranges
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hA1 : 1 ≤ A) :
    θ * σ ^ (-2 - 2 * ζ) ≤ (W.card : ℝ)
 :=
  defectCoveringBridge' (F := (5000 : ℝ) ^ 6) (C := (10 : ℝ) ^ 30)
    Tb U V V0 ϖ Tm anc W chg Afib A₁ D hUsub hret hϖmaps hϖsurj hϖfib hAfib (by norm_num)
    bridgeScaleTestConstant_le_of_source hV0 hV0card hancmaps hDlo hDhi hchg hA₁fib hfloor
    hgrid htest hD0 hAfib0 hA₁0 hθ0 hθ₀0 hσ0 hζ0 hζ hq0 hq1 hA1

set_option linter.unusedVariables false in
open scoped Classical in
/-- The existing bridge's statement, written once so the two proofs can be checked against it.
The hypothesis binders are named exactly as in the existing theorem — that is the point of this
`def` — so the unused-variable linter is switched off for this declaration only; binder names do
not enter the type, so the two `example`s below are unaffected. -/
def BridgeStatement.{v} : Prop :=
  ∀ {ιU ιV ιM ιW : Type v}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (W : Finset ιW) (chg : ιM → ιW)
    (Afib A₁ D : ℕ) {θ θ₀ σ q A ρa ρm ζ : ℝ}
    -- `eq:defect-bridge-retention` (l.5496–5499) : owner `w325gen`, pair `(p,b)`
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    -- `eq:defect-bridge-cover-map` (l.5512–5515) : the canonical exact cover, level `b`
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hAfib : (Afib : ℝ) ≤ 5000 ^ 6 * A)
    -- the retained sub-cover `𝕍₀ ⊆ 𝕍` (l.5541–5542)
    (hV0 : V0 ⊆ V)
    (hV0card : θ * (V.card : ℝ) ≤ (V0.card : ℝ))
    -- descendant regularity (l.5528–5530) : owner `w325gen`, pair `(m,b)`
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    -- the charging map (l.5653–5658) : `BridgeTransversePlacement` + line-ED supply these
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ W)
    (hA₁fib : ∀ w ∈ W,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    -- `eq:defect-bridge-floor` (l.5518–5521) = `eq:ml2-count-floor` (l.4478–4481), pair `(a,m)`
    (hfloor : (ρa / ρm) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ))
    -- the window location of `m` (l.5590–5622) : `ρ_a/ρ_m > δ^{1/M}/(56σ)`
    (hgrid : q / (56 * σ) ≤ ρa / ρm)
    -- the second scale test, `eq:defect-bridge-scale-tests` (l.5538–5539)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ) / (10 ^ 30 * A * A₁))
    -- ranges
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hA1 : 1 ≤ A),
    θ * σ ^ (-2 - 2 * ζ) ≤ (W.card : ℝ)

/-- **Control: the abstract sibling has EXACTLY the existing statement at `F₀ = 5000⁶`.**
Both `example`s carry the same written type; if the two theorems differed in a single binder,
one of them would fail to elaborate. -/
example : BridgeStatement.{v} := @defectCoveringBridge
example : BridgeStatement.{v} := @defectCoveringBridge_of_abstract

open scoped Classical in
/-- **Route 2, the push route**, at the NAMED `max`. -/
theorem defectCoveringBridge_pushRoute
    {ιU ιV ιM ιW : Type*}
    (Tb U : Finset ιU) (V V0 : Finset ιV) (ϖ : ιU → ιV)
    (Tm : Finset ιM) (anc : ιU → ιM) (W : Finset ιW) (chg : ιM → ιW)
    (Afib A₁ D : ℕ) {θ θ₀ σ q A ρa ρm ζ : ℝ}
    -- `eq:defect-bridge-retention` (l.5496–5499) : owner `w325gen`, pair `(p,b)`
    (hUsub : U ⊆ Tb)
    (hret : θ₀ * (Tb.card : ℝ) ≤ (U.card : ℝ))
    -- `eq:defect-bridge-cover-map` (l.5512–5515) : the canonical exact cover, level `b`
    (hϖmaps : ∀ u ∈ U, ϖ u ∈ V)
    (hϖsurj : ∀ v ∈ V, ∃ u ∈ U, ϖ u = v)
    (hϖfib : ∀ v ∈ V, (U.filter (fun u => ϖ u = v)).card ≤ Afib)
    (hAfib : (Afib : ℝ) ≤ coverFibreConstant 3 1 20 * A)
    -- the retained sub-cover `𝕍₀ ⊆ 𝕍` (l.5541–5542)
    (hV0 : V0 ⊆ V)
    (hV0card : θ * (V.card : ℝ) ≤ (V0.card : ℝ))
    -- descendant regularity (l.5528–5530) : owner `w325gen`, pair `(m,b)`
    (hancmaps : ∀ u ∈ Tb, anc u ∈ Tm)
    (hDlo : ∀ x ∈ Tm, D ≤ (Tb.filter (fun u => anc u = x)).card)
    (hDhi : ∀ x ∈ Tm, (Tb.filter (fun u => anc u = x)).card ≤ 2 * D)
    -- the charging map (l.5653–5658) : `BridgeTransversePlacement` + line-ED supply these
    (hchg : ∀ x ∈ (U.filter (fun u => ϖ u ∈ V0)).image anc, chg x ∈ W)
    (hA₁fib : ∀ w ∈ W,
      (((U.filter (fun u => ϖ u ∈ V0)).image anc).filter (fun x => chg x = w)).card ≤ A₁)
    -- `eq:defect-bridge-floor` (l.5518–5521) = `eq:ml2-count-floor` (l.4478–4481), pair `(a,m)`
    (hfloor : (ρa / ρm) ^ (2 + 4 * ζ) ≤ (Tm.card : ℝ))
    -- the window location of `m` (l.5590–5622) : `ρ_a/ρ_m > δ^{1/M}/(56σ)`
    (hgrid : q / (56 * σ) ≤ ρa / ρm)
    -- the second scale test, `eq:defect-bridge-scale-tests` (l.5538–5539)
    (htest : σ ^ (2 * ζ) ≤ θ₀ * q ^ (3 : ℝ)
      / (bridgeScaleTestConstant (coverFibreConstant 3 1 20) * A * A₁))
    -- ranges
    (hD0 : 0 < D) (hAfib0 : 0 < Afib) (hA₁0 : 0 < A₁)
    (hθ0 : 0 < θ) (hθ₀0 : 0 < θ₀)
    (hσ0 : 0 < σ) (hζ0 : 0 < ζ) (hζ : ζ ≤ 1 / 4)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hA1 : 1 ≤ A) :
    θ * σ ^ (-2 - 2 * ζ) ≤ (W.card : ℝ)
 :=
  defectCoveringBridge' (F := coverFibreConstant 3 1 20)
    (C := bridgeScaleTestConstant (coverFibreConstant 3 1 20))
    Tb U V V0 ϖ Tm anc W chg Afib A₁ D hUsub hret hϖmaps hϖsurj hϖfib hAfib
    (lt_of_lt_of_le (by norm_num) (source_le_coverFibreConstant 3 1 20)) le_rfl
    hV0 hV0card hancmaps hDlo hDhi hchg hA₁fib hfloor hgrid htest hD0 hAfib0 hA₁0 hθ0 hθ₀0
    hσ0 hζ0 hζ hq0 hq1 hA1

open scoped Classical in
/-- **The cover map, abstract in the fibre constant.**  The direct route gives `Afib = A`, so the
bound holds for **every** `F ≥ 1` — in particular for the source's `F₀ = 5000⁶` and for
`coverFibreConstant`.  This is the re-tie of `coverMap_fills_bridge_binders` requested by
 -/
theorem coverMap_fills_bridge_binders' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] [ProperSpace E]
    {δ ρ : NNReal} (hρ : 0 < ρ) (h4 : 4 * (δ : ℝ) ≤ (ρ : ℝ)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hcen : ∀ i ∈ s, (T i).IsCentred) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    {K : ℝ} {A : ℕ} (hED : Kakeya.VeryNotSticky.IsLineEssDistinctAt K A s T)
    (hK : 5 * (ρ : ℝ) ≤ K * (δ : ℝ)) {F : ℝ} (hF1 : 1 ≤ F) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E) (Afib : ℕ),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ W ∈ G, (s.filter (fun i ↦ ϖ i = W)).card ≤ Afib) ∧
      ((Afib : ℝ) ≤ F * (A : ℝ)) ∧
      (∀ i ∈ s, (T i).carrier ⊆ (ϖ i).carrier) := by
  obtain ⟨G, ϖ, hmaps, hsurj, hcov, hfib⟩ :=
    exists_coverMap_of_canonicalCentredCover hρ h4 hR₀ s T hcen hmid hED hK
  refine ⟨G, ϖ, A, hmaps, hsurj, hfib, ?_, hcov⟩
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The source's `F₀`, named where the caller supplies it. -/
noncomputable def bridgeSourceFibreConstant : ℝ := (5000 : ℝ) ^ 6

theorem bridgeSourceFibreConstant_eq : bridgeSourceFibreConstant = 5000 ^ 6 := rfl

theorem one_le_bridgeSourceFibreConstant : (1 : ℝ) ≤ bridgeSourceFibreConstant := by
  unfold bridgeSourceFibreConstant; norm_num

theorem one_le_coverFibreConstant (n : ℕ) (R₀ K : ℝ) : (1 : ℝ) ≤ coverFibreConstant n R₀ K :=
  le_trans (by norm_num) (source_le_coverFibreConstant n R₀ K)

end Kakeya.ML2Core

end
