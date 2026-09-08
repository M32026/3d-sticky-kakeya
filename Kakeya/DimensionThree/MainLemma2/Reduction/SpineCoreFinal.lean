/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreLeft
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreAssembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCardMultiplicative
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFactors
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# The final assembly of the geometric core (rows the component estimates )

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, lines 38–226 — the whole proof of Main
Lemma 2 from GWZ Lemma 9.1.  The target of the assembly is the existing
`Kakeya.ML2Assembly.GeometricCoreAt` (`Reduction/AssemblyPointwise.lean:195`).

## What is here

* **arithmetic**, `multiplicity_le_of_three_factors`: the three-factor version of
  `Kakeya.ML2Spine.multiplicity_le_of_two_factors`, multiplying fine factor, the middle
  factor (the estimate in the non-eccentric case, the estimate in the eccentric one) and coarse factor
  against product and cardinality bound.
* **the case split as an `Or`-elimination**, `middle_factor_of_cases`: the two branches deliver
  the middle factor at *different* exponents (`10 η_k/ε₂` non-eccentric,
  `10 η/ε₂ - η₀/2` eccentric) and this reads both at their common lower bound, so the estimate spends one
  `rcases` and no repackaging.
* **the scale transport of the middle factor**, `rpow_le_rpow_of_le_rpow_base`: the middle factor
  is proved at the *rescaled* thickness `δ̃ = τ/θ`, and `δ̃ ≤ δ^w` converts its gain to `δ^{w g}`.
* **The cardinality estimate needed for the product bound**, `card_three_factor_le` and
  `filter_assign_eq_of_mem`: the fine fibre `Kakeya.ML2Core.exists_twoScale_with_fine_factor`
  produces is taken inside the *node-restricted* family `{i ∈ s | assign b i ∈ t₁}`, while
  `Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` states it inside `s`; the two
  `Finset`s are **equal**, not merely comparable, and that closes the `hcard` binder the estimate left
  open.
* **the multiplicity → mass conversion**, `sum_shade_le_of_multiplicity_le`: the exact shape the
  right disjunct of `Kakeya.ML2Core.dichotomy_of_dichotomyLeft_or_gain` states.
* **wiring**, `geometricCoreAt_of_pointwise` (a definitional pin) and
  `dichotomy_of_windowGain`: branch (i) is existing
  (`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3`), so the producer of
  `GeometricCoreAt` is reduced to **one** obligation, the window branch's mass gain.
* **compatibility** lives in `Cap/CoreComposition.lean`, not here: the composition needs
  `Kakeya.ML2Cap.mainLemma2Statement_of_geometricCoreAt_free`, and `Cap/` imports `Reduction/`, so
  naming it in this module would close a cycle.

## What is *not* here, and why

the estimate (the packaging of the rescaled datum `(𝕋̃, Ỹ)` at `δ̃ = τ/θ`) and the estimate (the plank factoring
of `𝕋̃_ρ` and the eccentric/non-eccentric case split) **do not exist**: the rows dispatched under
those names delivered `Reduction/SpineDeltaMaxFloor.lean` and `Reduction/SpineEDExtraction.lean`,
which are the `Δ_max`-floor refutation and the essential-distinctness extraction, not the rescaled
datum.  Both `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` 
and `Kakeya.ML2Core.eccentric_atPlankScale`  act on that datum, so **the middle factor has
no producer** and the window branch's gain cannot be closed here.  It is therefore carried as the
single explicit hypothesis of `dichotomy_of_windowGain`, and everything else on the route is
.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ## the estimate, the arithmetic: three factors against one cardinality bound -/

/-- **The three-factor multiplicity bound**.

`Kakeya.ML2Spine.multiplicity_le_of_two_factors` multiplies two factors; GWZ's Main Lemma 2
multiplies *three* — the fine factor at scale `δ` inside a `τ`-node (GWZ 74–79), the middle factor
of `τ`-nodes inside a `θ`-node (GWZ 92–226, the row this file's siblings own) and the coarse factor
of `θ`-nodes (GWZ 81–85) — against `Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated`'s
product and `Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le`'s cardinality bound.

The middle factor's exponent `gm` is a **gain** (positive) while the outer two are losses; the
budget is the single inequality `g ≤ gm - εf - εc - κ`, with `κ` paying the product's loss
constant `L` and the cardinality constant `Cu`.  Nothing here is spine-specific: the exponents are
free reals. -/
theorem multiplicity_le_of_three_factors
    {δ : NNReal} {mu mf mm mc L Cu : ENNReal} {Nf Nm Nc N : ℕ} {β εf gm εc κ g : ℝ}
    (hδ0 : (δ : ENNReal) ≠ 0) (hδ1 : (δ : ENNReal) ≤ 1) (hβ0 : 0 ≤ β)
    (hsplit : mu ≤ L * mf * mm * mc)
    (hf : mf ≤ (δ : ENNReal) ^ (-εf) * (Nf : ENNReal) ^ β)
    (hm : mm ≤ (δ : ENNReal) ^ gm * (Nm : ENNReal) ^ β)
    (hc : mc ≤ (δ : ENNReal) ^ (-εc) * (Nc : ENNReal) ^ β)
    (hcard : (Nf : ENNReal) * (Nm : ENNReal) * (Nc : ENNReal) ≤ Cu * (N : ENNReal))
    (hL : L * Cu ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ) :
    mu ≤ (δ : ENNReal) ^ g * (N : ENNReal) ^ β := by
  have hδt : (δ : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
  have hstep1 : mf * mm * mc
      ≤ (δ : ENNReal) ^ (gm - εf - εc)
        * (((Nf : ENNReal) * (Nm : ENNReal) * (Nc : ENNReal)) ^ β) := by
    calc mf * mm * mc
        ≤ ((δ : ENNReal) ^ (-εf) * (Nf : ENNReal) ^ β)
            * ((δ : ENNReal) ^ gm * (Nm : ENNReal) ^ β)
            * ((δ : ENNReal) ^ (-εc) * (Nc : ENNReal) ^ β) := by gcongr
      _ = ((δ : ENNReal) ^ (-εf) * (δ : ENNReal) ^ gm * (δ : ENNReal) ^ (-εc))
            * ((Nf : ENNReal) ^ β * (Nm : ENNReal) ^ β * (Nc : ENNReal) ^ β) := by ring
      _ = (δ : ENNReal) ^ (gm - εf - εc)
            * (((Nf : ENNReal) * (Nm : ENNReal) * (Nc : ENNReal)) ^ β) := by
          rw [← ENNReal.rpow_add _ _ hδ0 hδt, ← ENNReal.rpow_add _ _ hδ0 hδt,
            ENNReal.mul_rpow_of_nonneg _ _ hβ0, ENNReal.mul_rpow_of_nonneg _ _ hβ0]
          ring_nf
  have hstep2 : (((Nf : ENNReal) * (Nm : ENNReal) * (Nc : ENNReal)) ^ β)
      ≤ Cu ^ β * (N : ENNReal) ^ β := by
    calc (((Nf : ENNReal) * (Nm : ENNReal) * (Nc : ENNReal)) ^ β)
        ≤ (Cu * (N : ENNReal)) ^ β := ENNReal.rpow_le_rpow hcard hβ0
      _ = Cu ^ β * (N : ENNReal) ^ β := ENNReal.mul_rpow_of_nonneg _ _ hβ0
  calc mu ≤ L * mf * mm * mc := hsplit
    _ = L * (mf * mm * mc) := by ring
    _ ≤ L * ((δ : ENNReal) ^ (gm - εf - εc) * (Cu ^ β * (N : ENNReal) ^ β)) :=
        mul_le_mul' le_rfl (hstep1.trans (mul_le_mul' le_rfl hstep2))
    _ = (L * Cu ^ β) * ((δ : ENNReal) ^ (gm - εf - εc) * (N : ENNReal) ^ β) := by ring
    _ ≤ (δ : ENNReal) ^ (-κ) * ((δ : ENNReal) ^ (gm - εf - εc) * (N : ENNReal) ^ β) := by gcongr
    _ = (δ : ENNReal) ^ (gm - εf - εc - κ) * (N : ENNReal) ^ β := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδ0 hδt]
        ring_nf
    _ ≤ (δ : ENNReal) ^ g * (N : ENNReal) ^ β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hexp) le_rfl

/-! ## The case split of the estimate, as an `Or`-elimination -/

/-- **The eccentric/non-eccentric split costs one `rcases` and nothing else.**

the estimate lands the eccentric branch at the exponent `10 η/ε₂ - η₀/2`
(`Kakeya.ML2Core.eccentric_atPlankScale`) and the estimate lands the non-eccentric branch at
`10 η_k/ε₂` (`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`).  Both are
bounds of the shape `μ ≤ δ̃^x |·|^β`, so reading them at any common lower bound `z ≤ min x y`
unifies them.  There is no repackaging and no loss: `δ̃ ≤ 1` makes `δ̃^x ≤ δ̃^z` for `z ≤ x`. -/
theorem middle_factor_of_cases {δt : NNReal} {mm : ENNReal} {Nm : ℕ} {β x y z : ℝ}
    (hδ1 : (δt : ENNReal) ≤ 1)
    (hcase : mm ≤ (δt : ENNReal) ^ x * (Nm : ENNReal) ^ β
      ∨ mm ≤ (δt : ENNReal) ^ y * (Nm : ENNReal) ^ β)
    (hx : z ≤ x) (hy : z ≤ y) :
    mm ≤ (δt : ENNReal) ^ z * (Nm : ENNReal) ^ β := by
  rcases hcase with h | h
  · exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hx) le_rfl)
  · exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hy) le_rfl)

/-- **The middle factor is proved at the rescaled thickness and consumed at the ambient one.**

`δ̃ = τ/θ` is the thickness of the rescaled family; the window gives `δ̃ ≤ δ^w` for the appropriate
window exponent `w`, and a *gain* `δ̃^{g}` at the rescaled thickness is a gain `δ^{w g}` at the
ambient one.  The direction matters: this is only sound because `g ≥ 0`, i.e. because the middle
factor is the one branch that *gains*. -/
theorem rpow_le_rpow_of_le_rpow_base {δ δt : NNReal} {w g : ℝ}
    (hg : 0 ≤ g) (hw : 0 ≤ w) (hle : δt ≤ δ ^ w) :
    (δt : ENNReal) ^ g ≤ (δ : ENNReal) ^ (w * g) := by
  have hstep : δt ^ g ≤ (δ ^ w) ^ g := NNReal.rpow_le_rpow hle hg
  have hcast : ((δt ^ g : NNReal) : ENNReal) ≤ (((δ ^ (w * g) : NNReal)) : ENNReal) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [NNReal.rpow_mul]
    exact hstep
  rwa [ENNReal.coe_rpow_of_nonneg _ hg,
    ENNReal.coe_rpow_of_nonneg _ (mul_nonneg hw hg)] at hcast

/-! ## The cardinality estimate needed for the product bound — the `hcard` binder, closed -/

section Card

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {δ : NNReal} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
  {Cu : NNReal}

open Classical in
/-- **The two fine fibres are the same `Finset`, not merely comparable.**

`Kakeya.ML2Core.exists_twoScale_with_fine_factor` takes the fine fibre inside the *node-restricted*
family `{i ∈ s | assign b i ∈ t₁}`, while
`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` states its first bracket inside
`s`.  When the node `j` is one of the retained ones (`j ∈ t₁`), a leaf assigned to `j` is
automatically node-restricted, so the two filters are **equal**.  This is what lets the estimate be used
without an adapter, and it is the whole content of the `hcard` binder the estimate carried. -/
theorem filter_assign_eq_of_mem {κ : Type*} (s : Finset ι) (f : ι → κ) (t : Finset κ)
    {j : κ} (hj : j ∈ t) :
    {i ∈ ({i ∈ s | f i ∈ t} : Finset ι) | f i = j} = {i ∈ s | f i = j} := by
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨his, _⟩, hij⟩
    exact ⟨his, hij⟩
  · rintro ⟨his, hij⟩
    exact ⟨⟨his, hij ▸ hj⟩, hij⟩

open Classical in
/-- **the estimate, cast into product.**

`Kakeya.ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le` proves the three-factor
cardinality bound in `ℝ≥0` with the fine fibre taken inside `s`; the estimate needs it in `ENNReal` with
the fine fibre taken inside the node-restricted family.  Both moves are free —
`Kakeya.ML2Core.filter_assign_eq_of_mem` for the first and a cast for the second — so **the
`hcard` binder of `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` is
discharged, not carried.**

The hypothesis `jτ ∈ t₁` is the only new one, and the estimate supplies it: `jτ` is chosen *in* the
retained set `tτ' ⊆ t₁`. -/
theorem card_three_factor_le (𝒰 : Tube.ChainUniformTubeSet s T N σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    {t₁ tτ' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover b) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ t₁) :
    ((({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i = jτ}).card : ENNReal))
        * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ}).card : ENNReal))
        * ((tθ'.card : ENNReal))
      ≤ ((Cu ^ 5 : NNReal) : ENNReal) * (s.card : ENNReal) := by
  have hmem : jτ ∈ 𝒰.cover.indexSet b :=
    ML2Reduction.activeNodes_subset 𝒰.cover b (ht₁ hjτ)
  have hW6 := ML2Reduction.card_class_mul_card_coarseFibre_mul_card_le 𝒰 hab haN hbN htτ htθ
    (jθ := jθ) hmem
  rw [filter_assign_eq_of_mem s (𝒰.cover.assign b) t₁ hjτ]
  exact_mod_cast hW6

end Card

/-! ## The multiplicity → mass conversion of the estimate -/

/-- **The mass form the right disjunct of `Kakeya.ML2Core.dichotomy_of_dichotomyLeft_or_gain`
states.**  `ShadedBody.multiplicity_le_iff` is an iff, so no hypothesis is spent and the
conversion is exact; the only work is the associativity
`(δ^g · |s|^β) · vol(⋃) = δ^g · |s|^β · vol(⋃)`. -/
theorem sum_shade_le_of_multiplicity_le' {δ : NNReal} {ι : Type*} {s : Finset ι} {c : ENNReal}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (h : ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤ c) :
    ∑ i ∈ s, volume (T i).shade ≤ c * volume (⋃ i ∈ s, (T i).shade) :=
  (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp h

/-- The same, with the bound in the exponent shape `Kakeya.ML2Assembly.Dichotomy` states. -/
theorem sum_shade_le_of_multiplicity_le {δ : NNReal} {β g : ℝ} {ι : Type*} {s : Finset ι}
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (h : ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β) :
    ∑ i ∈ s, volume (T i).shade
      ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade) :=
  (ShadedBody.multiplicity_le_iff s (fun i ↦ (T i).toShadedBody)).mp h

/-! ## the estimate: the two branches under one `filter_upwards` -/

/-- **The residue of `GeometricCoreAt` is exactly the right disjunct.**

`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` (branch (i), existing) already delivers, for a
suitable `ε₁` and at a.e. small `δ`, the alternative *`DichotomyLeft (β/2)` or the window package*.
Here the window package is a **parameter** `Q`, so this combinator never restates it: a producer
instantiates `Q` at the existing package, discharges `hleft` with the existing theorem, and owes only
`hright` — the window branch's mass gain.

That is the honest statement of what is left of the estimate: **one** implication, on **one** of the two
branches. -/
theorem dichotomy_of_left_or_Q {β ε₀ g η : ℝ}
    (Q : ∀ (δ : NNReal) (ι : Type u), Finset ι →
      (ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) → Prop)
    (hleft : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        ML2Shading.DichotomyLeft ε₀ s T ∨ Q δ ι s T)
    (hright : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        Q δ ι s T →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)) :
    ML2Assembly.Dichotomy.{u} β ε₀ g η := by
  refine dichotomy_of_dichotomyLeft_or_gain ?_
  filter_upwards [hleft, hright] with δ hl hr
  intro ι s T hball hKT hfull hcard
  exact (hl s T hball hKT hfull hcard).imp id (fun hq ↦ hr s T hq)

/-- **`GeometricCoreAt` is, definitionally, the per-exponent dichotomy statement.**

The pin `:= fun h ↦ h` is the point: nothing between a producer of the right-hand side and the
existing `Kakeya.ML2Assembly.GeometricCoreAt` needs proving, so packaging costs nothing and
any drift in the existing `def` breaks this declaration. -/
theorem geometricCoreAt_of_pointwise
    (h : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
        ML2Assembly.Dichotomy.{u} β (β / 2)
          (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) η) :
    ML2Assembly.GeometricCoreAt.{u} :=
  fun β ϖ gain dens hβ0 hβ1 hp hKT hF ↦ h β ϖ gain dens hβ0 hβ1 hp hKT hF

/-- **the estimate, assembled: the `ε₁`/`η` packaging and the positivity side conditions are free.**

`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` supplies the Katz--Tao exponent `ε₁`, the
density exponent `η 0`, the identification `η 0 = ML2Spine.spineNu β ϖ ε₁ gain dens` and its two
side conditions `0 < η 0 ≤ 1`.  This theorem spends all of that and reduces `GeometricCoreAt`'s
per-exponent obligation to the **window branch alone**: the mass gain, on the families where
branch (i) does *not* fire.

`Kakeya.ML2Spine.spineNu_pos` and `Kakeya.ML2Inputs.spineNu_le_div_48000` are not invoked directly
— the existing theorem already carries `0 < η 0` and `η 0 ≤ 1` as fields of its output, which is
where those two lemmas were spent.

The hypothesis is stated with `¬ DichotomyLeft` rather than with the window package because the
package is a forty-line existential; a producer discharges it by running
`exists_dichotomyLeft_or_window_dim3` at the same `δ` and eliminating the left disjunct, which is
exactly what `¬ DichotomyLeft` licenses.  Classically `¬L → G` is `L ∨ G`, so nothing is hidden:
what this theorem buys is the packaging, not the mathematics. -/
theorem exists_dichotomy_of_windowGain {β ϖ : ℝ} {gain dens : ℝ → ℝ}
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hg : ∀ ζ : ℝ, 0 < ζ → 0 < gain ζ) (hd : ∀ ζ : ℝ, 0 < ζ → 0 < dens ζ)
    (hright : ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
            ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
            ≥ δ ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          ¬ ML2Shading.DichotomyLeft (β / 2) s T →
          ∑ i ∈ s, volume (T i).shade
            ≤ (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
                * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ML2Assembly.Dichotomy.{u} β (β / 2)
        (4 * ML2Spine.spineNu β ϖ ε₁ gain dens) η := by
  obtain ⟨ε₁, hε₁, C, Kl, cl, ε₂, e, N, η, -, -, -, hη0nu, hη00, hη01, -, -⟩ :=
    exists_dichotomyLeft_or_window_dim3.{u} hSFE hβ0 hβ1 hϖ hg hd
  refine ⟨ε₁, hε₁, η 0, hη00, hη01, ?_⟩
  refine dichotomy_of_dichotomyLeft_or_gain ?_
  filter_upwards [hright ε₁ hε₁] with δ hr
  intro ι s T hball hKT hfull hcard
  by_cases hL : ML2Shading.DichotomyLeft (β / 2) s T
  · exact Or.inl hL
  · rw [hη0nu] at hKT hfull
    exact Or.inr (hr s T hball hKT hfull hcard hL)

/-- **The `GeometricCoreAt` producer, over the single hypothesis.**

Everything `Kakeya.ML2Assembly.GeometricCoreAt` asks for is discharged here except the window
branch's mass gain: the exponent `ε₁`, the density exponent `η`, the two side conditions, the
`Dichotomy` packaging and the branch-(i) alternative all come from
`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` and
`Kakeya.ML2Core.exists_dichotomy_of_windowGain`.

The three positivity facts `Lemma91ParamsAt` carries (`window_pos`, `gain_pos`, `dens_pos`) are
exactly what the spine construction needs, so the binder list of `GeometricCoreAt` is spent in
full and nothing extra is asked of the caller. -/
theorem geometricCoreAt_of_windowGain
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (hright : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
          IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
            ((δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens))) →
          ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
            ≥ δ ^ (ML2Spine.spineNu β ϖ ε₁ gain dens) →
          (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
          ¬ ML2Shading.DichotomyLeft (β / 2) s T →
          ∑ i ∈ s, volume (T i).shade
            ≤ (δ : ENNReal) ^ (4 * ML2Spine.spineNu β ϖ ε₁ gain dens)
                * (s.card : ENNReal) ^ β * volume (⋃ i ∈ s, (T i).shade)) :
    ML2Assembly.GeometricCoreAt.{u} := by
  refine geometricCoreAt_of_pointwise (fun β ϖ gain dens hβ0 hβ1 hp hKT hF ↦ ?_)
  exact exists_dichotomy_of_windowGain hSFE hβ0 hβ1 hp.window_pos hp.gain_pos hp.dens_pos
    (fun ε₁ hε₁ ↦ hright β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁)

/-! ## The `hret` binder: the bookkeeping half, closed -/

/-- **The shading-mass retention, reduced to a per-tube comparison and a count retention.**

`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` carries one scalar
obligation, `∑_{fib} |Y_i| ≤ Cf ∑_{s'} |Y'_i|`, and
`Kakeya.ML2Reduction.multiplicity_le_of_shade_refinement` shows it is the *only* price of the
uniformisation.  This lemma discharges the bookkeeping in it: with a ceiling `A` on the shade mass
of a member of `fib`, a floor `B` on the shade mass of a retained member of `s'`, the count
retention `|fib| ≤ K |s'|` and the per-tube comparison `A ≤ K' B`, the constant is `Cf = K K'`.

So what remains of `hret` after this lemma is exactly **two geometric inputs, both already named in
the tree**: the count retention is the `(s.card : ℝ) ≤ σ^{-α} (s'.card : ℝ)` clause of
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`, and the per-tube comparison is what
`Kakeya.ML2Shaded.HasComparableDensities` states.  No new obligation is created, and no
per-tube *carrier*-volume comparison is needed after all — the shade masses are compared
directly. -/
theorem sum_shade_le_of_comparable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {s' fib : Finset ι} {V V' : ι → ShadedBody E} {A B K K' : ENNReal}
    (hceil : ∀ i ∈ fib, volume (V i).shade ≤ A)
    (hfloor : ∀ i ∈ s', B ≤ volume (V' i).shade)
    (hcard : (fib.card : ENNReal) ≤ K * (s'.card : ENNReal))
    (hAB : A ≤ K' * B) :
    ∑ i ∈ fib, volume (V i).shade ≤ (K * K') * ∑ i ∈ s', volume (V' i).shade := by
  have hup : ∑ i ∈ fib, volume (V i).shade ≤ (fib.card : ENNReal) * A := by
    calc ∑ i ∈ fib, volume (V i).shade ≤ ∑ _i ∈ fib, A := Finset.sum_le_sum hceil
      _ = (fib.card : ENNReal) * A := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlow : (s'.card : ENNReal) * B ≤ ∑ i ∈ s', volume (V' i).shade := by
    calc (s'.card : ENNReal) * B = ∑ _i ∈ s', B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s', volume (V' i).shade := Finset.sum_le_sum hfloor
  calc ∑ i ∈ fib, volume (V i).shade ≤ (fib.card : ENNReal) * A := hup
    _ ≤ (K * (s'.card : ENNReal)) * (K' * B) := by gcongr
    _ = (K * K') * ((s'.card : ENNReal) * B) := by ring
    _ ≤ (K * K') * ∑ i ∈ s', volume (V' i).shade := by gcongr

/-! ## the estimate, assembled: the compatibility the compiler adjudicates -/

section Assembled

variable {δ : NNReal} {ι : Type u} {s : Finset ι}
  {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {Nn : ℕ} {σ : ℕ → NNReal} {Cu : NNReal}

open Classical in
/-- **the estimate.**  The three factors, product and cardinality bound, multiplied and
converted to the mass form `Kakeya.ML2Assembly.Dichotomy` states.

Every index set below is written exactly as
`Kakeya.ML2Core.exists_twoScale_with_fine_factor` produces it, and the cardinality bound is
`Kakeya.ML2Core.card_three_factor_le`, so **no adapter stands between the estimate and this row**:
any drift in their statements breaks this declaration.  That is the point of stating it, and it is
why `hprod` and `hfine` are written out rather than abstracted.

The only abstract binders are the *middle* factor `hmid` — the one GWZ proves by rescaling to
`(𝕋̃, Ỹ)` and case-splitting (`Kakeya.ML2Core.middle_factor_of_cases` reads the two branches at a
common exponent) — and the coarse factor `hcoarse`, which
`Kakeya.ML2Core.exists_coarse_factor_at_window` supplies.

The conclusion is on the **node-restricted** family `{i ∈ s | assign b i ∈ t₁}` with `|s|^β` on the
right, because that is what the estimate delivers: the cardinality loss is already paid against the whole
of `s`. -/
theorem mass_gain_of_three_factors
    (𝒰 : Tube.ChainUniformTubeSet s (fun i ↦ (V i).toTube) Nn σ Cu)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ Nn) (hbN : b ≤ Nn)
    {t₁ tτ' tθ' : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover b)
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover b) (htθ : tθ' ⊆ 𝒰.cover.indexSet a)
    {jτ jθ : ι} (hjτ : jτ ∈ t₁)
    {Yτ' : ι → ShadedTube (σ b) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (σ a) (EuclideanSpace ℝ (Fin 3))}
    {Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {L : ENNReal} {β εf gm εc κ g : ℝ}
    (hδ0 : (δ : ENNReal) ≠ 0) (hδ1 : (δ : ENNReal) ≤ 1) (hβ0 : 0 ≤ β)
    (hprod : ShadedBody.multiplicity ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i ↦ (V i).toShadedBody)
        ≤ L
          * ShadedBody.multiplicity
              ({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
          * ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
              (fun j ↦ (Yτ' j).toShadedBody)
          * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody))
    (hfine : ShadedBody.multiplicity
          ({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf)
          * ((({i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β)
    (hmid : ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gm
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover a b j = jθ}
                : Finset ι)).card : ENNReal) ^ β)
    (hcoarse : ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    (hL : L * (((Cu ^ 5 : NNReal) : ENNReal)) ^ β ≤ (δ : ENNReal) ^ (-κ))
    (hexp : g ≤ gm - εf - εc - κ) :
    ∑ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (V i).shade
      ≤ (δ : ENNReal) ^ g * (s.card : ENNReal) ^ β
        * volume (⋃ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset ι), (V i).shade) := by
  refine sum_shade_le_of_multiplicity_le' V ?_
  exact multiplicity_le_of_three_factors hδ0 hδ1 hβ0 hprod hfine hmid hcoarse
    (card_three_factor_le 𝒰 hab haN hbN ht₁ htτ htθ (jθ := jθ) hjτ) hL hexp

end Assembled

/-! ## The upstairs ED-multiplicity exponent `m`: when it is zero -/

section EdMult

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- **A pairwise essentially distinct family has ED-multiplicity `1`.**

`Kakeya.ML2Reduction.hup_of_step8`'s third clause prices the upstairs extraction by the family's
ED-multiplicity `M`, and the whole non-eccentric count chain closes iff `M ≤ ρ^{-m}` with
`m < ζ' - ζ`.  If the family step 8 is read on is *already* pairwise essentially distinct then the
fibre of `i` is `{i}` — a tube is never essentially distinct from itself, and every other member is
— so `M = 1` and **`m = 0`**: no extraction happens and no exponent is spent.

Nothing here is about tubes; it is the combinatorial content of "pairwise", stated on tubes only
because that is where it is used. -/
theorem card_notEssDistinct_le_one {ι : Type*} {t : Finset ι} {ρ : NNReal} (W : ι → Tube ρ E)
    (hED : (t : Set ι).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    {i : ι} (hi : i ∈ t) :
    (t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ 1 := by
  have hsub : t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier) ⊆ {i} := by
    intro j hj
    obtain ⟨hjt, hjnd⟩ := Finset.mem_filter.mp hj
    by_cases hji : j = i
    · simp [hji]
    · exact absurd (hED hjt hi hji) hjnd
  calc (t.filter (fun j ↦
        ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card
      ≤ ({i} : Finset ι).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton i

open Classical in
/-- **`m = 0` on an essentially distinct upstairs family.**

The ledger clause `(M : ℝ) ≤ ρ^{-m}` of `Kakeya.ML2Reduction.hup_of_step8` is satisfied at
`m = 0` with `M = 1`.  So the extraction's exponent is **not** an unavoidable cost: it is exactly
the price of *not* having essential distinctness upstairs, and it vanishes the moment the family
step 8 is read on has it.

Combined with `Kakeya.ML2Core.edSlack_of_exponents`' `m + c ≤ ζ' - ζ`, this reduces the whole
remaining count-side obligation to a single yes/no question about one family, with no arithmetic
attached.  **No positivity of `ρ` is needed** — `ρ^{-0} = 1` for every base — which is worth
recording, because every other clause of the bundle carries `0 < ρ`. -/
theorem edMult_bound_at_zero {ι : Type*} {t : Finset ι} {ρ : NNReal} (W : ι → Tube ρ E)
    (hED : (t : Set ι).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) :
    ∃ M : ℕ, (∀ i ∈ t, (t.filter (fun j ↦
        ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
      ∧ (M : ℝ) ≤ (ρ : ℝ) ^ (-(0 : ℝ)) := by
  refine ⟨1, fun i hi ↦ card_notEssDistinct_le_one W hED hi, ?_⟩
  rw [neg_zero, Real.rpow_zero]
  norm_num

end EdMult

end Kakeya.ML2Core

end
