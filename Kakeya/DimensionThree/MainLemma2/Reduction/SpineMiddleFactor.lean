/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreFinal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHupProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCoverAt

/-!
# the estimate: the middle factor, from the rescaled world back to the ambient one

Blueprint: `blueprint/src/GWZAdapted/section9.tex` lines 92–105 — the passage
"*rescale `T_θ` to `B₁`, converting `𝕋[T_θ]` to `𝕋̃` of thickness `δ̃ = τ/θ`*", and the two
displays `upperBdDeltaMaxTildeTT` and `tildeDeltaLargeDeltamax` that travel with it.

`Kakeya.ML2Core.mass_gain_of_three_factors`  consumes the middle factor as
`μ({j ∈ tτ' | coarseNode 𝒞 a b j = jθ}, Yτ') ≤ δ^{gm} |·|^β` — at the **ambient** scale `δ`.
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`  and
`Kakeya.ML2Core.eccentric_atPlankScale`  both prove it at the **rescaled** thickness `δ̃`.
This file is the bridge, and it is exact on the multiplicity: the rescaling is an affine
equivalence, and an affine equivalence multiplies every volume by one nonzero finite factor, so
every ratio of volumes — and `ShadedBody.multiplicity` is a ratio of volumes — is unchanged.

## The ledger

```
μ(fibre, Yτ')  =  μ(fibre, outerFamily … Yτ')            exact  (outerFamily_multiplicity)
               ≤  δ̃^{gm̃} · |fibre|^β                     the component estimates on the rescaled family
               ≤  δ^{w · gm̃} · |fibre|^β                  from δ̃ ≤ δ^{w}
```

**No constant is lost in the first step and no constant is lost in the third.** The only price of
the whole rescaling is the *exponent* contraction `gm̃ ↦ w · gm̃`, and `w` is the window exponent
the dividing-scales lemma already supplies (`δ̃ = τ/θ ≤ δ^{e}` on the spine, `e = 1/√N`).

## What this file does and does not close

It closes the **transport**.  It does *not* build the plank factoring of `𝕋̃_ρ`, which is the estimate;
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale` and
`Kakeya.ML2Reduction.isEccentric_or_isNonEccentric` are existing and are what the estimate must compose, and
`Kakeya.ML2Core.middle_factor_of_cases` is where their `Or` lands.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ## The fibre sits inside its coarse node, after translation -/

section Fibre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal} {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}

omit [BorelSpace E] in
open Classical in
/-- **The ancestor fibre of `jθ` lies inside the translated coarse node `Yθ jθ`.**

`Kakeya.ML2Reduction.tube_le_coarseNode` gives the containment on the hierarchy's own tubes, and
`Kakeya.ML2Core.tube_translate_le_iff` carries it across the translation that
`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated` applies to both levels at once.  So the
`hsub` binder of every rescaling lemma below is discharged by the hierarchy, with **no dilation**
and no constant — this is the estimate §6's D4 distinction, used again one level up. -/
theorem fibre_carrier_subset_coarseNode (𝒞 : Tube.ChainCoverSystem s T N σ)
    {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N) {tτ' : Finset ι}
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒞 b) {jθ : ι} (v : E)
    {Yτ' : ι → ShadedTube (σ b) E} {Yθ : ι → ShadedTube (σ a) E}
    (hYτ : ∀ j, (Yτ' j).toTube = (𝒞.tube b j).translate v)
    (hYθ : ∀ k, (Yθ k).toTube = (𝒞.tube a k).translate v) :
    ∀ j ∈ ({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ} : Finset ι),
      (Yτ' j).carrier ⊆ (Yθ jθ).toTube.carrier := by
  intro j hj
  obtain ⟨hjt, hjc⟩ := Finset.mem_filter.mp hj
  have hbase : (𝒞.tube b j).toConvexSpaceBody
      ≤ (𝒞.tube a (ML2Reduction.coarseNode 𝒞 a b j)).toConvexSpaceBody :=
    ML2Reduction.tube_le_coarseNode 𝒞 hab hbN (htτ hjt)
  rw [hjc] at hbase
  have htr : ((𝒞.tube b j).translate v).toConvexSpaceBody
      ≤ ((𝒞.tube a jθ).translate v).toConvexSpaceBody :=
    (tube_translate_le_iff (𝒞.tube b j) (𝒞.tube a jθ) v).mpr hbase
  have h1 : (Yτ' j).carrier = ((𝒞.tube b j).translate v).carrier := by rw [hYτ j]
  have h2 : (Yθ jθ).toTube.carrier = ((𝒞.tube a jθ).translate v).carrier := by rw [hYθ jθ]
  rw [h1, h2]
  exact htr

end Fibre

/-! ## The transport itself -/

/-- **the estimate.**  The middle factor, proved at the rescaled thickness `σ = δ̃`, read at the ambient
one.

Two things are worth stating plainly about the ledger.

* **The multiplicity step is an equality, not an inequality.**
  `Kakeya.ML2Reduction.outerFamily_multiplicity` is `μ(s, outerFamily …) = μ(s, 𝕋)`: the rescaling
  is an affine equivalence and the outer-tube replacement only enlarges bodies, which multiplicity
  cannot see. So the outer-tube constant `outerLoss R` — which *is* paid on `Δ_max` and on the
  fullness — is **not** paid here.
* **The exponent contracts by exactly the window width.**  `δ̃ ≤ δ^{w}` turns a gain `gm̃` at `δ̃`
  into a gain `w · gm̃` at `δ`, and that is the whole price. `0 ≤ gm̃` is load-bearing: on a *loss*
  the inequality would run the other way, which is why this lemma is stated for the middle factor
  and not reused for the two outer ones. -/
theorem middle_factor_of_rescaled
    {θ τ σ δ : NNReal} {R : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {ι : Type*} {fib : Finset ι} (Y : ι → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ j ∈ fib, (Y j).carrier ⊆ T₀.carrier)
    {Nm : ℕ} {β gm w : ℝ} (hgm : 0 ≤ gm) (hw : 0 ≤ w) (hsep : σ ≤ δ ^ w)
    (hres : ShadedBody.multiplicity fib
        (fun j ↦ (ML2Reduction.outerFamily hsit.pos_ambient T₀ hR σ Y j).toShadedBody)
      ≤ (σ : ENNReal) ^ gm * (Nm : ENNReal) ^ β) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * gm) * (Nm : ENNReal) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsub]
  exact hres.trans
    (mul_le_mul' (rpow_le_rpow_of_le_rpow_base hgm hw hsep) le_rfl)

/-- **the estimate with case split already taken.**

The two branches produce the middle factor at *different* exponents — `10 η/ε₂ - η₀/2` and `10 η_k/ε₂` — and this reads them at a common lower bound `z`
before transporting.  `0 ≤ z` is what makes the transport sound (see
`Kakeya.ML2Core.middle_factor_of_rescaled`), and it is the statement that the middle factor is a
*gain*: the whole `δ`-power of GWZ's Main Lemma 2 comes from this one factor. -/
theorem middle_factor_of_rescaled_cases
    {θ τ σ δ : NNReal} {R : ℝ} (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {ι : Type*} {fib : Finset ι} (Y : ι → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ j ∈ fib, (Y j).carrier ⊆ T₀.carrier)
    {Nm : ℕ} {β x y z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w) (hsep : σ ≤ δ ^ w)
    (hσ1 : (σ : ENNReal) ≤ 1) (hx : z ≤ x) (hy : z ≤ y)
    (hcase : ShadedBody.multiplicity fib
          (fun j ↦ (ML2Reduction.outerFamily hsit.pos_ambient T₀ hR σ Y j).toShadedBody)
        ≤ (σ : ENNReal) ^ x * (Nm : ENNReal) ^ β
      ∨ ShadedBody.multiplicity fib
          (fun j ↦ (ML2Reduction.outerFamily hsit.pos_ambient T₀ hR σ Y j).toShadedBody)
        ≤ (σ : ENNReal) ^ y * (Nm : ENNReal) ^ β) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * z) * (Nm : ENNReal) ^ β :=
  middle_factor_of_rescaled hsit hR hτσ T₀ Y hsub hz hw hsep
    (middle_factor_of_cases hσ1 hcase hx hy)

/-! ## The upstairs ED-multiplicity exponent `m`: the counting route is closed -/

/-- **REFUTATION: the trivial bound on the ED-multiplicity misses the budget by more than `2`.**

`Kakeya.ML2Reduction.hup_of_step8` prices the upstairs extraction by `M ≤ ρ^{-m}` and the chain
closes only if `m ≤ ζ' - ζ`.  The one bound available for free is `M ≤ |t₈|` — the fibre of `i`
cannot exceed the family.  But the count clause says `ρ^{-2-ζ'} ≤ |t₈|`, so the free bound forces
`m ≥ 2 + ζ'`, and `2 + ζ' ≤ ζ' - ζ` is false for every `ζ ≥ 0`.

**It misses by `2 + ζ + ζ' - ζ' = 2 + ζ`, i.e. by more than the entire reading gap.** So `m`
cannot be obtained by counting, at any `ζ`, at any scale: it needs a *geometric* input, exactly as
 concluded from the other three routes.  Together with
`Kakeya.ML2Core.edMult_bound_at_zero` — which gives `m = 0` on a pairwise essentially distinct
family — this brackets the question completely: **`m` is `0` if step 8's family is essentially
distinct and is not obtainable otherwise.** -/
theorem not_hup_budget_at_trivial_edMult {ρ : NNReal} (hρ0 : 0 < (ρ : ℝ)) (hρ1 : (ρ : ℝ) < 1)
    {ζ ζ' m : ℝ} (hζ : 0 ≤ ζ) {n : ℕ}
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (n : ℝ))
    (htriv : (n : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hbud : m ≤ ζ' - ζ) : False := by
  have hchain : (ρ : ℝ) ^ (-2 - ζ') ≤ (ρ : ℝ) ^ (-m) := hcard.trans htriv
  have hexp : -m ≤ -2 - ζ' :=
    (Real.rpow_le_rpow_left_iff_of_base_lt_one hρ0 hρ1).mp hchain
  linarith

/-! ## `hret`'s per-tube comparison, from `HasComparableDensities` -/

section Retention

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The per-tube shade comparison, division-free.**

`Kakeya.ML2Core.sum_shade_le_of_comparable` reduces the `hret` binder of
`Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover` to a count retention and
a per-tube comparison `A ≤ K' B`.  This produces the latter from
`Kakeya.ML2Shaded.HasComparableDensities`, which is one of the clauses
`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3` already delivers on the window branch.

The statement is multiplied out rather than divided: `|Y_i| · c_lo ≤ K · c_hi · |Y_j|` for any two
members of the family, where `c_lo`/`c_hi` are the two-sided volume bounds a family of tubes at one
scale enjoys (`Tube.le_volume`, `Tube.volume_le`).  **No positivity or finiteness of `c_lo` is
needed** — the inequality is proved by transitivity through `HasComparableDensities`' own product
form, and that is why no `ENNReal` division ever appears. -/
theorem shade_le_of_comparableDensities {ι : Type*} {u : Finset ι} {V : ι → ShadedBody E}
    {K : NNReal} (h : ML2Shaded.HasComparableDensities K u V)
    {clo chi : ENNReal}
    (hlo : ∀ i ∈ u, clo ≤ volume (V i).carrier)
    (hhi : ∀ i ∈ u, volume (V i).carrier ≤ chi)
    {i j : ι} (hi : i ∈ u) (hj : j ∈ u) :
    volume (V i).shade * clo ≤ (K : ENNReal) * chi * volume (V j).shade := by
  calc volume (V i).shade * clo
      ≤ volume (V i).shade * volume (V j).carrier := by gcongr; exact hlo j hj
    _ ≤ (K : ENNReal) * (volume (V j).shade * volume (V i).carrier) := h i hi j hj
    _ ≤ (K : ENNReal) * (volume (V j).shade * chi) := by gcongr; exact hhi i hi
    _ = (K : ENNReal) * chi * volume (V j).shade := by ring

/-- **`hret`, closed.**

The `hret` binder of `Kakeya.ML2Reduction.spine_multiplicity_le_nonEccentric_of_canonicalCover`
asks for `∑_{u} |Y_i| ≤ Cf ∑_{u'} |Y_j|` over a retained subfamily `u' ⊆ u`.  It follows from
exactly two things, both already produced on the window branch by
`Kakeya.ML2Core.exists_dichotomyLeft_or_window_dim3`:

* **`HasComparableDensities K u V`** — its per-pair form, through
  `Kakeya.ML2Core.shade_le_of_comparableDensities`;
* **the count retention** `|u| ≤ Kc |u'|`, which is the
  `(s.card : ℝ) ≤ σ^{-α} (s'.card : ℝ)` clause of
  `Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`.

plus the two-sided volume bounds a family of tubes at one scale always enjoys.  The constant is
read off the single inequality `Kc · K · c_hi ≤ Cf · c_lo`, and **the whole proof is
division-free**: `c_lo` is cancelled at the end by `ENNReal.mul_le_mul_right`, never divided by.

`u'.Nonempty` is load-bearing and is not decoration: on `u' = ∅` the right-hand side is `0` while
the left need not be, and the count retention `|u| ≤ Kc · 0` would already have forced `u = ∅`
only if `Kc` were finite — which the statement does not assume. -/
theorem sum_shade_retention {ι : Type*} {u u' : Finset ι} (hsub : u' ⊆ u) (hne : u'.Nonempty)
    {V : ι → ShadedBody E} {K : NNReal} (h : ML2Shaded.HasComparableDensities K u V)
    {clo chi : ENNReal} (hclo0 : clo ≠ 0) (hclotop : clo ≠ ⊤)
    (hlo : ∀ i ∈ u, clo ≤ volume (V i).carrier)
    (hhi : ∀ i ∈ u, volume (V i).carrier ≤ chi)
    {Kc Cf : ENNReal} (hcard : (u.card : ENNReal) ≤ Kc * (u'.card : ENNReal))
    (hCf : Kc * ((K : ENNReal) * chi) ≤ Cf * clo) :
    ∑ i ∈ u, volume (V i).shade ≤ Cf * ∑ j ∈ u', volume (V j).shade := by
  classical
  -- one member at a time
  have hpair : ∀ j ∈ u', (∑ i ∈ u, volume (V i).shade) * clo
      ≤ (u.card : ENNReal) * ((K : ENNReal) * chi * volume (V j).shade) := by
    intro j hj
    have hju : j ∈ u := hsub hj
    calc (∑ i ∈ u, volume (V i).shade) * clo
        = ∑ i ∈ u, volume (V i).shade * clo := by rw [Finset.sum_mul]
      _ ≤ ∑ _i ∈ u, (K : ENNReal) * chi * volume (V j).shade :=
          Finset.sum_le_sum (fun i hi ↦ shade_le_of_comparableDensities h hlo hhi hi hju)
      _ = (u.card : ENNReal) * ((K : ENNReal) * chi * volume (V j).shade) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- summed over the retained set
  have hsum : (u'.card : ENNReal) * ((∑ i ∈ u, volume (V i).shade) * clo)
      ≤ (u.card : ENNReal) * ((K : ENNReal) * chi) * ∑ j ∈ u', volume (V j).shade := by
    calc (u'.card : ENNReal) * ((∑ i ∈ u, volume (V i).shade) * clo)
        = ∑ _j ∈ u', (∑ i ∈ u, volume (V i).shade) * clo := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ u', (u.card : ENNReal) * ((K : ENNReal) * chi * volume (V j).shade) :=
          Finset.sum_le_sum hpair
      _ = (u.card : ENNReal) * ((K : ENNReal) * chi) * ∑ j ∈ u', volume (V j).shade := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ ↦ ?_)
          ring
  -- the count retention, then cancel the cardinality
  have hcard0 : (u'.card : ENNReal) ≠ 0 := by
    simpa using Finset.card_ne_zero_of_mem hne.choose_spec
  have hcardtop : (u'.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hstep : (u'.card : ENNReal) * ((∑ i ∈ u, volume (V i).shade) * clo)
      ≤ (u'.card : ENNReal) * ((Kc * ((K : ENNReal) * chi)) * ∑ j ∈ u', volume (V j).shade) := by
    refine hsum.trans ?_
    calc (u.card : ENNReal) * ((K : ENNReal) * chi) * ∑ j ∈ u', volume (V j).shade
        ≤ (Kc * (u'.card : ENNReal)) * ((K : ENNReal) * chi)
            * ∑ j ∈ u', volume (V j).shade := by gcongr
      _ = (u'.card : ENNReal) * ((Kc * ((K : ENNReal) * chi))
            * ∑ j ∈ u', volume (V j).shade) := by ring
  have hcancel : (∑ i ∈ u, volume (V i).shade) * clo
      ≤ (Kc * ((K : ENNReal) * chi)) * ∑ j ∈ u', volume (V j).shade :=
    (ENNReal.mul_le_mul_iff_right hcard0 hcardtop).mp hstep
  -- and cancel the volume floor
  refine (ENNReal.mul_le_mul_iff_left hclo0 hclotop).mp ?_
  refine hcancel.trans ?_
  calc (Kc * ((K : ENNReal) * chi)) * ∑ j ∈ u', volume (V j).shade
      ≤ (Cf * clo) * ∑ j ∈ u', volume (V j).shade := by gcongr
    _ = Cf * (∑ j ∈ u', volume (V j).shade) * clo := by ring

end Retention

/-! ## one missing datum: `IsUniformAtScale` from a chain -/

section AtScale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {δ : NNReal} {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
  {C : NNReal}

open Classical in
/-- **A chain, read at one level, is a `Tube.IsUniformAtScale`.**

the estimate — the plank factoring of `𝕋̃_ρ` and the eccentric/non-eccentric split — consumes exactly one
datum that the tree had no producer for: `Tube.IsUniformAtScale s T ρ C D` at the plank scale
`ρ = Kakeya.ML2Reduction.plankScale δ̃ ε₂`.  Both branches need it —
`Kakeya.ML2Core.eccentric_atPlankScale` takes it as `PS`, and
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale` is stated on it.

**It is a chain read at one level, with no geometry and no loss beyond one squaring of the
constant.**  Field by field:

| `IsUniformAtScale` | supplied by |
|---|---|
| `branchingN` | `𝒰.branchingN k` |
| `parent`, `parentTube` | `𝒰.cover.indexSet k`, `𝒰.cover.tube k` |
| `exists_le_rescale` | `Tube.ChainUniformTubeSet.exists_le_node` |
| `boundedOverlap` (at `D`) | `𝒰.boundedOverlap k hk` — verbatim, at `D := C` |
| `parentTube_injOn` | `𝒰.tube_injOn k hk` |
| `card_filter_le` (at `C²`) | `Tube.ChainUniformTubeSet.card_filter_le` |
| `le_mul_card_filter` (at `C²`) | `𝒰.le_card_class` on the class, then `class ⊆ filter` |

The two brackets are read at `C²` and the overlap at `C`, which is why the structure carries two
constants at all.  `1 ≤ C` is load-bearing in exactly one place — widening `C` to `C²` in the lower
bracket — and nowhere else.

**Consequence for the estimate.** With this, residue is no longer "a uniformity structure at the
plank scale" but "a *chain* on the rescaled family whose level-`k` radius is the plank scale", and
that is the same object the estimate builds one level down with
`Tube.exists_uniformTubeSet_subfamily_ssf`. -/
noncomputable def chainAtScale (𝒰 : Tube.ChainUniformTubeSet s T N σ C) {k : ℕ} (hk : k ≤ N)
    (hC : 1 ≤ C) : Tube.IsUniformAtScale s T (σ k) (C ^ 2) C where
  branchingN := 𝒰.branchingN k
  parent := 𝒰.cover.indexSet k
  parentTube := 𝒰.cover.tube k
  exists_le_rescale := fun h ↦ 𝒰.exists_le_node hk h
  boundedOverlap := fun V ↦ 𝒰.boundedOverlap k hk V
  parentTube_injOn := 𝒰.tube_injOn k hk
  card_filter_le := fun {j} hj ↦ 𝒰.card_filter_le hC hk hj
  le_mul_card_filter := fun {j} hj ↦ by
    have hclass : Tube.coverClass s (𝒰.cover.assign k) j
        ⊆ {i ∈ s | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody} := by
      intro i hi
      obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨his, ?_⟩
      have := 𝒰.cover.le_tube_assign k hk i his
      rwa [hij] at this
    have hcard : ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal)
        ≤ (({i ∈ s | (T i).toConvexSpaceBody
              ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card : NNReal) := by
      exact_mod_cast Finset.card_le_card hclass
    calc 𝒰.branchingN k ≤ C * ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal) :=
          𝒰.le_card_class k hk j hj
      _ ≤ C ^ 2 * ((Tube.coverClass s (𝒰.cover.assign k) j).card : NNReal) := by
          gcongr
          nlinarith [hC]
      _ ≤ C ^ 2 * (({i ∈ s | (T i).toConvexSpaceBody
            ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card : NNReal) := by gcongr

/-! ## The plank scale is a grid level, and that dissolves the exact-radius obstruction -/

/-- **A grid level below the plank exponent exists.**  `k = ⌊(1-ε₂) N⌋` works, and it is `≤ N`
because `1 - ε₂ ≤ 1`. -/
theorem exists_gridLevel_le_plankExponent {ε₂ : ℝ} (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1) {N : ℕ}
    (hN : 0 < N) : ∃ k ≤ N, (k : ℝ) / (N : ℝ) ≤ 1 - ε₂ := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine ⟨⌊(1 - ε₂) * (N : ℝ)⌋₊, ?_, ?_⟩
  · have h1 : ((⌊(1 - ε₂) * (N : ℝ)⌋₊ : ℕ) : ℝ) ≤ (1 - ε₂) * (N : ℝ) :=
      Nat.floor_le (by nlinarith)
    have h2 : (1 - ε₂) * (N : ℝ) ≤ (N : ℝ) := by nlinarith
    exact_mod_cast h1.trans h2
  · rw [div_le_iff₀ hN']
    exact Nat.floor_le (by nlinarith)

/-- **The plank scale is at most the grid scale of any level below the plank exponent.**

`Kakeya.ML2Core.eccentric_of_leafUnitBall` — and hence `Kakeya.ML2Core.eccentric_atPlankScale`'s
general form — takes an **arbitrary** `ρ` subject to `δ^{1-ε₂} ≤ ρ` and `16 ρ ≤ 1`.  So the parent
datum it needs is *not* required at the exact radius `Kakeya.ML2Reduction.plankScale δ ε₂`: any
grid scale `δ^{k/N}` with `k/N ≤ 1 - ε₂` will do.

**This is what dissolves the exact-radius obstruction.**  `Kakeya.ML2Core.chainAtScale` produces
`Tube.IsUniformAtScale` at the *exact* radius `σ k` of a chain, and a grid chain's radii are
`δ^{k/N}`, which never hit `δ^{1-ε₂}` on the nose; but they do not have to. -/
theorem plankScale_le_gridScale {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ} {ε₂ : ℝ}
    (hk : (k : ℝ) / (N : ℝ) ≤ 1 - ε₂) :
    ML2Reduction.plankScale δ ε₂ ≤ Tube.gridScale δ N k :=
  NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hk

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **parent datum, at a radius the eccentric branch accepts.**

Composing `Kakeya.ML2Core.exists_gridLevel_le_plankExponent`,
`Kakeya.ML2Core.plankScale_le_gridScale` and `Kakeya.ML2Core.chainAtScale`: a uniform tube set
along the grid gives, at the level `k = ⌊(1-ε₂)N⌋`, a `Tube.IsUniformAtScale` whose radius is at
least the plank scale — which is exactly the pair of hypotheses `ρ` carries in
`Kakeya.ML2Core.eccentric_of_leafUnitBall`, bar the threshold `16 ρ ≤ 1`.

**So residue is now one object and one object only: a `Tube.UniformTubeSet` on the
rescaled family `𝕋̃`.**  That is what `Tube.exists_uniformTubeSet_subfamily_ssf` builds, at a
subfamily loss, and it is the same construction the estimate runs one level down. -/
theorem exists_isUniformAtScale_ge_plankScale (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ε₂ : ℝ} (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1) (hN : 0 < N) (hC : 1 ≤ C)
    (𝒰 : Tube.UniformTubeSet s T N C) :
    ∃ ρ : NNReal, ML2Reduction.plankScale δ ε₂ ≤ ρ ∧
      Nonempty (Tube.IsUniformAtScale s T ρ (C ^ 2) C) := by
  obtain ⟨k, hkN, hk⟩ := exists_gridLevel_le_plankExponent hε₂0 hε₂1 hN
  exact ⟨Tube.gridScale δ N k, plankScale_le_gridScale hδ0 hδ1 hk,
    ⟨chainAtScale 𝒰.toChain hkN hC⟩⟩

end AtScale

/-! ## Step 8 to step 10, with `huni` bypassed -/

/-- **Step 8 ⟹ step 10, at the post-uniformisation family — and `huni`-free.**

The existing `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_step8` composes step 8 into
step 10 but still carries the **pinned** `huni` binder — uniformity on the *whole* index set with
the *unrefined* outer family — which  (a) shows is an extension, false in general, and
which no uniformiser in the tree produces.

This composition does not. It routes `Kakeya.ML2Reduction.canonicalCover_of_step8`'s output —
which is the `hcanon` binder character for character — into
`Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover`, i.e. into `Lemma91At` applied
**directly at `(s', U')`**, where the uniformity witness `huni` is the *producible* one:
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet`'s, on the subfamily it actually returns.

**So the whole count side of step 10 is now a single composition with no undischargeable binder in
it.** What remains inside is `hstep8`'s ED-multiplicity ledger `M ≤ ρ^{-m}`, and the next lemma
shows `m = 0` is admissible there. -/
theorem fine_factor_of_lemma91At_of_step8
    {β ϖ ζ ζ' m ν ηd cst : ℝ} {b δt δ' : NNReal} {R : ℝ}
    (hL : ML2Reduction.Lemma91At.{u} β ϖ ζ ν ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ)) (hδ'0 : 0 < δ') (hϖ0 : 0 ≤ ϖ)
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s s' : Finset α} (hs' : s' ⊆ s)
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc s s' 𝕋 U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s' 𝕋 U')
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hgap : ζ ≤ ζ' - m)
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ ≤ ζ' - m` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ ν * (s'.card : ENNReal) ^ β :=
  ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover' hL hζ hsit hR hδ'0 hqc0 h3qc T₀ mm
    (s := s) 𝕋 U' hcb (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ (by
      -- The cover is read at the CONTRACTED radius.  `hstep8` moved to the wide window;
      -- `hbudget` did not — `Kakeya.ML2Reduction.budget_descends` carries it down.
      have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
      have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
        lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
          Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
      obtain ⟨κ₀, t₈, W, M, hsubW, hused, hM, hMρ, hcard⟩ := hstep8 _ hmem
      exact ML2Reduction.canonicalCoverAt_of_step8_const
        (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)) hsit hR T₀ 𝕋 hc0
        (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W hsubW hused hM hMρ hcard
        (ML2Reduction.budget_descends
          (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
            (by simpa using hcntbudget ρ hρ))
          (hρ'0 := by exact_mod_cast hc0)
          (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
          (he := by linarith))))

open Classical in
/-- **An essentially distinct family enters `hstep8` at `m = 0`.**

`Kakeya.ML2Reduction.hup_of_step8`'s third and fourth clauses are the ED-multiplicity ledger
`#{j ∈ t₈ | ¬ ED (W j) (W i)} ≤ M` and `M ≤ ρ^{-m}`.  On a family that is *already* pairwise
essentially distinct the fibre of `i` is `{i}` (`Kakeya.ML2Core.card_notEssDistinct_le_one`), so
`M = 1` and the ledger is met at **`m = 0`**: `1 ≤ ρ^{-0} = 1`.

**Consequence, and it is the whole of item 1.**  Fed an essentially distinct family, the chain
`hstep8 → hup_of_step8 → canonicalCover_of_step8 → step 10` spends **nothing** of the reading gap
on the extraction, the budget clause of
`Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8` collapses to
`⌈C⌉ · spineOuterCountLoss R ≤ ρ^{-(ζ' - ζ)}` — a threshold on `ρ` whenever `ζ < ζ'`
(`Kakeya.ML2Reduction.exists_threshold_hup_budget`) — and
`Kakeya.ML2Core.not_hup_budget_at_trivial_edMult` becomes moot, because no counting is done.

**No positivity of `ρ` is needed.**  The residue is therefore not an exponent to be bounded but a
family to be exhibited: an essentially distinct `ρ b`-family inside `T₀`, all-used over `s'`, of
cardinality at least `ρ^{-2-ζ'}`. -/
theorem hstep8_of_essDistinct {b δt ρ : NNReal} {ζ' : ℝ}
    {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
    {α : Type u} {s' : Finset α} {𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3)))
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier)
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (t₈ : Finset κ₁)
      (W' : κ₁ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
      (∀ k ∈ t₈, (W' k).carrier ⊆ T₀.carrier) ∧
      (∀ k ∈ t₈, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W' k).carrier) ∧
      (∀ i ∈ t₈, (t₈.filter (fun j ↦
        ¬ _root_.IsEssentiallyDistinct (W' j).carrier (W' i).carrier)).card ≤ M) ∧
      (M : ℝ) ≤ (ρ : ℝ) ^ (-(0 : ℝ)) ∧
      (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ) := by
  refine ⟨κ₀, t, W, 1, hsubW, hused, fun i hi ↦ card_notEssDistinct_le_one W hED hi, ?_, hcard⟩
  rw [neg_zero, Real.rpow_zero]
  norm_num

/-! ## Item 2: the uniform tube set on the rescaled family, and the parent datum from it -/

section Rescaled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]

/-- **last object, built.**

`Tube.exists_uniformTubeSet_subfamily_ssf` builds a `Tube.UniformTubeSet` on **a subfamily** of any
family of `σ`-tubes in `B̄(0,1)` with a crude cardinality bound, below an explicit threshold.
Composing it with `Kakeya.ML2Core.chainAtScale` and
`Kakeya.ML2Core.exists_isUniformAtScale_ge_plankScale` gives the parent datum
`Tube.IsUniformAtScale` at a radius at least the plank scale — which is what
`Kakeya.ML2Core.eccentric_of_leafUnitBall` asks of `ρ`, and what
`Kakeya.ML2Reduction.exists_plankFactoringData_of_isUniformAtScale` is stated on.

**The pinning trap is respected and it is the point of the statement.**  The uniformity is bound to
`s'`, the subfamily the uniformiser returns — *never* to the whole family.  Passing back to the
whole family is an extension and is false in general ( (a)); the only thing that comes
back is the **count retention** `|s| ≤ σ^{-α} |s'|`, which the statement returns alongside, and
which `Kakeya.ML2Core.sum_shade_retention` converts into the multiplicity retention the middle
factor needs.

`α > 0` is the only budget spent, and it is free: it is a *choice*, and the threshold `δ₀` adapts
to it. -/
theorem exists_isUniformAtScale_on_subfamily (K₀ : ℕ) (α : ℝ) (hα : 0 < α)
    {ε₂ : ℝ} (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {σ : NNReal}, 0 < σ → σ ≤ δ₀ →
      ∀ (s : Finset ι) (T : ι → Tube σ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) →
        ∃ s' ⊆ s, (s.card : ℝ) ≤ (σ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
          ∃ ρ : NNReal, ML2Reduction.plankScale σ ε₂ ≤ ρ ∧
            Nonempty (Tube.IsUniformAtScale s' T ρ
              (Tube.uniformConst (Module.finrank ℝ E) ^ 2)
              (Tube.uniformConst (Module.finrank ℝ E))) := by
  obtain ⟨δ₁, hδ₁0, hδ₁1, huni⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf.{u} (E := E) K₀ α hα
  obtain ⟨δ₂, hδ₂0, hδ₂1, hgrid⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl K₀ 1 α hα
  refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, le_trans (min_le_left _ _) hδ₁1, ?_⟩
  intro ι σ hσ0 hσ s T hball hcard
  obtain ⟨s', hs', hret, ⟨𝒰⟩⟩ := huni hσ0 (hσ.trans (min_le_left _ _)) s T hball hcard
  have hN : 0 < Tube.ssfGridLen σ := (hgrid hσ0 (hσ.trans (min_le_right _ _))).1
  obtain ⟨ρ, hρ, hPS⟩ := exists_isUniformAtScale_ge_plankScale (T := T) (s := s')
    hσ0 (hσ.trans (le_trans (min_le_left _ _) hδ₁1)) hε₂0 hε₂1 hN
    (Tube.one_le_uniformConst _) 𝒰
  exact ⟨s', hs', hret, ρ, hρ, hPS⟩

end Rescaled

section NoEd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- **The contrapositive certificate: why the residue exists at all.**

`Kakeya.ML2Core.hstep8_of_essDistinct` says an essentially distinct family enters
`Kakeya.ML2Reduction.hup_of_step8` at `m = 0`.  This is the other end: a family with **no**
essential distinctness — no two members essentially distinct, which is what a cover with no
`essDistinct` clause may look like — cannot have its count converted **at any exponent budget**.

Under `hno` the ED-multiplicity fibre of every `i` is the whole family, so the only valid `M` is
`|t₈|`; the count clause `ρ^{-2-ζ'} ≤ |t₈|` then forces `m ≥ 2 + ζ'`, and
`Kakeya.ML2Core.not_hup_budget_at_trivial_edMult` closes it against `m ≤ ζ' - ζ` for every
`ζ ≥ 0`.

**So the residue is not an accounting slack that a better constant would absorb: it is the
statement that the hierarchy's nodes carry no essential-distinctness information, and
`Tube.UniformTubeSet.boundedOverlap`'s own docstring says pairwise essential distinctness of the
nodes "is unsatisfiable while preserving cardinality".  Either GWZ's `𝕋_ρ` carries essential
distinctness by definition — in which case the tree's `Tube.UniformTubeSet` is weaker than the
source and the uniformiser owes an `essDistinct` field — or the count cannot be carried across the
extraction at all.**  That is exactly the question has to rule, and this theorem is the
form of why it has to be specified. -/
theorem not_hup_budget_of_no_essDistinct {ρb : NNReal} {ρ : NNReal}
    (hρ0 : 0 < (ρ : ℝ)) (hρ1 : (ρ : ℝ) < 1) {ζ ζ' m : ℝ} (hζ : 0 ≤ ζ)
    {κ₀ : Type*} {t₈ : Finset κ₀} (W : κ₀ → Tube ρb E) (hne : t₈.Nonempty)
    (hno : ∀ i ∈ t₈, ∀ j ∈ t₈,
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)
    {M : ℕ} (hM : ∀ i ∈ t₈, (t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
    (hMρ : (M : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbud : m ≤ ζ' - ζ) : False := by
  obtain ⟨i, hi⟩ := hne
  have hfilter : t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier) = t₈ := by
    refine Finset.filter_true_of_mem (fun j hj ↦ hno i hi j hj)
  have hcardM : (t₈.card : ℝ) ≤ (M : ℝ) := by
    have := hM i hi
    rw [hfilter] at this
    exact_mod_cast this
  exact not_hup_budget_at_trivial_edMult hρ0 hρ1 hζ hcard (hcardM.trans hMρ) hbud

end NoEd

/-! ## The residue, isolated: the fine factor from ONE essential-distinctness clause -/

open Classical in
/-- **`hED` is the only thing left, and this is where it is spent.**

Every other input of step 10 is now a existing or new producer.  This theorem takes the
essential-distinctness clause — an essentially distinct all-used `ρ b`-family inside `T₀` with the
step-8 count, at every scale of Lemma 9.1's window — and delivers the fine factor at the
post-uniformisation family `(s', U')`, with

* `m = 0` throughout, by `Kakeya.ML2Core.hstep8_of_essDistinct`: **no exponent is spent on the
  extraction**, so `hbudget` is the bare `⌈C₃⌉ · spineOuterCountLoss R ≤ ρ^{-(ζ' - ζ)}`, a
  threshold on `ρ` for `ζ < ζ'` (`Kakeya.ML2Reduction.exists_threshold_hup_budget`);
* **no `huni`-shaped binder**, by routing through
  `Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8`.

**`hED` is stated as a plain hypothesis — no new `def … : Prop` — and its shape is
`Kakeya.ML2Reduction.hup_of_step8`'s first, second, fourth and fifth clauses at `m = 0`, with the
third replaced by the pairwise-`IsEssentiallyDistinct` it makes redundant.**  So whichever repair
is condition — an `essDistinct` field on `Tube.UniformTubeSet`, or a Section-9-local essentially
distinct cover datum — plugs in by `exact`. -/
theorem fine_factor_of_lemma91At_of_edCover
    {β ϖ ζ ζ' ν ηd cst : ℝ} {b δt δ' : NNReal} {R : ℝ}
    (hL : ML2Reduction.Lemma91At.{u} β ϖ ζ ν ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ)) (hδ'0 : 0 < δ') (hϖ0 : 0 ≤ ϖ)
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s s' : Finset α} (hs' : s' ⊆ s)
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc s s' 𝕋 U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s' 𝕋 U')
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hgap : ζ ≤ ζ')
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- as in the block above: `hbudget` with `centringCountLossConstant R ·` at the head,
    -- hence implying it; `hbudget` is retained only for text.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) :
    ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ ν * (s'.card : ENNReal) ^ β := by
  refine fine_factor_of_lemma91At_of_step8 (m := 0) (ζ' := ζ') hL hζ hsit hR hR1 hτσ hδ'0 hϖ0
    hwin4 T₀ hs' 𝕋 U' mm hqc0 h3qc hcb hct hsub hloss hmax hfull huni (by simpa using hgap)
    (fun ρ hρ ↦ ?_) (fun ρ hρ ↦ ?_) (fun ρ hρ ↦ by simpa using hcntbudget ρ hρ)
  · obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED ρ hρ
    exact hstep8_of_essDistinct (T₀ := T₀) (𝕋 := 𝕋) (s' := s') t W hEDt hsubW hused hcard
  · simpa using hbudget ρ hρ

/-! ## The supplier tie: `eventually_outerHuni_ssf`'s conjunct fills the sites' `huni` slot -/

/-- **Compiled tie.**  The folded conjunct
`Kakeya.ML2Reduction.eventually_outerHuni_ssf` produces is *the* `huni` binder of the middle-factor
sites: it is fed into the two sites of this file **by name**, so the match is checked by the
elaborator rather than asserted.

**Firing control**, run and recorded : replacing
`ShadedTube.ssfUniformConst 3` by `ssfUniformConst 4` in `h` turns both applications into
`Application type mismatch`.  So the tie is not vacuous — it pins the constant, not just the shape.

**The other four sites** (`Kakeya.ML2Core.middle_factor_of_edNodes_sharp'`,
`middle_factor_of_lineEDNodes_sharp`, `middle_factor_of_edNodes`, `middle_factor_of_edNodes_sharp`)
carry the  binder text — one md5 over the three-line block at all six sites,
`4831783341ff5494c122547ddd600c5d`, with its own firing control — so the same term fills their
slot; they are not tied here only because pinning their twenty-odd preceding implicit arguments
would add nothing the byte-identity does not already give. -/
theorem huni_supplier_tie {δ' b δt : NNReal} {ηd R qc β ϖ ζ ζ' m ν cst : ℝ}
    {α : Type u} {s s' : Finset α}
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (h : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3))) : True := by
  have _tie1 := fine_factor_of_lemma91At_of_step8
    (b := b) (δt := δt) (R := R) (qc := qc) (s := s) (β := β) (ϖ := ϖ) (ζ := ζ) (ζ' := ζ')
    (m := m) (ν := ν) (cst := cst) (huni := h)
  have _tie2 := fine_factor_of_lemma91At_of_edCover
    (b := b) (δt := δt) (R := R) (qc := qc) (s := s) (β := β) (ϖ := ϖ) (ζ := ζ) (ζ' := ζ')
    (ν := ν) (cst := cst) (huni := h)
  trivial


end Kakeya.ML2Core

end
