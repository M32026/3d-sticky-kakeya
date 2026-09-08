/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac
public import Kakeya.MultiScaleLoss
public import Kakeya.StickyKakeya
public import Kakeya.StickyKakeya.Reindex
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams

/-!
# Main Lemma 2, the spine: the dividing-scales dichotomy and its every-scale branch

The first two sentences of the blueprint's "Proof of Main Lemma~\ref{lemmain2}"
(`blueprint/src/GWZAdapted/section9.tex`):

> Apply Lemma `dividingScalesLemmaB` to `𝕋`.  If Conclusion (i) holds, then (provided we select
> `ε₂ ≤ ε₁/5`) we have that `𝕋` is `δ^{-ε₁}` Katz–Tao at every scale, and hence by Theorem
> `katzTaoAtEveryScaleImpliesMultSmall` we have `μ(𝕋,Y) ≤ δ^{-ε}`, and thus `(mugoalml2quant)`
> is satisfied.

Four things are carried here.

* **The dichotomy**, `Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow`: GWZ Lemma
  7.7(B) (`StickyKakeya.dividingScalesKatzTao`) read at the Main-Lemma-2 parameters
  `N = stepCount ε₂` and `ε_div = epsDiv N = 1/√N`, with alternative (ii) bundled into the named
  predicate `Kakeya.ML2Reduction.IsKatzTaoDividingWindow` and alternative (i) already stated at
  the accuracy `ε₂` rather than at the lemma's own `5 ε_div`.
* **The `ε₂ ≤ ε₁/5` bookkeeping**, `Kakeya.ML2Reduction.exists_threshold_katzTaoError_le` and
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale`: alternative (i) of GWZ Lemma 7.7(B)
  reads `Δ_max(𝕋_ρ) ≤ C · L(δ) · δ^{-5 ε_div}` with a *displayed* subpolynomial loss `L(δ)`
  (`StickyKakeya.totalLoss`), not a clean power.  Choosing `N = ⌈25/ε₂²⌉` makes `5 ε_div ≤ ε₂`,
  and `ε₂ ≤ ε₁/5` then leaves the four fifths `4ε₁/5` of the budget free to absorb `C · L(δ)`,
  which is what `StickyKakeya.exists_threshold_totalLoss_le` does below a threshold depending only
  on `C`, `K`, `c` and `ε₁`.  The output is the clean `δ^{-ε₁}` that GWZ Theorem 7.3(B) asks for.
* **The every-scale branch**, `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` and
  `Kakeya.ML2Reduction.exists_everyScale_goal`: GWZ Theorem 7.3(B), which this development owns as
  `StickyKakeya.StickyKatzTaoEstimate` and *proves* from sticky Kakeya 7.3(A)
  (supplied explicitly as `StickyKakeya.StickyFrostmanEstimate`) by
  `StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate`.
* **The assembly with the parameter spine**,
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_params`,
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_of_isSpine`,
  `Kakeya.ML2Reduction.exists_everyScale_exponent` and
  `Kakeya.ML2Reduction.exists_ml2_epsFree_dichotomy`.  `Kakeya.ML2Spine.IsSpine`
  (`Reduction/SpineParams.lean`) commits to its own `N` and `e = 1/√N` through `stepCount_eq`
  and `div_eq`, so the `stepCount`/`epsDiv` versions above, which fix those internally, cannot be
  applied to it; the `_params` version takes `(N, e)` from the caller, and the `_of_isSpine`
  version additionally discharges all four ladder hypotheses of GWZ Lemma 7.7(B) from the spine.
  `exists_ml2_epsFree_dichotomy` is the witness that the three pieces compose, with **both
  `ν` and `ε₁` bound before `∀ ε > 0`**.

  `StickyKakeya.dividingScalesKatzTao`'s side condition `4096 ≤ N` **is** discharged: it is the
  field `Kakeya.ML2Spine.IsSpine.four_thousand_le_stepCount`, added to `IsSpine` together with the
  tightening of `Kakeya.ML2Spine.spineEps₂` from `min … (1/2)` to `min … (1/64)` that makes it
  realizable (`⌈25/ε₂²⌉ ≥ 25 · 64² = 102400`).  Neither
  `Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_of_isSpine` nor
  `Kakeya.ML2Reduction.exists_ml2_epsFree_dichotomy` carries it as a hypothesis any more.
  `Kakeya.ML2Reduction.four_thousand_le_of_div_eq` remains, for callers that hold the exponent
  `e = 1/√N` rather than a spine; `Kakeya.ML2Spine.IsSpine.div_le_inv64` is its converse.

## `ε₀` is absolute, and that is why `|𝕋| ≥ δ^{-1}` is needed

Per Prof. Hong Wang's clarification of 2026-08-30, the published dependency chain
`ε → ε₁ → ε₂ → (N, η_i) → ν` must not make `ν` depend on `ε`.  The only place where `ε` could
leak into the chain is the accuracy at which GWZ Theorem 7.3(B) is read, so **that accuracy is a
parameter `ε₀` of `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le`, and the caller is meant
to fix it once from `β` alone** — never from its own `ε`.  Everything downstream of it (`ε₁`, and
hence `ε₂`, `N`, the ladder `η_i` and `ν`) is then a function of `β` alone.

The price is that the branch concludes `μ(𝕋, Y) ≤ δ^{-ε₀}` with `ε₀` possibly much *larger* than
the goal's `ε`.  It is `Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow` that closes the gap,
and it is the one place where the cardinality lower bound
`|𝕋| ≥ δ^{-1}` of the same clarification is spent: `|𝕋|^{β-ν} ≥ δ^{-(β-ν)}`, so
`δ^{-ε₀} ≤ δ^{-ε} |𝕋|^{β-ν}` as soon as `ε₀ ≤ ε + (β - ν)`, which a choice such as `ε₀ = β/2`
meets for every `ε > 0` once `ν ≤ β/2`.  Without the cardinality bound the branch supplies only
`μ(𝕋, Y) ≤ δ^{-ε₀} |𝕋|^{β-ν}` (`Kakeya.ML2Reduction.multiplicity_le_mul_card_rpow_of_le`), which
is the goal only when `ε₀ ≤ ε`.

## What is *not* here

The dichotomy hands back a subfamily `s' ⊆ s` carrying a *new* tube hierarchy `𝒰'`, while GWZ
Theorem 7.3(B) consumes a `ShadedTube.ShadedUniformTubeSet` — a uniform *shading* — read on the very
hierarchy the every-scale hypothesis is stated against.  Bridging the two is
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which refines the shading over the given
hierarchy without touching the index set or the nodes; that bridge, and the transport of the
resulting multiplicity bound back from `s'` to `s` across the cardinality loss
`|s| ≤ L(δ) |s'|`, belong to the assembly and are not asserted here.
`Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq` is the small piece of that bridge which is
proved here, since it is a fact about `Tube.UniformTubeSet.IsKatzTaoAtEveryScale` alone.
-/

@[expose] public section

open MeasureTheory Metric ShadedBody StickyKakeya Tube

namespace Kakeya.ML2Reduction

universe u w

variable
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The two dividing-scales parameters -/

/-- **The number of stopping steps** of GWZ Lemma 7.7(B) at accuracy `ε₂`: the blueprint's
`N = ⌈25/ε₂²⌉`, floored at the `4096` that `StickyKakeya.dividingScalesKatzTao` requires.

The floor is harmless: the only property of `N` the reduction spends is
`Kakeya.ML2Reduction.five_mul_epsDiv_stepCount_le`, which a *larger* `N` only improves. -/
noncomputable def stepCount (ε₂ : ℝ) : ℕ := max 4096 ⌈25 / ε₂ ^ 2⌉₊

/-- **The dividing exponent** `ε_div = 1/√N` that GWZ Lemma 7.7(B) is read at. -/
noncomputable def epsDiv (N : ℕ) : ℝ := 1 / Real.sqrt (N : ℝ)

theorem epsDiv_eq (N : ℕ) : epsDiv N = 1 / Real.sqrt (N : ℝ) := rfl

theorem four_thousand_le_stepCount (ε₂ : ℝ) : 4096 ≤ stepCount ε₂ := le_max_left _ _

theorem epsDiv_pos {N : ℕ} (hN : 4096 ≤ N) : 0 < epsDiv N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : (4096 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have := Real.sqrt_pos.mpr hNR
  rw [epsDiv]
  positivity

/-- **`N = ⌈25/ε₂²⌉` is exactly the choice that makes alternative (i) of GWZ Lemma 7.7(B) an
`ε₂`-statement**: its error is `δ^{-5 ε_div}`, and `5 ε_div ≤ ε₂`. -/
theorem five_mul_epsDiv_stepCount_le {ε₂ : ℝ} (hε₂ : 0 < ε₂) :
    5 * epsDiv (stepCount ε₂) ≤ ε₂ := by
  have hceil : (25 / ε₂ ^ 2 : ℝ) ≤ (⌈25 / ε₂ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hle : (⌈25 / ε₂ ^ 2⌉₊ : ℝ) ≤ (stepCount ε₂ : ℝ) := by
    have : ⌈25 / ε₂ ^ 2⌉₊ ≤ stepCount ε₂ := le_max_right _ _
    exact_mod_cast this
  have hN : (25 / ε₂ ^ 2 : ℝ) ≤ (stepCount ε₂ : ℝ) := le_trans hceil hle
  have hsq : (5 / ε₂) ^ 2 ≤ (stepCount ε₂ : ℝ) := by
    have h5 : (5 / ε₂ : ℝ) ^ 2 = 25 / ε₂ ^ 2 := by
      rw [div_pow]; norm_num
    rw [h5]; exact hN
  have hpos : (0 : ℝ) ≤ 5 / ε₂ := by positivity
  have hsqrt : (5 / ε₂ : ℝ) ≤ Real.sqrt (stepCount ε₂ : ℝ) :=
    (Real.le_sqrt hpos (by positivity)).mpr hsq
  have hsqrtpos : (0 : ℝ) < Real.sqrt (stepCount ε₂ : ℝ) := by
    have : (0 : ℝ) < 5 / ε₂ := by positivity
    linarith
  rw [epsDiv]
  rw [mul_one_div, div_le_iff₀ hsqrtpos]
  have : (5 / ε₂) * ε₂ ≤ Real.sqrt (stepCount ε₂ : ℝ) * ε₂ :=
    mul_le_mul_of_nonneg_right hsqrt hε₂.le
  calc (5 : ℝ) = (5 / ε₂) * ε₂ := by field_simp
    _ ≤ Real.sqrt (stepCount ε₂ : ℝ) * ε₂ := this
    _ = ε₂ * Real.sqrt (stepCount ε₂ : ℝ) := by ring

/-- **`4096 ≤ N` from the dividing exponent.**  `StickyKakeya.dividingScalesKatzTao`
requires `4096 ≤ N`, and a consumer that carries the exponent `e = 1/√N` rather than `N` itself
— `Kakeya.ML2Spine.IsSpine.div_eq` — reads that requirement as `e ≤ 1/64`.

This is the one hypothesis of the dichotomy that `Kakeya.ML2Spine.IsSpine` does **not** supply on
its own: its `eps₂_le_half` and `div_le` give only `e ≤ 1/10`, hence `N ≥ 100`.  A caller must
therefore know `e ≤ 1/64` (equivalently `ε₂ ≤ 5/64`) separately, which any honest instantiation
does, since `ε₂ ≤ ε₁/5` and the Katz--Tao exponent `ε₁` of Theorem 7.3(B) is small. -/
theorem four_thousand_le_of_div_eq {N : ℕ} {e : ℝ} (he : e = 1 / Real.sqrt (N : ℝ)) (hepos : 0 < e)
    (he64 : e ≤ 1 / 64) : 4096 ≤ N := by
  have hsne : Real.sqrt (N : ℝ) ≠ 0 := by
    intro h
    rw [he, h] at hepos
    simp at hepos
  have hs : 0 < Real.sqrt (N : ℝ) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsne)
  have h64 : (64 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [he] at he64
    rw [div_le_div_iff₀ hs (by norm_num)] at he64
    linarith
  have hNR : (4096 : ℝ) ≤ (N : ℝ) := by
    have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [hsq, hs]
  exact_mod_cast hNR

/-! ### The dividing window: alternative (ii) of GWZ Lemma 7.7(B), bundled -/

/-- **The dividing window** of GWZ Lemma 7.7(B), alternative (ii), as a named predicate.

The seven fields are, in order and verbatim, the seven clauses of the right disjunct of
`StickyKakeya.dividingScalesKatzTao`.  The two scales of the blueprint are `θ = ρ_a` and
`τ = ρ_b`, so `a < b` is `τ ≤ θ`, `b ≤ ssfGridLen δ` is `δ ≤ τ`, and `scale_sep` is
`τ ≤ δ^{ε_div} θ`; the blueprint's step index `j` with `1 ≤ j ≤ N` is `m + 1` here, so its
`η_{j-1}` is `η m` and its `η_j` is `η (m + 1)` and no truncated subtraction occurs.

`Cstar` is the single error the three density clauses are read at.  At the one point where the
dichotomy produces a window it is `C · L(δ)` — the uniformity constant that
`StickyKakeya.dividingScalesKatzTao` *returns* times the subpolynomial loss
`StickyKakeya.totalLoss` it carries — but the predicate does not pin it, because every consumer
absorbs it into a fixed negative power of the scale rather than reading its value.

The factor `Cstar` sits on the right of `le_window_maxDensity` rather than as a `Cstar⁻¹` on the
left, which is the same statement, and it is the weaker of the two placements the blueprint
allows; the reduction takes the weaker form because that is the form the Lean statement of GWZ
Lemma 7.7(B) delivers. -/
structure IsKatzTaoDividingWindow {ι : Type*} {δ Cst : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cst) (Cstar : ENNReal) (η : ℕ → ℝ) (εd : ℝ)
    (N a b m : ℕ) : Prop where
  /-- The step index lies below the number of stopping steps; the blueprint's `j` is `m + 1`. -/
  step_lt : m < N
  /-- `θ = ρ_a` is coarser than `τ = ρ_b`. -/
  coarse_lt_fine : a < b
  /-- Both scales lie on the grid of `δ`. -/
  fine_le_gridLen : b ≤ ssfGridLen δ
  /-- The two scales are `ε_div`-separated: `τ ≤ δ^{ε_div} θ`. -/
  scale_sep : (gridScale δ (ssfGridLen δ) b : ℝ)
    ≤ (δ : ℝ) ^ εd * (gridScale δ (ssfGridLen δ) a : ℝ)
  /-- `Δ_max(𝕋_θ) ≤ C_⋆ θ^{-η_{j-1}}`. -/
  coarse_maxDensity_le :
    Kakeya.maxDensity (𝒰.cover.indexSet a) (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal ((gridScale δ (ssfGridLen δ) a : ℝ) ^ (-η m))
  /-- `Δ_max(𝕋_{τ∣θ}[T_θ]) ≤ C_⋆ (θ/τ)^{η_{j-1}}` at every level-`θ` node. -/
  middle_maxDensity_le : ∀ j ∈ 𝒰.cover.indexSet a,
    Kakeya.maxDensity (𝒰.nodesUnder b a j) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal
          (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)
  /-- `(θ/ρ)^{η_j} ≤ C_⋆ Δ_max(𝕋_{ρ∣θ}[T_θ])` at every intermediate scale `ρ` of the window and
  every level-`θ` node. -/
  le_window_maxDensity : ∀ ρ : NNReal,
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ εd
      ≤ (ρ : ℝ) →
    (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ) / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ εd →
    ∀ j ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
            (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody)

open scoped Classical in
/-- **The dividing window with the source's own intermediate clause.**  Two fields the tree's proof
of GWZ 7.7(B) already establishes and the existing statement discards: the multiplicity-free
level-cell lower bound (refined `eqdividingKwitness`, l.2698-2703; the third non-sticky window
inequality of `lem:ml2-window-refinement`, l.4051-4053) and the two-level maximal-density
homogenization band (refined l.4032-4035, rendered at the tree's own `Cstar` rather than at the
source's factor `2`).

This is a **twin**, not two extra fields on `Kakeya.ML2Reduction.IsKatzTaoDividingWindow`: every
existing consumer keeps the parent predicate, keeps its text **and** its meaning, and reads this
through `toIsKatzTaoDividingWindow`; and `Kakeya.ML2Core.gridModel_window` -- the sticky grid family
of `Reduction/SpineCountFloorObstruction.lean`, which satisfies the parent and must **not** satisfy
this -- keeps compiling as the permanent record of why the parent cannot carry a count floor. -/
structure IsKatzTaoDividingWindowLevels {ι : Type*} {δ Cst : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cst) (Cstar : ENNReal)
    (η : ℕ → ℝ) (εd : ℝ) (N a b m : ℕ) : Prop
    extends IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m where
  /-- `(θ/ρ_c)^{η_j} ≤ C_⋆ Δ_max(𝕋_c[T_θ])` on the **distinct level-`c` cells** -- no rescaling and
  no multiplicity -- at every level `c` of the `ε_div`-inset window and every level-`θ` node.
  Refined l.2700 and l.4051-4053. -/
  le_level_maxDensity : ∀ c : ℕ,
    a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c → c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
    ∀ j ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ η (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
  /-- The **two-level maximal densities** are pinned to one profile `Φ` within the factor `Cstar`
  at **every pair of levels** and uniformly in the coarse node — the refined source's
  l.4032-4035, *"pairwise within a factor two at every fixed level or pair of levels"*.  The
  window's own coarse level `a` is the specialisation `p := a`; the genuine parent `p` of
  alternative (F) is why the general form is needed (`le_maxDensity_nodesUnder_of_band` at the pair
  `(p, c)`).  The descendant counts, the two-level counts and the fibre shaded masses of that
  sentence are still **not** carried here. -/
  level_density_band : ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ ssfGridLen δ, ∀ c ≤ ssfGridLen δ,
    ∀ j ∈ 𝒰.cover.indexSet p,
    Φ p c ≤ Kakeya.maxDensity
        ((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
      Kakeya.maxDensity
        ((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c

/-! ### (a) The dichotomy at the Main-Lemma-2 parameters -/

/-- **The dividing-scales dichotomy, specialised to the Main-Lemma-2 configuration** (blueprint
`section9.tex`, "Apply Lemma `dividingScalesLemmaB` to `𝕋`").

`StickyKakeya.dividingScalesKatzTao` read at `N = stepCount ε₂` and `ε_div = epsDiv N`, with the
two cosmetic changes the reduction wants:

* alternative (i) is stated at the accuracy `ε₂` rather than at the lemma's own `5 ε_div`, which
  is legitimate exactly because `N = ⌈25/ε₂²⌉` (`five_mul_epsDiv_stepCount_le`);
* alternative (ii) is bundled into `Kakeya.ML2Reduction.IsKatzTaoDividingWindow`.

Everything else is the lemma verbatim: the ladder hypotheses `0 ≤ η 0`,
`η k ≤ ε_div · η (k+1)` for `k < N` and `η N ≤ ε_div` are the Lean reading of the blueprint's
`η ≤ η₁ ≤ … ≤ η_N ≤ ε₂` with "each `η_j` selected very small depending on `η_{j+1}`"; the input
family is an essentially distinct, uniform family of `δ`-tubes in `B_1` with
`Δ_max(𝕋) ≤ δ^{-η 0}`; and the output is a subfamily `s' ⊆ s` retaining all but a `totalLoss`
share, carrying a new hierarchy `𝒰'` on the *same* grid `ssfGridLen δ`.

The constant `C`, the threshold `δ₀` and the two loss exponents `K`, `c` are produced before the
scale and before the family, as `StickyKakeya.dividingScalesKatzTao` produces them, so that the
absorption `Kakeya.ML2Reduction.exists_threshold_katzTaoError_le` can be performed at a threshold
that does not depend on the family. -/
theorem exists_dichotomy_katzTaoDividingWindow (hn : Module.finrank ℝ E = 3) (Cu : NNReal)
    {ε₂ : ℝ} (hε₂ : 0 < ε₂) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 →
        (∀ k < stepCount ε₂, η k ≤ epsDiv (stepCount ε₂) * η (k + 1)) →
        η (stepCount ε₂) ≤ epsDiv (stepCount ε₂) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        UniformTubeSet s T (ssfGridLen δ) Cu →
        Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
        ∃ s' ⊆ s,
          (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
          ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
            (𝒰'.IsKatzTaoAtEveryScale
                  ((C : ENNReal) * totalLoss C K c δ * ENNReal.ofReal ((δ : ℝ) ^ (-ε₂)))
              ∨ ∃ a b m : ℕ,
                  IsKatzTaoDividingWindowLevels 𝒰' ((C : ENNReal) * totalLoss C K c δ) η
                    (epsDiv (stepCount ε₂)) (stepCount ε₂) a b m) := by
  obtain ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, hmain⟩ :=
    dividingScalesKatzTao.{u} (E := E) hn (stepCount ε₂) (four_thousand_le_stepCount ε₂)
      (ε := epsDiv (stepCount ε₂)) (epsDiv_eq _) Cu
  refine ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδpos hδle η hη₀ hηstep hηN s T hball hED hunif hdens
  obtain ⟨s', hs's, hcard, 𝒰', halt⟩ :=
    hmain (ι := ι) (δ := δ) hδpos hδle η hη₀ hηstep hηN s T hball hED hunif hdens
  refine ⟨s', hs's, hcard, 𝒰', ?_⟩
  have hδ1 : δ ≤ 1 := hδle.trans hδ₀le
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  rcases halt with hevery | ⟨a, b, m, hm, hab, hbM, hsep, hcoarse, hmiddle, hlower, hlev, hband⟩
  · refine Or.inl (hevery.mono ?_)
    have hpow : (δ : ℝ) ^ (-(5 * epsDiv (stepCount ε₂))) ≤ (δ : ℝ) ^ (-ε₂) :=
      Real.rpow_le_rpow_of_exponent_ge hδR hδR1
        (by linarith [five_mul_epsDiv_stepCount_le hε₂])
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hpow) _
  · exact Or.inr ⟨a, b, m, ⟨⟨hm, hab, hbM, hsep, hcoarse, hmiddle, hlower⟩, hlev, hband⟩⟩

/-! ### (c) The `ε₂ ≤ ε₁/5` bookkeeping -/

/-- **The constant and the loss of GWZ Lemma 7.7(B) are absorbed by any fixed negative power of
the scale** (the analogue of the blueprint's "absorbing `C_⋆`").

`C · L(δ) ≤ δ^{-α}` for every `α > 0` once `δ` is small, at a threshold depending only on `α` and
on the data `C`, `K`, `c` that `StickyKakeya.dividingScalesKatzTao` returns — in particular not on
the scale and not on the family, which is what every consumer needs.

Both factors are handled at `α/2`.  The loss is subpolynomial by
`StickyKakeya.exists_threshold_totalLoss_le`; the constant is a fixed real, and is read as the
degenerate grid loss `gridLoss C 0 δ = C^{ssfGridLen δ + 1} ≥ C`, which
`StickyKakeya.exists_threshold_gridLoss_le` absorbs. -/
theorem exists_threshold_constMulTotalLoss_le (C : NNReal) (hC : 1 ≤ C) (K c : ℕ) {α : ℝ}
    (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        (C : ENNReal) * totalLoss C K c δ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) := by
  have hα2 : 0 < α / 2 := by positivity
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, h₁⟩ := exists_threshold_totalLoss_le C hC K c (α / 2) hα2
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, h₂⟩ := exists_threshold_gridLoss_le C hC 0 (α / 2) hα2
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, (min_le_left _ _).trans hδ₁le1, ?_⟩
  intro δ hδpos hδle
  have hδle₁ : δ ≤ δ₁ := hδle.trans (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := hδle.trans (min_le_right _ _)
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hL : totalLoss C K c δ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) := h₁ hδpos hδle₁
  have hCle : (C : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) := by
    have hC1 : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    have hGL : gridLoss C 0 δ = (C : ℝ) ^ (ssfGridLen δ + 1) := by
      unfold gridLoss
      rw [zero_mul, pow_zero, mul_one]
    have hCpow : (C : ℝ) ≤ (C : ℝ) ^ (ssfGridLen δ + 1) := by
      simpa using pow_le_pow_right₀ hC1 (Nat.succ_le_succ (Nat.zero_le (ssfGridLen δ)))
    have hCreal : (C : ℝ) ≤ (δ : ℝ) ^ (-(α / 2)) :=
      le_trans (hCpow.trans hGL.ge) (h₂ hδpos hδle₂)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hCreal
  calc (C : ENNReal) * totalLoss C K c δ
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) * ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2))) :=
        mul_le_mul' hCle hL
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-(α / 2)) * (δ : ℝ) ^ (-(α / 2))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)).symm
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-α)) := by
        rw [← Real.rpow_add hδR]
        ring_nf

/-- **`ε₂ ≤ ε₁/5` is exactly what makes alternative (i) of GWZ Lemma 7.7(B) a `δ^{-ε₁}`
statement** (blueprint `section9.tex`, "provided we select `ε₂ ≤ ε₁/5`").

The error alternative (i) carries is `C · L(δ) · δ^{-ε₂}`.  Of the budget `ε₁`, the fifth `ε₁/5`
pays for `δ^{-ε₂}`, since `ε₂ ≤ ε₁/5` and `δ ≤ 1`; the remaining four fifths pay for `C · L(δ)`
by `Kakeya.ML2Reduction.exists_threshold_constMulTotalLoss_le`.  No positivity of `ε₂` is used:
the comparison `δ^{-ε₂} ≤ δ^{-ε₁/5}` needs only `ε₂ ≤ ε₁/5` and `δ ≤ 1`. -/
theorem exists_threshold_katzTaoError_le (C : NNReal) (hC : 1 ≤ C) (K c : ℕ) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 < ε₁) (hε₂₁ : ε₂ ≤ ε₁ / 5) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        (C : ENNReal) * totalLoss C K c δ * ENNReal.ofReal ((δ : ℝ) ^ (-ε₂))
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, h⟩ :=
    exists_threshold_constMulTotalLoss_le C hC K c (α := 4 * ε₁ / 5) (by linarith)
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro δ hδpos hδle
  have hδ1 : δ ≤ 1 := hδle.trans hδ₀le1
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have h₂ : ENNReal.ofReal ((δ : ℝ) ^ (-ε₂)) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ε₁ / 5))) :=
    ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith))
  calc (C : ENNReal) * totalLoss C K c δ * ENNReal.ofReal ((δ : ℝ) ^ (-ε₂))
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε₁ / 5))) * ENNReal.ofReal ((δ : ℝ) ^ (-(ε₁ / 5))) :=
        mul_le_mul' (h hδpos hδle) h₂
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε₁ / 5)) * (δ : ℝ) ^ (-(ε₁ / 5))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)).symm
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)) := by
        rw [← Real.rpow_add hδR]
        ring_nf

/-! ### (a) + (c): the dichotomy with alternative (i) already at `δ^{-ε₁}` -/

/-- **The dichotomy in the form Main Lemma 2 consumes it** (blueprint `section9.tex`:
"Apply Lemma `dividingScalesLemmaB` to `𝕋`.  If Conclusion (i) holds, then (provided we select
`ε₂ ≤ ε₁/5`) we have that `𝕋` is `δ^{-ε₁}` Katz–Tao at every scale").

`Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow` with the loss of alternative (i)
absorbed by `Kakeya.ML2Reduction.exists_threshold_katzTaoError_le`.  The left disjunct is now the
clean hypothesis of GWZ Theorem 7.3(B) at the exponent `ε₁` that theorem itself returned, and the
right disjunct is unchanged.

`ε₁` is the every-scale exponent that GWZ Theorem 7.3(B) produces — in this development,
the `ε₁` of `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le`, read at an **absolute**
accuracy `ε₀`; see the module docstring.  `ε₂` is then chosen from `ε₁` (and from Lemma 9.1's own
`ϖ(β)`, which does not enter here), and `N = stepCount ε₂` from `ε₂`.  Nothing in the chain sees
the outer `ε` of the Main Lemma 2 goal. -/
theorem exists_dichotomy_katzTaoAtEveryScale (hn : Module.finrank ℝ E = 3) (Cu : NNReal)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε₂₁ : ε₂ ≤ ε₁ / 5) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 →
        (∀ k < stepCount ε₂, η k ≤ epsDiv (stepCount ε₂) * η (k + 1)) →
        η (stepCount ε₂) ≤ epsDiv (stepCount ε₂) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        UniformTubeSet s T (ssfGridLen δ) Cu →
        Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
        ∃ s' ⊆ s,
          (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
          ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
            (𝒰'.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
              ∨ ∃ a b m : ℕ,
                  IsKatzTaoDividingWindow 𝒰' ((C : ENNReal) * totalLoss C K c δ) η
                    (epsDiv (stepCount ε₂)) (stepCount ε₂) a b m) := by
  obtain ⟨C, δ₁, K, c, hC, hδ₁pos, hδ₁le, hmain⟩ :=
    exists_dichotomy_katzTaoDividingWindow.{u} (E := E) hn Cu hε₂
  obtain ⟨δ₂, hδ₂pos, hδ₂le, habs⟩ := exists_threshold_katzTaoError_le C hC K c hε₁ hε₂₁
  refine ⟨C, min δ₁ δ₂, K, c, hC, lt_min hδ₁pos hδ₂pos, (min_le_left _ _).trans hδ₁le, ?_⟩
  intro ι δ hδpos hδle η hη₀ hηstep hηN s T hball hED hunif hdens
  obtain ⟨s', hs's, hcard, 𝒰', halt⟩ :=
    hmain (ι := ι) (δ := δ) hδpos (hδle.trans (min_le_left _ _)) η hη₀ hηstep hηN s T
      hball hED hunif hdens
  refine ⟨s', hs's, hcard, 𝒰', ?_⟩
  rcases halt with hevery | ⟨a, b, m, hwindow⟩
  · exact Or.inl (hevery.mono (habs hδpos (hδle.trans (min_le_right _ _))))
  · exact Or.inr ⟨a, b, m, hwindow.toIsKatzTaoDividingWindow⟩

/-! ### (a) + (c) at externally supplied parameters `(N, e)` -/

/-- **The dichotomy at parameters chosen outside this file.**

`Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale` fixes the pair
`(N, ε_div) = (stepCount ε₂, epsDiv (stepCount ε₂))` internally, so a consumer that has already
committed to its own `N` — as `Kakeya.ML2Spine.IsSpine` does, through `stepCount_eq` and
`div_eq` — cannot use it without first proving `N = stepCount ε₂`, which is false as soon as
`⌈25/ε₂²⌉ < 4096`.  This is the same statement with `N` and `e = 1/√N` handed in.

The three hypotheses are exactly what `Kakeya.ML2Spine.IsSpine` carries: `hN` is the
`4096 ≤ N` of `StickyKakeya.dividingScalesKatzTao` (see
`Kakeya.ML2Reduction.four_thousand_le_of_div_eq`), `he` is `IsSpine.div_eq`, and `hdiv` is
`IsSpine.div_le_everyScale`.  In particular the intermediate `ε₂` has disappeared: the only role
it played was to bound `5 e ≤ ε₂ ≤ ε₁/5`, i.e. `e ≤ ε₁/25`. -/
theorem exists_dichotomy_katzTaoAtEveryScale_params (hn : Module.finrank ℝ E = 3) (Cu : NNReal)
    (N : ℕ) (hN : 4096 ≤ N) {e ε₁ : ℝ} (he : e = 1 / Real.sqrt (N : ℝ)) (hε₁ : 0 < ε₁)
    (hdiv : e ≤ ε₁ / 25) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 → (∀ k < N, η k ≤ e * η (k + 1)) → η N ≤ e →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        UniformTubeSet s T (ssfGridLen δ) Cu →
        Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
        ∃ s' ⊆ s,
          (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
          ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
            (𝒰'.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
              ∨ ∃ a b m : ℕ,
                  IsKatzTaoDividingWindowLevels 𝒰' ((C : ENNReal) * totalLoss C K c δ)
                    η e N a b m) := by
  obtain ⟨C, δ₁, K, c, hC, hδ₁pos, hδ₁le, hmain⟩ :=
    dividingScalesKatzTao.{u} (E := E) hn N hN he Cu
  obtain ⟨δ₂, hδ₂pos, hδ₂le, habs⟩ :=
    exists_threshold_katzTaoError_le C hC K c (ε₂ := 5 * e) hε₁ (by linarith)
  refine ⟨C, min δ₁ δ₂, K, c, hC, lt_min hδ₁pos hδ₂pos, (min_le_left _ _).trans hδ₁le, ?_⟩
  intro ι δ hδpos hδle η hη₀ hηstep hηN s T hball hED hunif hdens
  obtain ⟨s', hs's, hcard, 𝒰', halt⟩ :=
    hmain (ι := ι) (δ := δ) hδpos (hδle.trans (min_le_left _ _)) η hη₀ hηstep hηN s T
      hball hED hunif hdens
  refine ⟨s', hs's, hcard, 𝒰', ?_⟩
  rcases halt with hevery | ⟨a, b, m, hm, hab, hbM, hsep, hcoarse, hmiddle, hlower, hlev, hband⟩
  · exact Or.inl (hevery.mono (habs hδpos (hδle.trans (min_le_right _ _))))
  · exact Or.inr ⟨a, b, m, ⟨⟨hm, hab, hbM, hsep, hcoarse, hmiddle, hlower⟩, hlev, hband⟩⟩

/-! ### (b) The every-scale branch: GWZ Theorem 7.3(B) at an absolute accuracy -/

omit [Nontrivial E] in
/-- `δ^x` computed in `ℝ` and pushed into `ENNReal` is `δ^x` computed in `ENNReal`. -/
theorem ofReal_rpow_coe {δ : NNReal} (hδ : 0 < δ) (x : ℝ) :
    ENNReal.ofReal ((δ : ℝ) ^ x) = (δ : ENNReal) ^ x := by
  rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_rpow_of_ne_zero hδ.ne']

/-- **The every-scale branch of Main Lemma 2** (blueprint `section9.tex`: "hence by Theorem
`katzTaoAtEveryScaleImpliesMultSmall` we have `μ(𝕋,Y) ≤ δ^{-ε}`").

GWZ Theorem 7.3(B), which this development owns as `StickyKakeya.StickyKatzTaoEstimate` and
*derives* from sticky Kakeya 7.3(A), supplied explicitly as a
`StickyKakeya.StickyFrostmanEstimate` hypothesis, by
`StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate`.  Nothing is assumed here beyond
that explicit input.

**`ε₀` is the absolute accuracy, and it is the only place `ε` could have leaked in.**  Per Prof.
Hong Wang's clarification, the chain `ε → ε₁ → ε₂ → (N, η_i) → ν` must be broken at its first
link, because `ν` may not depend on `ε`.  `ε₀` is therefore a parameter of *this* lemma, fixed by
the caller once and for all from `β` alone (`ε₀ = β/2` is the intended choice), and the exponent
`ε₁` it returns — the `η` of GWZ Theorem 7.3(B) — depends on `ε₀` alone.  Everything the reduction
builds from `ε₁` is then `ε`-free.  A caller that passed its own `ε` here would reintroduce the
published typo.

The hypotheses are read at a level `η ≤ ε₁` rather than at `ε₁` itself, since that is how the
reduction has them: `Δ_max(𝕋) ≤ δ^{-η}` and `λ(𝕋, Y) ≥ δ^η` are the standing hypotheses of Main
Lemma 2 at the small level `η`, while the every-scale bound is at `ε₁` exactly, being what
`Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale` delivers.  Both weaken to level `ε₁`
because `δ ≤ 1`.

The uniformity constant `C` of the shaded structure is quantified after the threshold and is
arbitrary: `StickyKakeya.StickyKatzTaoEstimate` quantifies it inside, so no absolute constant has
to be pinned here.  The grid the shaded structure lives on is `Tube.ssfGridLen δ`, the one
`StickyKakeya.dividingScalesKatzTao` also uses, so the two interfaces agree on the grid. -/
theorem exists_everyScale_multiplicity_le (hdim : Module.finrank ℝ E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{u, u} (E := E))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε₁ δ₁ : ℝ, 0 < ε₁ ∧ 0 < δ₁ ∧ δ₁ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₁ →
      ∀ {ι : Type w} {η : ℝ}, η ≤ ε₁ →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∀ {C : NNReal} (𝒱 : ShadedTube.ShadedUniformTubeSet s V (ssfGridLen δ) C),
          ENNReal.ofReal ((δ : ℝ) ^ η)
              ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
          Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η)) →
          𝒱.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁))) →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε₀)) := by
  obtain ⟨ε₁, δ₀, hε₁, hδ₀, hmain⟩ :=
    stickyKatzTaoEstimate_apply.{w, _} (E := E)
      (stickyKatzTaoEstimate_of_stickyFrostmanEstimate hSFE) ε₀ hε₀
  refine ⟨ε₁, min δ₀ 1, hε₁, lt_min hδ₀ one_pos, min_le_right _ _, ?_⟩
  intro δ hδpos hδle ι η hηε₁ s V hball C 𝒱 hfull hdens hevery
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδR1 : (δ : ℝ) ≤ 1 := hδle.trans (min_le_right _ _)
  refine hmain hδpos (hδle.trans (min_le_left _ _)) s V hball 𝒱 ?_ ?_ hevery
  · exact le_trans
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδR hδR1 hηε₁)) hfull
  · exact hdens.trans
      (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)))

/-- **The every-scale branch, with its exponent packaged as a function of the accuracy.**

`Kakeya.ML2Spine.exists_ml2SpineParams` consumes Theorem 7.3(B) as a *map*
`E : ℝ → ℝ` from accuracy to Katz--Tao exponent, together with `∀ a, 0 < a → 0 < E a`, and
applies it at `Kakeya.ML2Spine.absAccuracy β = β/2`.  What
`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` delivers is an existential, one accuracy
at a time.  This is the same content with the choice made once and for all, so that the spine
builder can be instantiated directly:

```
obtain ⟨Eexp, hEpos, hEspec⟩ := exists_everyScale_exponent (E := E) hdim
obtain ⟨ν, hν, hνβ, hspine⟩ :=
  Kakeya.ML2Spine.exists_ml2SpineParams hβ hβ1 hϖ hgain hdens (E := Eexp) hEpos
```

after which `hspine ε hε` supplies an `IsSpine β ϖ (Eexp (absAccuracy β)) gain dens ε₂ e N η`
whose `ε₁` is exactly the exponent `hEspec (absAccuracy_pos hβ)` speaks about, and
`Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_of_isSpine` closes the loop.  There is
no `ε` anywhere in the construction of `Eexp`, so `ν` is `ε`-free, which is the whole point. -/
theorem exists_everyScale_exponent (hdim : Module.finrank ℝ E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{u, u} (E := E)) :
    ∃ Eexp : ℝ → ℝ, (∀ a : ℝ, 0 < a → 0 < Eexp a) ∧
      ∀ {ε₀ : ℝ}, 0 < ε₀ →
        ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 ∧
          ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₁ →
          ∀ {ι : Type w} {η : ℝ}, η ≤ Eexp ε₀ →
          ∀ (s : Finset ι) (V : ι → ShadedTube δ E),
            (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
            ∀ {C : NNReal} (𝒱 : ShadedTube.ShadedUniformTubeSet s V (ssfGridLen δ) C),
              ENNReal.ofReal ((δ : ℝ) ^ η)
                  ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
              Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
                  ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η)) →
              𝒱.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-(Eexp ε₀)))) →
              ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
                ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε₀)) := by
  classical
  refine ⟨fun a => if h : 0 < a then
      (exists_everyScale_multiplicity_le.{u, w} (E := E) hdim hSFE h).choose else 1, ?_, ?_⟩
  · intro a ha
    obtain ⟨δ₁, h1, -, -, -⟩ :=
      (exists_everyScale_multiplicity_le.{u, w} (E := E) hdim hSFE ha).choose_spec
    simpa only [dif_pos ha] using h1
  · intro ε₀ hε₀
    obtain ⟨δ₁, -, h2, h3, hmain⟩ :=
      (exists_everyScale_multiplicity_le.{u, w} (E := E) hdim hSFE hε₀).choose_spec
    refine ⟨δ₁, h2, h3, ?_⟩
    simp only [dif_pos hε₀]
    exact hmain

/-! ### The hierarchy bridge: transporting the every-scale bound along equal covers -/

omit [Nontrivial E] in
/-- **`Tube.UniformTubeSet.IsKatzTaoAtEveryScale` only sees the cover.**

The dichotomy hands back a *tube* hierarchy `𝒰'` carrying
`𝒰'.IsKatzTaoAtEveryScale (δ^{-ε₁})`, while `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le`
consumes the same property on the `tubeUniform` field of a
`ShadedTube.ShadedUniformTubeSet`.  The bridge between the two is
`ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet`, which refines the *shading* over the
given hierarchy and returns the equalities
`𝒱.tubeUniform.cover.indexSet = 𝒰.cover.indexSet` and
`𝒱.tubeUniform.cover.tube = 𝒰.cover.tube`.

This lemma is the piece of that bridge which is a fact about `IsKatzTaoAtEveryScale` alone: the
predicate mentions only `cover.indexSet` and `cover.tube`, neither of whose types mentions the
underlying family or the uniformity constant, so those two equalities transport it verbatim.
Everything else in the bridge — the fullness loss `(clamp+1)^{2N+2}` and the transport of the
final multiplicity bound from `s'` back to `s` across `|s| ≤ L(δ) |s'|` — is assembly work and is
not asserted here. -/
theorem isKatzTaoAtEveryScale_of_cover_eq {ι : Type*} {δ : NNReal} {s : Finset ι}
    {T T' : ι → Tube δ E} {N : ℕ} {C C' : NNReal}
    {𝒰 : UniformTubeSet s T N C} {𝒰' : UniformTubeSet s T' N C'}
    (hidx : 𝒰'.cover.indexSet = 𝒰.cover.indexSet)
    (htube : 𝒰'.cover.tube = 𝒰.cover.tube) {A : ENNReal}
    (h : 𝒰.IsKatzTaoAtEveryScale A) : 𝒰'.IsKatzTaoAtEveryScale A := by
  intro k hk
  rw [hidx, htube]
  exact h k hk

/-! ### From `μ ≤ δ^{-ε₀}` to the Main Lemma 2 goal `μ ≤ δ^{-ε} |𝕋|^{β-ν}` -/

omit [Nontrivial E] in
/-- **A multiplicity bound survives an extra nonnegative power of the cardinality.**

`μ(𝕋, Y) ≤ A` gives `μ(𝕋, Y) ≤ A |𝕋|^b` for every `b ≥ 0`, because a nonempty index set has
`|𝕋| ≥ 1`.  This is the whole of the passage from the every-scale branch to the Main Lemma 2 goal
*when the accuracy at which GWZ Theorem 7.3(B) was read is already below the goal's `ε`* — which
is exactly the case Prof. Hong Wang's clarification rules out, since it forces the accuracy, and
with it `ν`, to depend on `ε`.  For the absolute-accuracy reading use
`Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow` instead.

`hne` is carried rather than dropped: at `s = ∅` the multiplicity is `0/0 = 0` in `ENNReal` and
the inequality holds by a junk-value coincidence rather than by the argument. -/
theorem multiplicity_le_mul_card_rpow_of_le {ι : Type*} {s : Finset ι} {V : ι → ShadedBody E}
    (hne : s.Nonempty) {A : ENNReal} (hA : ShadedBody.multiplicity s V ≤ A) {b : ℝ}
    (hb : 0 ≤ b) :
    ShadedBody.multiplicity s V ≤ A * (s.card : ENNReal) ^ b := by
  calc
    ShadedBody.multiplicity s V
        ≤ ShadedBody.multiplicity s V * (s.card : ENNReal) ^ b := by
      refine le_mul_of_one_le_right' ?_
      rcases hb.lt_or_eq with hb_pos | hb_eq
      · exact ENNReal.one_le_rpow (by exact_mod_cast (Finset.one_le_card.mpr hne)) hb_pos
      · rw [← hb_eq, ENNReal.rpow_zero]
    _ ≤ A * (s.card : ENNReal) ^ b := by gcongr

/-- **The absolute accuracy `ε₀` is paid for by the cardinality** (Prof. Hong Wang's
`|𝕋| > δ^{-1}`).

`δ^{-ε₀} ≤ δ^{-ε} n^b` whenever `n ≥ δ^{-1}`, `b ≥ 0` and `ε₀ ≤ ε + b`.  With `b = β - ν` and
`n = |𝕋|` this is precisely the step that turns the every-scale conclusion
`μ(𝕋, Y) ≤ δ^{-ε₀}` — with `ε₀` fixed in advance from `β` alone, hence *larger* than the goal's
`ε` in general — into the Main Lemma 2 goal `μ(𝕋, Y) ≤ δ^{-ε} |𝕋|^{β-ν}`.

The three hypotheses are exactly the three ingredients of the clarification: `0 ≤ b` is
`ν ≤ β`, `hn` is `|𝕋| ≥ δ^{-1}`, and `hε₀` is the constraint on the absolute accuracy, met for
every `ε > 0` by e.g. `ε₀ = β/2` together with `ν ≤ β/2`.  Without `hn` the statement is false
for small `ε`: at `n = 1` the right-hand side is `δ^{-ε}` and the left-hand side `δ^{-ε₀}`, which
exceeds it as soon as `ε < ε₀`. -/
theorem ofReal_rpow_neg_le_mul_card_rpow {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ}
    (hn : (δ : ℝ)⁻¹ ≤ (n : ℝ)) {ε ε₀ b : ℝ} (hb : 0 ≤ b) (hε₀ : ε₀ ≤ ε + b) :
    ENNReal.ofReal ((δ : ℝ) ^ (-ε₀)) ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ b := by
  have hδ0 : (δ : ENNReal) ≠ 0 := by
    simpa using hδ.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hNN : δ⁻¹ ≤ (n : NNReal) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hn
  have hinv : (δ : ENNReal)⁻¹ ≤ (n : ENNReal) := by
    rw [← ENNReal.coe_inv hδ.ne']
    exact_mod_cast hNN
  have h1 : (δ : ENNReal) ^ (-b) ≤ (n : ENNReal) ^ b := by
    rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow]
    exact ENNReal.rpow_le_rpow hinv hb
  calc ENNReal.ofReal ((δ : ℝ) ^ (-ε₀)) = (δ : ENNReal) ^ (-ε₀) := ofReal_rpow_coe hδ _
    _ ≤ (δ : ENNReal) ^ (-(ε + b)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
    _ = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-b) := by
        rw [← ENNReal.rpow_add _ _ hδ0 hδtop]
        ring_nf
    _ ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ b := by gcongr

/-- **The every-scale branch, delivered in the shape of the Main Lemma 2 goal.**

`Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` read at the absolute accuracy
`Kakeya.ML2Spine.absAccuracy β = β/2`, with its conclusion `μ(𝕋, Y) ≤ δ^{-β/2}` converted by
`Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow` into the goal
`μ(𝕋, Y) ≤ δ^{-ε} |𝕋|^{β-ν}` of Main Lemma 2 — for **every** `ε > 0` at once, at the price of the
cardinality hypothesis `|𝕋| ≥ δ^{-1}` of Prof. Hong Wang's clarification (`hcard`).

`ν` enters only through `2 ν ≤ β`, which is what `Kakeya.ML2Spine.exists_ml2SpineParams` returns
alongside `ν`; `ε` is quantified *last*, inside everything else, which is the formal statement
that nothing in the branch depends on it.  In particular the exponent `ε₁` this returns — the
`η` of GWZ Theorem 7.3(B) — is a function of `β` alone, as it must be.

The hypothesis `η ≤ ε₁` is the level at which the reduction actually holds the two standing
bounds of Main Lemma 2 (`λ(𝕋,Y) ≥ δ^η` and `Δ_max(𝕋) ≤ δ^{-η}`); it is *not* an equality, so the
loss the shading bridge charges to the fullness can be paid inside it. -/
theorem exists_everyScale_goal (hdim : Module.finrank ℝ E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{u, u} (E := E))
    {β ν : ℝ} (hβ : 0 < β) (hν : 2 * ν ≤ β) :
    ∃ ε₁ δ₁ : ℝ, 0 < ε₁ ∧ 0 < δ₁ ∧ δ₁ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₁ →
      ∀ {ι : Type w} {η : ℝ}, η ≤ ε₁ →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        ∀ {C : NNReal} (𝒱 : ShadedTube.ShadedUniformTubeSet s V (ssfGridLen δ) C),
          ENNReal.ofReal ((δ : ℝ) ^ η)
              ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
          Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η)) →
          𝒱.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁))) →
          ∀ ε : ℝ, 0 < ε →
            ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
              ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ (β - ν) := by
  obtain ⟨ε₁, δ₁, hε₁, hδ₁, hδ₁1, hmain⟩ :=
    exists_everyScale_multiplicity_le.{u, w} (E := E) hdim hSFE
      (ε₀ := Kakeya.ML2Spine.absAccuracy β) (Kakeya.ML2Spine.absAccuracy_pos hβ)
  refine ⟨ε₁, δ₁, hε₁, hδ₁, hδ₁1, ?_⟩
  intro δ hδpos hδle ι η hη s V hball hcard C 𝒱 hfull hdens hevery ε hε
  have hδ1 : δ ≤ 1 := by
    have : (δ : ℝ) ≤ 1 := hδle.trans hδ₁1
    exact_mod_cast this
  refine (hmain hδpos hδle hη s V hball 𝒱 hfull hdens hevery).trans ?_
  refine ofReal_rpow_neg_le_mul_card_rpow hδpos hδ1 hcard (by linarith) ?_
  simp only [Kakeya.ML2Spine.absAccuracy]
  linarith

/-! ### Feeding the dichotomy from `Kakeya.ML2Spine.IsSpine` -/

/-- **The ladder hypothesis of GWZ Lemma 7.7(B), read off the spine.**

`StickyKakeya.dividingScalesKatzTao` wants `η k ≤ e · η (k+1)` for `k < N`; the spine
carries the sharper separation `Kakeya.ML2Spine.IsSpine.sep_le`,
`12 η_k/(e β) ≤ e η_{k+1}/4`, which gives `η k ≤ e² β η_{k+1}/48` and hence the lemma's form as
soon as `e β ≤ 48` — true with room to spare, since `e ≤ ε₂/5 ≤ 1/10` and `β ≤ 1`. -/
theorem rung_le_div_mul_rung_succ {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : Kakeya.ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) : η k ≤ e * η (k + 1) := by
  have hepos : 0 < e := h.div_pos
  have hη1 : 0 < η (k + 1) := h.rung_pos (k + 1)
  have hd : e ≤ ε₂ / 5 := h.div_le
  have hhalf : ε₂ ≤ 1 / 2 := h.eps₂_le_half
  have he10 : e ≤ 1 / 10 := by linarith
  have hab : e * β ≤ 1 := by nlinarith
  have hsep := h.sep_le k hk
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < e * β)] at hsep
  nlinarith [mul_nonneg (mul_pos hepos hη1).le (by linarith : (0 : ℝ) ≤ 48 - e * β), hsep]

/-- **The dichotomy, fed directly from the Main-Lemma-2 parameter spine.**

`Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_params` with all four of its
`η`-hypotheses discharged from `Kakeya.ML2Spine.IsSpine`:

* `0 ≤ η 0` is `IsSpine.rung_pos`;
* `η k ≤ e · η (k+1)` for `k < N` is `Kakeya.ML2Reduction.rung_le_div_mul_rung_succ`;
* `η N ≤ e` is `IsSpine.rung_top`, an equality;
* `e = 1/√N` is `IsSpine.div_eq` and `e ≤ ε₁/25` is `IsSpine.div_le_everyScale`.

* `4096 ≤ N` is `IsSpine.four_thousand_le_stepCount`.

Nothing is left over: every hypothesis of `StickyKakeya.dividingScalesKatzTao` is a field of
`Kakeya.ML2Spine.IsSpine` or a one-line consequence of its fields.

Composed with `Kakeya.ML2Spine.exists_ml2SpineParams`, this is the whole of the first sentence of
the blueprint proof: that theorem produces `ν > 0` **before** `∀ ε > 0`, together with an
`IsSpine β ϖ (E (absAccuracy β)) gain dens ε₂ e N η` whose `ν = η 0`, and `ε₁` here is that same
`E (absAccuracy β) = ` the Katz--Tao exponent of Theorem 7.3(B) read at the *absolute* accuracy
`β/2`.  Nothing in this statement mentions the outer `ε`. -/
theorem exists_dichotomy_katzTaoAtEveryScale_of_isSpine (hn : Module.finrank ℝ E = 3)
    (Cu : NNReal) {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (hspine : Kakeya.ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε₁ : 0 < ε₁) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        UniformTubeSet s T (ssfGridLen δ) Cu →
        Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
        ∃ s' ⊆ s,
          (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
          ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
            (𝒰'.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
              ∨ ∃ a b m : ℕ,
                  IsKatzTaoDividingWindow 𝒰' ((C : ENNReal) * totalLoss C K c δ) η e N a b m) := by
  obtain ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, hmain⟩ :=
    exists_dichotomy_katzTaoAtEveryScale_params.{u} (E := E) hn Cu N
      hspine.four_thousand_le_stepCount hspine.div_eq hε₁ hspine.div_le_everyScale
  refine ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδpos hδle s T hball hED hunif hdens
  obtain ⟨s', hs's, hcard, 𝒰', halt⟩ := hmain (ι := ι) (δ := δ) hδpos hδle η
    (hspine.rung_pos 0).le (fun k hk => rung_le_div_mul_rung_succ hspine hβ hβ1 hk)
    (le_of_eq hspine.rung_top) s T hball hED hunif hdens
  refine ⟨s', hs's, hcard, 𝒰', ?_⟩
  rcases halt with hevery | ⟨a, b, m, hwindow⟩
  · exact Or.inl hevery
  · exact Or.inr ⟨a, b, m, hwindow.toIsKatzTaoDividingWindow⟩

/-- **The first sentence of the blueprint proof of Main Lemma 2, assembled and `ε`-free.**

This is the witness that the three pieces fit together, and that nothing in them is
vacuous: `Kakeya.ML2Reduction.exists_everyScale_exponent` supplies the accuracy-to-exponent map of
GWZ Theorem 7.3(B), `Kakeya.ML2Spine.exists_ml2SpineParams` runs the parameter chain at the
**absolute** accuracy `Kakeya.ML2Spine.absAccuracy β = β/2`, and
`Kakeya.ML2Reduction.exists_dichotomy_katzTaoAtEveryScale_of_isSpine` applies GWZ Lemma 7.7(B) at
the resulting `(N, e, η)`.

**Both `ν` and `ε₁` are bound outside `∀ ε > 0`**, which is exactly what Prof. Hong Wang's
clarification of 2026-08-30 demands and what
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy` shows to be impossible if Theorem 7.3(B) is read
at the outer `ε` instead.  The only clause that mentions `ε` at all is
`absAccuracy β ≤ ε + (β - ν)`, the inequality that
`Kakeya.ML2Reduction.ofReal_rpow_neg_le_mul_card_rpow` spends against `|𝕋| ≥ δ^{-1}` to turn the
every-scale bound `μ(𝕋,Y) ≤ δ^{-β/2}` into the Main Lemma 2 goal `μ(𝕋,Y) ≤ δ^{-ε} |𝕋|^{β-ν}`.

There is **no residual side condition**.  An earlier version of this theorem guarded its last
conjunct by `4096 ≤ N`, because `Kakeya.ML2Spine.IsSpine` did not imply the threshold that
`StickyKakeya.dividingScalesKatzTao` demands.  That hole is closed on the `IsSpine` side:
`Kakeya.ML2Spine.IsSpine.four_thousand_le_stepCount` is now a field, realized by
`Kakeya.ML2Spine.spineEps₂`'s cap of `1/64`.

What is still missing before this becomes Main Lemma 2 is the *other* branch (the dividing
window, handled by the `Spine*` rescaling files) and the shading bridge described in the module
docstring. -/
theorem exists_ml2_epsFree_dichotomy (hn : Module.finrank ℝ E = 3) (Cu : NNReal)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{u, u} (E := E))
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ∃ ν ε₁ : ℝ, 0 < ν ∧ 0 < ε₁ ∧ 2 * ν ≤ β ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ (ε₂ e : ℝ) (N : ℕ) (η : ℕ → ℝ),
          Kakeya.ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η ∧ ν = η 0 ∧
          Kakeya.ML2Spine.absAccuracy β ≤ ε + (β - ν) ∧
          (∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
              ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
              ∀ (s : Finset ι) (T : ι → Tube δ E),
                (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
                (s : Set ι).Pairwise
                  (fun i j => IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
                UniformTubeSet s T (ssfGridLen δ) Cu →
                Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
                    ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
                ∃ s' ⊆ s,
                  (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
                  ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
                    (𝒰'.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-ε₁)))
                      ∨ ∃ a b m : ℕ,
                          IsKatzTaoDividingWindow 𝒰'
                            ((C : ENNReal) * totalLoss C K c δ) η e N a b m)) := by
  obtain ⟨Eexp, hEpos, -⟩ := exists_everyScale_exponent.{u, u} (E := E) hn hSFE
  obtain ⟨ν, hν, hνβ, hmain⟩ :=
    Kakeya.ML2Spine.exists_ml2SpineParams hβ hβ1 hϖ hgain hdens (E := Eexp) hEpos
  refine ⟨ν, Eexp (Kakeya.ML2Spine.absAccuracy β), hν,
    hEpos _ (Kakeya.ML2Spine.absAccuracy_pos hβ), hνβ, ?_⟩
  intro ε hε
  obtain ⟨ε₂, e, N, η, hspine, hν0, -, hgoal⟩ := hmain ε hε
  refine ⟨ε₂, e, N, η, hspine, hν0, hgoal, ?_⟩
  exact exists_dichotomy_katzTaoAtEveryScale_of_isSpine.{u} (E := E) hn Cu hspine hβ hβ1
    (hEpos _ (Kakeya.ML2Spine.absAccuracy_pos hβ))

end Kakeya.ML2Reduction

end
