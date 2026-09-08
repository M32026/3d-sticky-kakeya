/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.KatzTao
public import Kakeya.Uniform
public import Kakeya.ShadedUniform
public import Kakeya.Multiplicity

/-!
# The two every-scale conditions

Staging area for the replacement of `Tube.IsFrostmanAtEveryScale` and
`Tube.IsKatzTaoAtEveryScale`.  Both are re-based on `Tube.UniformTubeSet`, and both
are restated in the reading Wang–Zahl actually use.

## What changes, and why

**The anchor is a node, not a thickened leaf.**  WZ set
`𝕋[T_ρ] = {T ∈ 𝕋 : T ⊂ T_ρ}` with `T_ρ` a member of the balanced partitioning cover `𝕋_ρ`
(`blueprint/src/WZ2/250224e_K3.tex:365`), and impose the axiom on `𝕋^{T_ρ}` — the family rescaled so
that `T_ρ` becomes the unit ball.  The anchor is therefore a *free* `ρ`-tube, not the `ρ`-thickening
`T_{i₀}^{(ρ)}` of a leaf.  Two consequences: the rescaling is invisible here, because
`ConvexSpaceBody.frostmanConstant` is a ratio of densities and so is invariant under it; and the
factor-`2` anchor inflation that the leaf reading forced *disappears*, since a class lies inside its
own node by construction and that is exactly what `ConvexSpaceBody.IsFrostmanIn` requires of its
members.

**The scale runs over grid points only.**  WZ's definitions quantify over every `ρ₀ ∈ [δ,1]` but
allow the scale actually used to be any `ρ ∈ [ρ₀, Kρ₀)` (`:2258` and `:4734`).  With error
`K = δ^{-5ε}` against grid spacing `δ^{-1/N} = δ^{-ε²}` the grid is far finer than that window, so a
grid point always lies in it: quantifying over grid indices is WZ's condition with the scale-choice
freedom already spent.  What this buys is the deletion of the two "grid scales suffice" lemmas,
whose only job was to re-derive that freedom.

**(A) speaks of the classes, (B) of the cover itself.**  That is the sole difference between WZ's
two definitions: `:2261` imposes a Frostman bound on `𝕋^{T_ρ}` for each node `T_ρ`, while
`:4737` imposes a Katz–Tao bound on `𝕋_ρ` as a family.

The old thickened Katz–Tao reading is *not* reinstated: `Δ_max(𝕋^{(ρ)}) ≤ A` on the
multiplicity-preserving family forces `#s ≲_n A`, which no family of `≈ δ^{-(n-1)}` tubes satisfies
with `A = δ^{-o(1)}`.

**Fibre families and comparable fibre counts are gone.**  Both were artefacts of the leaf reading.
A leaf-anchored fibre `{i ∈ s : T_i^{(σ)} ⊆ T_{i₀}^{(ρ)}}` has no reason to have the same size as
its neighbours, so their comparability had to be carried as a separate hypothesis and separately
re-established after every refinement; the two-sided bracket of Definition 2.1(iii) on the
*containment* set does not give it.  Once the object is the class of a node, comparability *is*
`Tube.UniformTubeSet.card_class_le` together with
`Tube.UniformTubeSet.le_card_class`, both squeezing against the same `branchingN k`.
Nothing to hypothesise and nothing to restore.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- Definition 7.1(A): `T` is `C`-Frostman at every scale: for every `ρ ∈ [δ, 1]`
and every `i₀ ∈ s`, the sub-family of tubes contained in the ρ-rescale of
`T i₀` is `C`-Frostman inside that rescale. -/
def IsFrostmanAtEveryScale {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (C : ENNReal) : Prop :=
  ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ s,
        ConvexSpaceBody.IsFrostmanIn {i ∈ s |
            (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ).toConvexSpaceBody}
          (fun i => (T i).toConvexSpaceBody)
          ((T i₀).rescale ρ).toConvexSpaceBody C

omit [Nontrivial E] in
lemma IsFrostmanAtEveryScale_def {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (C : ENNReal) :
    IsFrostmanAtEveryScale s T C ↔
      ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ s,
        ConvexSpaceBody.IsFrostmanIn {i ∈ s |
            (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ).toConvexSpaceBody}
          (fun i => (T i).toConvexSpaceBody)
          ((T i₀).rescale ρ).toConvexSpaceBody C := Iff.rfl
/-! ### The two every-scale conditions -/

/-- **GWZ Definition 7.1(A)** (WZ `convexAtEveryScaleFromAssouadPaper`,
`blueprint/src/WZ2/250224e_K3.tex:2258`).

For every grid scale and every node of the hierarchy there, the class of leaves assigned to that
node is `A`-Frostman *inside the node*.  This is WZ's `C_FC(𝕋^{T_ρ}) ≤ K` for each `T_ρ ∈ 𝕋_ρ`
(`:2261`), read without the affine rescaling.

No thickening of the members and no inflation of the anchor: the class lies in its own node by
construction. -/
def UniformTubeSet.IsFrostmanAtEveryScale {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (A : ENNReal) : Prop :=
  ∀ k ≤ N, ∀ j ∈ 𝒰.cover.indexSet k,
    ConvexSpaceBody.IsFrostmanIn
      (coverClass s (𝒰.cover.assign k) j)
      (fun i => (T i).toConvexSpaceBody)
      (𝒰.cover.tube k j).toConvexSpaceBody A

/-- **GWZ Definition 7.1(B)** (WZ `KatzTaoConvexWolffAtEveryScaleDefn`,
`blueprint/src/WZ2/250224e_K3.tex:4734`).

`Δ_max` of the *node family* at each grid scale, each node counted once.  This is WZ's
`C_KT(𝕋_ρ) ≤ K` (`:4737`).  The multiplicities with which the members of `𝕋` sit inside the nodes do
not enter — that is the whole point, and it is why this is not the thickened reading. -/
def UniformTubeSet.IsKatzTaoAtEveryScale {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (A : ENNReal) : Prop :=
  ∀ k ≤ N,
    Kakeya.maxDensity (𝒰.cover.indexSet k)
      (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) ≤ A

omit [Nontrivial E] in
/-- Both conditions weaken as the error grows. -/
theorem UniformTubeSet.IsFrostmanAtEveryScale.mono {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} {𝒰 : UniformTubeSet s T N C} {A A' : ENNReal}
    (h : 𝒰.IsFrostmanAtEveryScale A) (hA : A ≤ A') : 𝒰.IsFrostmanAtEveryScale A' := by
  intro k hk j hj K' hK'
  exact (h k hk j hj K' hK').trans (mul_le_mul_left hA _)

omit [Nontrivial E] in
theorem UniformTubeSet.IsKatzTaoAtEveryScale.mono {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} {𝒰 : UniformTubeSet s T N C} {A A' : ENNReal}
    (h : 𝒰.IsKatzTaoAtEveryScale A) (hA : A ≤ A') : 𝒰.IsKatzTaoAtEveryScale A' :=
  fun k hk => (h k hk).trans hA

end Tube

open Tube
open ShadedTube

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- Statement of GWZ Theorem 7.3(A): for every `ε > 0` there exist `η, δ₀ > 0`
such that for every `δ ∈ (0, δ₀]` and every uniform shaded family `(T, Y)` of
`δ`-tubes in the unit ball of `E` with `λ(T, Y) ≥ δ^η`, if `T` is Frostman at
every scale with error `δ^{-η}` then `|U(T, Y)| ≥ δ^ε`.

The original GWZ statement is for `E = ℝ³`; the dimension assumption is dropped
here so that the dimension-free implication `StickyFrostmanEstimate ⇒
StickyKatzTaoEstimate` (Lemma 7.4 + Lemma 7.5) can be formulated in any `n`.

**Uniformity and the every-scale condition share one hierarchy.**  Both hypotheses are read
off a single `ShadedTube.ShadedUniformTubeSet`: its `tubeUniform` field is the nested
system of covers of GWZ Definition 2.1 along the grid `ρ_k = δ^{k/N}`, and
`Tube.UniformTubeSet.IsFrostmanAtEveryScale` imposes the Frostman bound on the
*class* of each node of that very system.  This replaces the pair
"`∃ C, Nonempty (per-scale shaded uniformity …)`" plus the leaf-anchored
`Tube.IsFrostmanAtEveryScale`, in which nothing tied the family witnessing
uniformity to the anchors carrying the Frostman bound.  Quantifying over *every* bundle
rather than asserting that some bundle exists is what lets the every-scale hypothesis refer
to the bundle at all; a consumer holding one bundle can still apply the statement to it.

**Grid length and uniformity constant.**  The grid length is
`Tube.ssfGridLen δ = ⌈log log (1/δ)⌉`, which is the scale set of GWZ Definition 2.2.
The bundle constant is bounded by the dimension-only constant
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)` produced by shaded uniformization. -/
def StickyFrostmanEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∀ {C : NNReal}, C ≤ ssfUniformConst (Module.finrank ℝ E) →
        ∀ (𝒱 : ShadedUniformTubeSet s V (ssfGridLen δ) C),
        ENNReal.ofReal ((δ : ℝ) ^ η)
          ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
        𝒱.tubeUniform.IsFrostmanAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
        ENNReal.ofReal ((δ : ℝ) ^ ε) ≤ volume (⋃ i ∈ s, (V i).shade)

/-- Statement of GWZ Theorem 7.3(B): for every `ε > 0` there exist `η, δ₀ > 0`
such that for every `δ ∈ (0, δ₀]` and every uniform shaded family `(T, Y)` of
`δ`-tubes in the unit ball of `E` with `λ(T, Y) ≥ δ^η` and `Δ_max(T) ≤ δ^{-η}`, if `T` is
Katz-Tao at every scale with error `δ^{-η}` then `μ(T, Y) ≤ δ^{-ε}`.

The original GWZ statement is for `E = ℝ³`; the dimension assumption is dropped
here so that the dimension-free implication `StickyFrostmanEstimate ⇒
StickyKatzTaoEstimate` (Lemma 7.4 + Lemma 7.5) can be formulated in any `n`.

**The every-scale condition is read on the node family.**
`Tube.UniformTubeSet.IsKatzTaoAtEveryScale` bounds `Δ_max` of the *nodes* of the
hierarchy at each grid scale, each node counted once; the multiplicities with which the
members of `T` sit inside them do not enter.  The thickened reading previously used here is
unsatisfiable in the regime the statement is applied in, since
`Δ_max(T^{(ρ)}) ≤ A` on the multiplicity-preserving family forces `#s ≲_n A`
(`StickyKakeya.card_mul_le_of_isKatzTaoAtEveryScale`).

**The leaf-scale hypothesis is new and necessary.**  `Δ_max(T) ≤ δ^{-η}` at the leaf scale
`δ` is *not* implied by the node reading: at `ρ = δ` the every-scale condition bounds the
density of a family of nodes covering `T`, and a node may bunch essentially identical leaves,
so it says nothing about leaf multiplicities.  The proof of Lemma 7.5 uses a leaf-scale
density bound twice, and the thickened reading supplied it implicitly.  Downstream this costs
nothing: the §9 consumer (`Kakeya.KatzTaoEstimate`) carries this bound already. -/
def StickyKatzTaoEstimate : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ →
      ∀ {ι : Type} (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∀ {C : NNReal} (𝒱 : ShadedUniformTubeSet s V (ssfGridLen δ) C),
        ENNReal.ofReal ((δ : ℝ) ^ η)
          ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) →
        ConvexSpaceBody.IsKatzTao s (fun i => (V i).toConvexSpaceBody)
            (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
        𝒱.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η))) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε))

end StickyKakeya

