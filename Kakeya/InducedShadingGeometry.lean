/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.BallDense
public import Kakeya.Factorization
public import Kakeya.Shading
public import Kakeya.Thickness.Scale

/-!
# The common block scale, and the geometry of an induced shading

`ShadedBody.inducedShading` (GWZ Definition 5.7) thickens each block `W j` by *its own*
shortest affine thickness `r j = τ_{n-1}(W j)`, whereas GWZ thicken every block by one and the
same scale `w₁`.  `ConvexSpaceBody.HasCommonScale` records the hypothesis that makes the two
agree up to a bounded factor; it is what GWZ's phrase "`𝒲` is a family of convex sets of
dimensions roughly `w₁ × ⋯ × wₙ`" asserts, and every outer family produced by the factorization
machinery satisfies it with `K = 2`.

This file collects the set-theoretic and measure-theoretic ingredients of GWZ Lemma 5.8
(`ShadedBody.multiplicityLowerBdInducedShading`, in `Kakeya/Multiplicity.lean`): the sandwich
`U(𝒱, Y) ⊆ U(𝒲, Y_𝒲) ⊆ N_{K r}(U(𝒱, Y))`, the dilation of a single induced shade, the
integrated form of a pointwise covering bound, and the volume bound on a dilated block
thickening coming from ball density.

The fullness estimate for an induced shading in `ℝ³` (GWZ Lemma 5.9,
`ShadedBody.lambdaForInducedShading`) is a separate development, in
`Kakeya/DimensionThree/InducedShading.lean`.
-/

@[expose] public section

open Metric MeasureTheory Convexity

/-! ### The common block scale -/

namespace ConvexSpaceBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- Blueprint `def:commonBlockScale`: the family `𝒲 = (W j)_{j ∈ t}` has **common scale `r`
with comparability `K`** if `r ≤ τ_{n-1}(W j) ≤ K * r` for every `j ∈ t`.

This is not a new demand on the development: every outer family produced by the factorization
machinery satisfies it with `K = 2`, by
`ConvexSpaceBody.Factorization.exists_hasCommonScale`. -/
def HasCommonScale (t : Finset ι) (W : ι → ConvexSpaceBody E) (r K : ℝ) : Prop :=
  ∀ j ∈ t, r ≤ (W j).scale ∧ (W j).scale ≤ K * r

variable [DecidableEq ι]

/-- Blueprint `lem:factorizationCommonBlockScale`: a `C`-factoring outer family has a common
block scale with comparability `C`.

Item (iii) of `ConvexSpaceBody.Factorization` (`simDims`), read at rank `n - 1` and at the
block `t₀` realising the minimum, gives `ethick_{n-1}(W t) ≤ C · ethick_{n-1}(W t₀)`; since
each block is compact, `ethickness` and `thickness` agree on it.  In particular the outer
family of GWZ Lemma 4.1 (`ConvexSpaceBody.nonempty_factorization.factorization`), which
`2`-factors `𝒱'`, has a common block scale with `K = 2`. -/
theorem Factorization.exists_hasCommonScale {C : NNReal} {s : Finset ι}
    {V : ι → ConvexSpaceBody E} (f : Factorization s V C) (hC : 1 ≤ C)
    (hne : f.parts.Nonempty)
    (hpos : ∀ p ∈ f.parts, 0 < (p.convexHull_biUnion V).scale) :
    ∃ r > 0, HasCommonScale f.parts (fun p => p.convexHull_biUnion V) r C := by
  classical
  let W : Finset ι → ConvexSpaceBody E := fun p => p.convexHull_biUnion V
  obtain ⟨t₀, ht₀, hmin⟩ := Finset.exists_min_image f.parts (fun p => (W p).scale) hne
  let r : ℝ := (W t₀).scale
  refine ⟨r, ?_, ?_⟩
  · exact hpos t₀ ht₀
  · intro j hj
    constructor
    · simpa [HasCommonScale, r, W] using (hmin j hj)
    · have hsim : ∀ k : ℕ,
          Metric.ethickness ℝ (W j).carrier k ≤
            C • Metric.ethickness ℝ (W t₀).carrier k :=
        f.simDims j hj t₀ ht₀
      let k : ℕ := Module.finrank ℝ E - 1
      have hjy : Bornology.IsBounded (W j).carrier := (W j).isBounded
      have hty : Bornology.IsBounded (W t₀).carrier := (W t₀).isBounded
      have hle : ENNReal.ofReal (thickness ℝ (W j).carrier k) ≤
          (C : ENNReal) * ENNReal.ofReal (thickness ℝ (W t₀).carrier k) := by
        have hsimk := hsim k
        rw [Metric.ethickness_thickness' hjy k] at hsimk
        rw [Metric.ethickness_thickness' hty k] at hsimk
        simpa [ENNReal.smul_def, smul_eq_mul] using hsimk
      have hC0 : (0 : ℝ) ≤ (C : ℝ) := C.2
      have ht0 : 0 ≤ thickness ℝ (W t₀).carrier k := Metric.thickness_nonneg _ _
      have ht0' : 0 ≤ (C : ℝ) * thickness ℝ (W t₀).carrier k := mul_nonneg hC0 ht0
      have hle' : ENNReal.ofReal (thickness ℝ (W j).carrier k) ≤
          ENNReal.ofReal ((C : ℝ) * thickness ℝ (W t₀).carrier k) := by
        calc
          ENNReal.ofReal (thickness ℝ (W j).carrier k) ≤
              (C : ENNReal) * ENNReal.ofReal (thickness ℝ (W t₀).carrier k) := hle
          _ = ENNReal.ofReal ((C : ℝ) * thickness ℝ (W t₀).carrier k) := by
                rw [← ENNReal.ofReal_coe_nnreal]
                rw [← ENNReal.ofReal_mul hC0]
      have hleR : thickness ℝ (W j).carrier k ≤
          (C : ℝ) * thickness ℝ (W t₀).carrier k :=
        (ENNReal.ofReal_le_ofReal_iff ht0').mp hle'
      have hjr : (W j).scale ≤ (C : ℝ) * (W t₀).scale := by
        simpa [ConvexSpaceBody.scale, k] using hleR
      simpa [HasCommonScale, r, W] using hjr

end ConvexSpaceBody

/-! ### The shaded union of an induced shading -/

namespace ShadedBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (V : ι → ShadedBody E) (part : ι → κ) (t : Finset κ)
    (W : κ → ConvexSpaceBody E)

/-! Blueprint `lem:inducedShadingInnerUnionSubset` is
`ShadedBody.iUnionShade_subset_iUnionShade_inducedShading` in `Kakeya/Shading.lean`.  A
branch-local copy used to live here; it collided with the upstream declaration when `main` was
merged in, and the upstream one is kept because it is stated in unbundled `iUnionShade` form and
sits low enough in the import graph to serve families that are not packaged as a
`ShadedBody.FactorFamily`.  Note the argument order differs: the upstream lemma takes the parent
index set and family first, as `t Wout p`. -/

/-- Blueprint `lem:inducedShadingOuterUnionSubset`: the induced shaded union is a bounded
thickening of the inner one, `U(𝒲, Y_𝒲) ⊆ N_{2 K r}(U(𝒱, Y))`.

Only the upper half `τ_{n-1}(W j) ≤ K r` of the common-scale hypothesis is used here, and it is
exactly what the common block scale buys: with a per-block radius one only gets
`U(𝒲, Y_𝒲) ⊆ ⋃_j N_{2 r_j}(U(𝒱_j, Y))`, and blocks whose `r_j` exceeds the common radius escape
the thickening.

The factor `2` is the one in `ShadedBody.inducedShading`, whose shade is cut out of
`N_{2 τ_{n-1}(W)}(U(𝒱_W, Y))` rather than of `N_{τ_{n-1}(W)}(U(𝒱_W, Y))`. -/
theorem iUnionShade_inducedShading_subset_cthickening {r K : ℝ}
    (hcs : ConvexSpaceBody.HasCommonScale t W r K) :
    (⋃ j ∈ t, (inducedShading (s := s.filter fun i => part i = j) (V := V) (W j)).shade)
      ⊆ Metric.cthickening (2 * (K * r)) (⋃ i ∈ s, (V i).shade) := by
  apply Set.iUnion₂_subset
  intro j hj
  have hscale : 2 * (W j).scale ≤ 2 * (K * r) := by
    have := (hcs j hj).2
    linarith
  have hfibre : (⋃ i ∈ (s.filter fun i => part i = j), (V i).shade) ⊆
      ⋃ i ∈ s, (V i).shade := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hxi⟩
  have h1 : (inducedShading (s := s.filter fun i => part i = j) (V := V) (W j)).shade ⊆
      Metric.cthickening (2 * (W j).scale)
        (⋃ i ∈ (s.filter fun i => part i = j), (V i).shade) := by
    dsimp [inducedShading]
    dsimp [ConvexSpaceBody.scale]
    exact Set.inter_subset_left
  have hset : Metric.cthickening (2 * (W j).scale)
        (⋃ i ∈ (s.filter fun i => part i = j), (V i).shade) ⊆
      Metric.cthickening (2 * (W j).scale) (⋃ i ∈ s, (V i).shade) :=
    Metric.cthickening_subset_of_subset (2 * (W j).scale) hfibre
  have hrad : Metric.cthickening (2 * (W j).scale) (⋃ i ∈ s, (V i).shade) ⊆
      Metric.cthickening (2 * (K * r)) (⋃ i ∈ s, (V i).shade) :=
    Metric.cthickening_mono hscale _
  exact h1.trans (hset.trans hrad)

/-- Blueprint `lem:inducedShadingUnionSandwich`: sandwiching the induced shaded union,
`U(𝒱, Y) ⊆ U(𝒲, Y_𝒲) ⊆ X` where `X = N_{2 K r}(U(𝒱, Y))`. -/
theorem iUnionShade_inducedShading_sandwich {r K : ℝ} (hpt : ∀ i ∈ s, part i ∈ t)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ (W (part i)).carrier)
    (hcs : ConvexSpaceBody.HasCommonScale t W r K) :
    (⋃ i ∈ s, (V i).shade) ⊆
        (⋃ j ∈ t, (inducedShading (s := s.filter fun i => part i = j) (V := V) (W j)).shade) ∧
      (⋃ j ∈ t, (inducedShading (s := s.filter fun i => part i = j) (V := V) (W j)).shade)
        ⊆ Metric.cthickening (2 * (K * r)) (⋃ i ∈ s, (V i).shade) := by
  have hVW : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ W (part i) := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hsub i hi)
  constructor
  · have h := iUnionShade_subset_iUnionShade_inducedShading s V t W part hpt hVW
    have hfibre (j : κ) :
        inducedShading (s := @Finset.filter ι (fun i => part i = j) (Classical.decPred _) s)
            (V := V) (W j) =
          inducedShading (s := s.filter fun i => part i = j) (V := V) (W j) := by
      exact congrArg (fun S => inducedShading S V (W j))
        (Finset.filter_congr_decidable s (fun i => part i = j) (Classical.decPred _))
    intro x hx
    have hx' : x ∈ iUnionShade s V := by simpa [iUnionShade] using hx
    rcases Set.mem_iUnion₂.mp (h hx') with ⟨j, hj, hxj⟩
    refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
    simpa [hfibre] using hxj
  · exact iUnionShade_inducedShading_subset_cthickening s V part t W hcs

variable {s V}

/-- Blueprint `lem:inducedShadingShadeDilate`: dilating one induced shade.
`N_ϱ(Y_𝒲(W)) ⊆ N_{ϱ + 2 τ_{n-1}(W)}(U(𝒱_W, Y))`.

As in `ShadedBody.iUnionShade_inducedShading_subset_cthickening`, the factor `2` is the one
built into `ShadedBody.inducedShading`. -/
theorem cthickening_inducedShading_shade_subset (W : ConvexSpaceBody E) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    Metric.cthickening ϱ (inducedShading (s := s) (V := V) W).shade
      ⊆ Metric.cthickening (ϱ + 2 * W.scale) (⋃ i ∈ s, (V i).shade) := by
  have hshade : (inducedShading (s := s) (V := V) W).shade ⊆
      Metric.cthickening (2 * W.scale) (⋃ i ∈ s, (V i).shade) := by
    dsimp [inducedShading]
    dsimp [ConvexSpaceBody.scale]
    exact Set.inter_subset_left
  have hscale : 0 ≤ 2 * W.scale := by
    have h0 : (0 : ℝ) ≤ W.scale := Metric.thickness_nonneg _ _
    linarith
  calc
    Metric.cthickening ϱ (inducedShading (s := s) (V := V) W).shade
        ⊆ Metric.cthickening ϱ (Metric.cthickening (2 * W.scale) (⋃ i ∈ s, (V i).shade)) :=
      Metric.cthickening_subset_of_subset ϱ hshade
    _ ⊆ Metric.cthickening (ϱ + 2 * W.scale) (⋃ i ∈ s, (V i).shade) :=
      Metric.cthickening_cthickening_subset hϱ hscale _

/-- Blueprint `lem:inducedShadingBlockVolumeBound`: volume of a dilated block thickening.
If every `V i` of the block sits inside `W`, and `W` is `β`-ball dense at its own scale
`r = τ_{n-1}(W) > 0`, then for every `K ≥ 1`
`|N_{(K+1) r}(U(𝒱_W, Y))| ≤ C(n, K + 1, β) · |Y_𝒲(W)|`.

This is `Metric.volume_cthickening_le_of_isBallDense` applied to the compact set `W`, the
measurable subset `A = U(𝒱_W, Y) ⊆ W`, and the dilation factor `λ = K + 1`, using
`W ∩ N_r(U(𝒱_W, Y)) = Y_𝒲(W)`. -/
theorem volume_cthickening_iUnionShade_le_of_isBallDense (W : ConvexSpaceBody E)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ W.carrier) {β K : NNReal}
    (hβ : Metric.IsBallDense (W.carrier : Set E) W.scale β) (hβ0 : 0 < β)
    (hscale : 0 < W.scale) (hK : 1 ≤ K) :
    volume (Metric.cthickening (((K : ℝ) + 1) * W.scale) (⋃ i ∈ s, (V i).shade))
      ≤ (Metric.volume_cthickening_le_of_isBallDense.C (Module.finrank ℝ E) (K + 1) β : ENNReal)
        * volume (inducedShading (s := s) (V := V) W).shade := by
  let A : Set E := ⋃ i ∈ s, (V i).shade
  have hA : MeasurableSet A := by
    dsimp [A]
    exact Finset.measurableSet_biUnion s (fun i _ => (V i).measurableSet_shade)
  have hAW : A ⊆ W.carrier := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact hsub i hi ((V i).shade_subset hxi)
  have hlam : (1 : NNReal) ≤ K + 1 := by
    exact le_trans hK (le_add_of_nonneg_right zero_le_one)
  have hbnd := Metric.volume_cthickening_le_of_isBallDense (W := W.carrier) (A := A)
    (r := W.scale) (lam := K + 1) (β := β) W.isCompact hβ hscale hβ0 hA hAW hlam
  -- `W ∩ N_r(A)` is contained in the shade `N_{2r}(A) ∩ N_r(W)` of `inducedShading`,
  -- so the ball-density bound for the former also bounds the latter.
  have hmono : W.carrier ∩ Metric.cthickening W.scale A ⊆
      (inducedShading (s := s) (V := V) W).shade := by
    dsimp [inducedShading, ConvexSpaceBody.scale]
    intro x hx
    refine ⟨Metric.cthickening_mono ?_ _ hx.2, Metric.self_subset_cthickening _ hx.1⟩
    have h0 : (0 : ℝ) ≤ Metric.thickness ℝ W.carrier (Module.finrank ℝ E - 1) :=
      Metric.thickness_nonneg _ _
    linarith
  exact hbnd.trans (by gcongr)

end ShadedBody

/-! ### Integrating a pointwise covering bound -/

namespace MeasureTheory

/-- Blueprint `lem:multiplicityLowerBdCoveringIntegral`: if `∑_{j ∈ t} 1_{A j} ≥ c` pointwise on
a measurable set `X`, then `c · |X| ≤ ∑_{j ∈ t} |A j|`. -/
theorem mul_measure_le_sum_measure_of_le_sum_indicator {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} (t : Finset ι) {X : Set α} {A : ι → Set α}
    (hX : MeasurableSet X) (hA : ∀ j ∈ t, MeasurableSet (A j)) {c : ENNReal}
    (h : ∀ x ∈ X, c ≤ ∑ j ∈ t, (A j).indicator (1 : α → ENNReal) x) :
    c * μ X ≤ ∑ j ∈ t, μ (A j) := by
  calc c * μ X
      = ∫⁻ x, X.indicator (fun _ : α => c) x ∂μ := by
        rw [lintegral_indicator_const hX c]
    _ ≤ ∫⁻ x, ∑ j ∈ t, (A j).indicator (1 : α → ENNReal) x ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ X
        · rw [Set.indicator_of_mem hx]
          exact h x hx
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ∑ j ∈ t, ∫⁻ x, (A j).indicator (1 : α → ENNReal) x ∂μ := by
        rw [lintegral_finsetSum t]
        exact fun j hj => measurable_const.indicator (hA j hj)
    _ = ∑ j ∈ t, μ (A j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [lintegral_indicator_one (hA j hj)]

end MeasureTheory
