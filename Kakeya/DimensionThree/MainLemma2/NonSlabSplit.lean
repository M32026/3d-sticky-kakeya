/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre
public import Kakeya.DimensionThree.MainLemma2.ThinConfig

/-!
# Splitting the multiplicity in the non-slab case of Main Lemma 2

This file formalizes the compatible refinement of the non-slab case and the resulting
splitting of `μ(𝕋, Y)` into an outer (body) factor and an inner (angular) factor: blueprint
`lem:ml2nonslabSegmentLocalise`, `lem:ml2nonslabCompat`, `lem:ml2nonslabPiecewise`,
`lem:ml2nonslabPointwiseMult`, `lem:ml2nonslabMultSplit` and `lem:ml2nonslabKKT`.

As in `Kakeya.DimensionThree.MainLemma2.ThinSetup`, the global Configurations
`hyp:ml2setup` and `hyp:ml2thinsetup` are not bundled into a single Lean object; the data
they supply is passed explicitly. The names follow the blueprint: `I` indexes `𝕋` with
shadings `Yg = Y` and `Y' `, `Pc B = B̂` is the piece of the subordinate partition of (C2)
attached to the ball `B`, `segs = 𝕋_B` with `carr` its carriers and `Yb = Y_B`, `Yb' = Y'_B`
its shadings, `fam p = 𝕋(T_B)` is the family of parent tubes of a segment, `blk` is the block
map of the factoring of (C4) and `bodies' B = 𝕎'_B` with shading `Wsh = Y_{𝕎'_B}` and axes
`ax j = v(W)`.
-/

@[expose] public section

namespace Kakeya.NonSlab

open MeasureTheory Metric Set ShadedBody

section Compat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Localising the tubes through a point to their parent segments** (blueprint
`lem:ml2nonslabSegmentLocalise`).

Let `x` lie in the partition piece `B̂` and let `T ∈ 𝕋` shade `x` for the refined shading
`Y'`. Since `Y'(T) ⊆ Y(T)` the set `Y(T) ∩ B̂` is non-empty, so by (C5) the tube `T` belongs
to `𝕋(T_B)` for a segment `T_B ∈ 𝕋_B`, and `Y(T) ∩ B̂ ⊆ Y_B(T_B) ⊆ T_B`; in particular
`x ∈ T_B`. Therefore `x ∈ Y'(T) ∩ T_B ∩ B̂`, which lies in `Y'_B(T_B)` by the forward
compatibility of (T1). So

`𝕋_{Y'}(x) ⊆ ⋃_{T_B ∈ 𝕋_B, x ∈ Y'_B(T_B)} 𝕋(T_B)`,

which is what the conclusion says pointwise.

The forward compatibility used here is local to the piece `B̂`; see the implementation note
following blueprint Definition `hyp:ml2thinsetup` for why no version valid on the whole ball
`B` is available. -/
theorem segmentLocalise {ι σ : Type*} (I : Finset ι) (Yg Y' : ι → Set E) (Pc : Set E)
    (segs : Finset σ) (fam : σ → Finset ι) (carr Yb Yb' : σ → Set E)
    (hY' : ∀ T ∈ I, Y' T ⊆ Yg T)
    (hparent : ∀ T ∈ I, (Yg T ∩ Pc).Nonempty → ∃ p ∈ segs, T ∈ fam p)
    (hinto : ∀ p ∈ segs, ∀ T ∈ fam p, Yg T ∩ Pc ⊆ Yb p)
    (hYbcarr : ∀ p ∈ segs, Yb p ⊆ carr p)
    (hfwd : ∀ p ∈ segs, ∀ T ∈ fam p, Y' T ∩ carr p ∩ Pc ⊆ Yb' p)
    {x : E} (hx : x ∈ Pc) :
    ∀ T ∈ I, x ∈ Y' T → ∃ p ∈ segs, x ∈ Yb' p ∧ T ∈ fam p := by
  intro T hTI hxTY
  have hxYg : x ∈ Yg T := hY' T hTI hxTY
  have hnonempty : (Yg T ∩ Pc).Nonempty := ⟨x, ⟨hxYg, hx⟩⟩
  rcases hparent T hTI hnonempty with ⟨p, hpseg, hTfam⟩
  have hxYb : x ∈ Yb p := hinto p hpseg T hTfam ⟨hxYg, hx⟩
  have hxcarr : x ∈ carr p := hYbcarr p hpseg hxYb
  have hxYb' : x ∈ Yb' p := hfwd p hpseg T hTfam ⟨⟨hxTY, hxcarr⟩, hx⟩
  exact ⟨p, hpseg, hxYb', hTfam⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Compatible refinements in the non-slab case** (blueprint `lem:ml2nonslabCompat`).

Combining `Kakeya.NonSlab.segmentLocalise` with the pointwise containment (T3) — every
segment shading `x` lies in a block whose body is shaded at `x` — and with the angular bound
`∠(T, v(W)) ≤ C_{lem:ml2bodyAngle}(C₀) ρ₂` of
`Kakeya.NonSlab.lineAngle_bodyAxis_le` gives, for every `x ∈ U(𝕋, Y') ∩ B̂`,

`𝕋_{Y'}(x) ⊆ ⋃_{W ∈ 𝕎'_B, x ∈ Y_{𝕎'_B}(W)} {T ∈ 𝕋_Y(x) : ∠(T, v(W)) ≤ C ρ₂}`.

The restriction to the partition piece `B̂` is essential; the hypotheses of
`segmentLocalise` are only available there. -/
theorem compat {ι σ ω : Type*} (I : Finset ι) (Yg Y' : ι → Set E) (dir : ι → E) (Pc : Set E)
    (segs : Finset σ) (fam : σ → Finset ι) (carr Yb Yb' : σ → Set E) (blk : σ → ω)
    (bodies' : Finset ω) (Wsh : ω → ShadedBody E) (ax : ω → E) {ρ : ℝ}
    (hY' : ∀ T ∈ I, Y' T ⊆ Yg T)
    (hparent : ∀ T ∈ I, (Yg T ∩ Pc).Nonempty → ∃ p ∈ segs, T ∈ fam p)
    (hinto : ∀ p ∈ segs, ∀ T ∈ fam p, Yg T ∩ Pc ⊆ Yb p)
    (hYbcarr : ∀ p ∈ segs, Yb p ⊆ carr p)
    (hfwd : ∀ p ∈ segs, ∀ T ∈ fam p, Y' T ∩ carr p ∩ Pc ⊆ Yb' p)
    -- (T3): the containment `containmentWWB`
    (hT3 : ∀ p ∈ segs, ∀ y ∈ Yb' p, blk p ∈ bodies' ∧ y ∈ (Wsh (blk p)).shade)
    -- the angular bound of `lem:ml2bodyAngle`, uniform over the blocks
    (hangle : ∀ p ∈ segs, ∀ T ∈ fam p, lineAngle (dir T) (ax (blk p)) ≤ ρ)
    {x : E} (hx : x ∈ Pc) :
    ∀ T ∈ I, x ∈ Y' T →
      ∃ j ∈ bodies', x ∈ (Wsh j).shade ∧ x ∈ Yg T ∧ lineAngle (dir T) (ax j) ≤ ρ := by
  intro T hT hxY'
  rcases segmentLocalise I Yg Y' Pc segs fam carr Yb Yb' hY' hparent hinto hYbcarr hfwd hx
      T hT hxY' with ⟨p, hp, hxYb', hTfam⟩
  rcases hT3 p hp x hxYb' with ⟨hblk, hshade⟩
  refine ⟨blk p, hblk, hshade, hY' T hT hxY', hangle p hp T hTfam⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Every shaded point is handled in exactly one piece** (blueprint
`lem:ml2nonslabPiecewise`).

The pieces `B̂`, `B ∈ 𝔅`, of (C2) are pairwise disjoint and cover `U(𝕋, Y)`; since
`Y'(T) ⊆ Y(T)` for every `T`, the union `U(𝕋, Y')` is contained in `U(𝕋, Y)`, so every
shaded point lies in exactly one piece. `Kakeya.NonSlab.compat` then applies in that piece,
with constants that do not depend on it: the only constant occurring is
`C_{lem:ml2bodyAngle}(C₀)`, where the single comparison constant `C₀` and the properties of
Configuration `hyp:ml2thinsetup` are shared by all `B ∈ 𝔅`.

The localisation costs nothing. The pieces are pairwise *disjoint*, so no factor `D` is lost,
in contrast with a covering argument run over the balls `B` themselves, where the `O(D)`
balls containing `x` would each contribute. -/
theorem piecewise {ι bι : Type*} (I : Finset ι) (Yg Y' : ι → Set E) (bs : Finset bι)
    (Pc : bι → Set E) (hdisj : (bs : Set bι).PairwiseDisjoint Pc)
    (hcov : ∀ T ∈ I, Yg T ⊆ ⋃ B ∈ bs, Pc B) (hY' : ∀ T ∈ I, Y' T ⊆ Yg T)
    {x : E} (hx : ∃ T ∈ I, x ∈ Y' T) :
    ∃! B, B ∈ bs ∧ x ∈ Pc B := by
  rcases hx with ⟨T, hTI, hxY'⟩
  have hxYg : x ∈ Yg T := hY' T hTI hxY'
  rcases Set.mem_iUnion₂.mp (hcov T hTI hxYg) with ⟨B, hB, hxB⟩
  exact existsUnique_of_exists_of_unique ⟨B, hB, hxB⟩ (by
    intro B₁ B₂ hB₁ hB₂
    exact hdisj.elim_set hB₁.1 hB₂.1 x hB₁.2 hB₂.2)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open scoped Classical in
/-- **The pointwise product bound** (blueprint `lem:ml2nonslabPointwiseMult`).

Let `B'` be the unique piece containing `x` and read the containment of
`Kakeya.NonSlab.compat` there. The outer union has at most `Mout` terms, because
`(𝕎'_{B'}, Y_{𝕎'_{B'}})` has constant multiplicity by (T4)(a) and the maximising ball `B`
was chosen so that `μ(𝕎'_{B'}, Y_{𝕎'_{B'}}) ≤ μ(𝕎'_B, Y_{𝕎'_B})`; each inner set
`{T ∈ 𝕋_Y(x) : ∠(T, v(W)) ≤ C ρ₂}` has at most `Min` elements by
`Kakeya.VeryNotSticky.angularInnerCount`. Multiplying the two counts gives the bound.

Both losses are independent of `B'`, which is what allows the bound to be stated at the
single maximising ball while the argument is run at the varying ball. -/
theorem pointwiseMult {ι bι ω : Type*} (I : Finset ι) (Y' : ι → ShadedBody E)
    (bs : Finset bι) (Pc : bι → Set E) (bodies' : bι → Finset ω) (Wsh : ω → ShadedBody E)
    (inner : bι → ω → Finset ι) (Mout Min : ℕ)
    (hpiece : ∀ y ∈ iUnionShade I Y', ∃ B ∈ bs, y ∈ Pc B)
    (hcompat : ∀ B ∈ bs, ∀ y ∈ Pc B, ∀ T ∈ I, y ∈ (Y' T).shade →
      ∃ j ∈ bodies' B, y ∈ (Wsh j).shade ∧ T ∈ inner B j)
    (hout : ∀ B ∈ bs, ∀ y : E, pointwiseMultiplicity (bodies' B) Wsh y ≤ Mout)
    (hin : ∀ B ∈ bs, ∀ j ∈ bodies' B, (inner B j).card ≤ Min)
    {x : E} (hx : x ∈ iUnionShade I Y') :
    pointwiseMultiplicity I Y' x ≤ Mout * Min := by
  classical
  rcases hpiece x hx with ⟨B, hB, hxB⟩
  let J : Finset ω := {j ∈ bodies' B | x ∈ (Wsh j).shade}
  have hJ : J.card ≤ Mout := by
    simpa [J] using hout B hB x
  have hsub : {T ∈ I | x ∈ (Y' T).shade} ⊆ J.biUnion (fun j => inner B j) := by
    intro T hT
    rcases (Finset.mem_filter.mp hT) with ⟨hTI, hxT⟩
    rcases hcompat B hB x hxB T hTI hxT with ⟨j, hjB, hjx, hTinn⟩
    refine Finset.mem_biUnion.mpr ⟨j, ?_, hTinn⟩
    simp [J, hjB, hjx]
  calc
    pointwiseMultiplicity I Y' x = {T ∈ I | x ∈ (Y' T).shade}.card := rfl
    _ ≤ (J.biUnion (fun j => inner B j)).card := Finset.card_le_card hsub
    _ ≤ J.card * Min :=
      Finset.card_biUnion_le_card_mul J (fun j => inner B j) Min (by
        intro j hj
        exact hin B hB j (Finset.mem_filter.mp hj).1)
    _ ≤ Mout * Min := Nat.mul_le_mul hJ (le_refl Min)

/-- **Splitting the multiplicity in the non-slab case** (blueprint
`lem:ml2nonslabMultSplit`).

`Kakeya.NonSlab.pointwiseMult` bounds `|𝕋_{Y'}(x)|` by the product of the outer multiplicity
`μ(𝕎'_B, Y_{𝕎'_B})` and the inner multiplicity `μ(𝕋[T_{ρ₂*}], Y)` at every point of
`U(𝕋, Y')`. Taking the supremum over `x` bounds `μ(𝕋, Y')` by the same product, and since
`(𝕋, Y')` is a `⪆ 1` refinement of `(𝕋, Y)` by (T1) the multiplicity of `(𝕋, Y)` is
controlled by that of `(𝕋, Y')`, up to the refinement constant `c⁻¹`. -/
theorem multSplit {ι ω : Type*} (I : Finset ι) (Y Y' : ι → ShadedBody E)
    (bodies' : Finset ω) (Wsh : ω → ShadedBody E) (inn : Finset ι) (Yin : ι → ShadedBody E)
    {c C : NNReal} (hc : 0 < c) (href : ShadedBody.IsCRefinement I Y' I Y c)
    (hpt : ∀ x ∈ iUnionShade I Y', (pointwiseMultiplicity I Y' x : ENNReal) ≤
      (C : ENNReal) * multiplicity bodies' Wsh * multiplicity inn Yin) :
    multiplicity I Y ≤
      (c : ENNReal)⁻¹ * C * multiplicity bodies' Wsh * multiplicity inn Yin := by
  let t : ENNReal := C * multiplicity bodies' Wsh * multiplicity inn Yin
  have hptE : ∀ x ∈ iUnionShade I Y', (pointwiseMultiplicity I Y' x : ENNReal) ≤ t := by
    intro x hx
    simpa [t] using hpt x hx
  have hY' : multiplicity I Y' ≤ t := by
    exact ShadedBody.multiplicity_le_of_pointwiseMultiplicity_le (s := I) (V := Y') hptE
  have hmul : (c : ENNReal) * multiplicity I Y ≤ multiplicity I Y' :=
    ShadedBody.IsCRefinement.mul_multiplicity_le (s' := I) (V' := Y') (s := I) (V := Y) href
  have hcE : (c : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  have hcTop : (c : ENNReal) ≠ ⊤ := ne_of_lt (ENNReal.coe_lt_top : (c : ENNReal) < ⊤)
  have hinv : multiplicity I Y ≤ (c : ENNReal)⁻¹ * multiplicity I Y' := by
    calc
      multiplicity I Y = (c : ENNReal)⁻¹ * ((c : ENNReal) * multiplicity I Y) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcE hcTop, one_mul]
      _ ≤ (c : ENNReal)⁻¹ * multiplicity I Y' := by
        exact mul_le_mul_of_nonneg_left hmul (zero_le : 0 ≤ (c : ENNReal)⁻¹)
  calc
    multiplicity I Y ≤ (c : ENNReal)⁻¹ * multiplicity I Y' := hinv
    _ ≤ (c : ENNReal)⁻¹ * t := by
      exact mul_le_mul_of_nonneg_left hY' (zero_le : 0 ≤ (c : ENNReal)⁻¹)
    _ = (c : ENNReal)⁻¹ * C * multiplicity bodies' Wsh * multiplicity inn Yin := by
      simp [t, mul_assoc]

end Compat

end Kakeya.NonSlab

namespace Kakeya.VeryNotSticky

universe u

open MeasureTheory Metric Set ShadedBody

/-- **The Katz–Tao estimate at the fixed scale `δ`**, as a predicate on the configuration and
the loss `ε` (blueprint Configuration `hyp:ml2scale`, cross-section of Definition `def:KKT`).

`KTScaleData cfg ε` says that `K_KT(β)` may be run on any subfamily of `𝕋` at this `δ` with
loss `δ^{-ε}`, at the density and fullness thresholds `δ^{-η}` and `δ^{2η}` of (C1):

`Δ_max(𝕊) ≤ δ^{-η}` and `λ(𝕊, Y_𝕊) ≥ δ^{2η}` imply `μ(𝕊, Y_𝕊) ≤ δ^{-ε} |𝕊|^β`.

The fullness threshold reads `δ^{2η}` and not `δ^{η}` because that is what the configuration
supplies: `Kakeya.VeryNotSticky.fullness_ge` is asserted at `δ^{2η}` (at `δ^{η}` it was rigid —
see that field), and `Kakeya.VeryNotSticky.exists_full_fibre` transports exactly that to the
fibre. Weakening the *antecedent* makes this predicate **stronger**, and it stays available:
`Kakeya.VeryNotSticky.ktScaleData_of_le` produces it from `Kakeya.KatzTaoEstimate.generalize`
at any exponent threshold `η₁ ≥ 2η`, and `η₁` belongs to the pair `(ε, β)` and is therefore
fixed after `η`.

This is exactly the conclusion of `Kakeya.KatzTaoEstimate.generalize` applied to
`cfg.ktEstimate` at `ε`, read at `τ = δ`, and it carries no `Δ_max^{1-β}` factor and no upper
bound on `β`: those belong to `Kakeya.KatzTaoEstimate.multiplicity_bound` (blueprint
`genKKT`), the variant valid for an arbitrary `Δ_max`, which is not what the blueprint proof
of `lem:ml2nonslabKKT` uses.

Being a predicate rather than a direct application of `cfg.ktEstimate` is forced by the shape
of `Kakeya.KatzTaoEstimate`: that definition holds only *eventually* in `δ`, and the exponent
`η'` it produces for a given `ε` is existentially bound. `KTScaleData cfg ε` is the fixed-`δ`
cross-section, obtained once `δ` is below the threshold belonging to `ε` and `cfg.η ≤ η'`,
which is the blueprint's `η ≪ ϱ`. It plays for `def:KKT` the role that
`Kakeya.VeryNotSticky.AScaleData` plays for the scale-`a` estimates. -/
def KTScaleData (cfg : VeryNotSticky.{u}) (ε : ℝ) : Prop :=
  ∀ s' : Finset cfg.ι, s' ⊆ cfg.s →
    ConvexSpaceBody.IsKatzTao s' (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-cfg.η)) →
    ShadedBody.fullness s' (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η) →
    multiplicity s' (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-ε) * (s'.card : ENNReal) ^ cfg.β

/-- **Availability of `K_KT(β)` at the scale `δ`** (blueprint `lem:ml2ktScaleDataAvail`).

`Kakeya.VeryNotSticky.KTScaleData` is the cross-section of `Kakeya.KatzTaoEstimate` at the
single scale that the configuration fixes, so it becomes available once `δ` is below the
scale threshold `δ₀(ε, β)` and `2η` is below the exponent threshold `η₁(ε, β)` that
`Kakeya.KatzTaoEstimate.generalize` attaches to the pair `(ε, β)`.

Both thresholds are existentially bound in `Kakeya.KatzTaoEstimate`, so they are carried here
as explicit data rather than as inequalities: `hδ₀` *is* the statement that the eventual
conclusion of `KatzTaoEstimate.generalize` at `(ε, η₁)` already holds at this `δ` — that is,
`δ ≤ δ₀(ε, β)` — and `hη` is `2η ≤ η₁(ε, β)`.

The proof is monotonicity plus one degenerate case. Since `0 < δ ≤ 1` the map `s ↦ δ^s` is
antitone, so `2η ≤ η₁` turns the two thresholds of `KTScaleData` into those at `η₁`;
and the empty subfamily is handled separately, both sides of the conclusion vanishing because
`β > 0`. That clause is why `KTScaleData` carries no nonemptiness restriction, unlike
`Kakeya.KatzTaoEstimate` itself. -/
theorem ktScaleData_of_le (cfg : VeryNotSticky.{u})
    {ε η₁ : ℝ} (hη : 2 * cfg.η ≤ η₁)
    (hδ₀ : ∀ (s' : Finset cfg.ι) (T' : cfg.ι → ShadedTube cfg.δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s' (fun i ↦ (T' i).toConvexSpaceBody)
        ((cfg.δ : ENNReal) ^ (-η₁)) →
      ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) ≥ cfg.δ ^ η₁ →
      multiplicity s' (fun i ↦ (T' i).toShadedBody) ≤
        (cfg.δ : ENNReal) ^ (-ε) * (s'.card : ENNReal) ^ cfg.β) :
    cfg.KTScaleData ε := by
  intro s' hs' hKT hfull
  have hcont : ∀ i ∈ s', (cfg.T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => cfg.contained i (hs' hi)
  -- the `Δ_max` half of the transport needs only `η ≤ η₁`, which `hη` implies since `η > 0`
  have hη1 : cfg.η ≤ η₁ := le_trans (by linarith [cfg.hη]) hη
  have hKT' : ConvexSpaceBody.IsKatzTao s' (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-η₁)) :=
    ConvexSpaceBody.IsKatzTao.mono hKT
      (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast cfg.hδ1) (neg_le_neg hη1))
  have hfull' : ShadedBody.fullness s' (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ η₁ :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 hη) hfull
  exact hδ₀ s' cfg.T hcont hKT' hfull'

/-- **Katz–Tao bound for the inner factor** (blueprint `lem:ml2nonslabKKT`).

Here `sub` is the subfamily `𝕋[T_{ρ₂*}]` of the tubes of `𝕋` inside a fixed `ρ₂*`-tube. The
conclusion is `K_KT(β)` applied to `𝕋[T_{ρ₂*}]` with `ϱ` in place of `ε`, i.e.
`cfg.ktEstimate` read at this `δ` through `Kakeya.VeryNotSticky.KTScaleData`. Its two
hypotheses are (C1) at the subfamily: `Δ_max(𝕋[T_{ρ₂*}]) ≤ Δ_max(𝕋) ≤ δ^{-η}` is `hsub`
together with `cfg.maxDensity_le` and `ConvexSpaceBody.IsKatzTao.subset`, while `hfull`
is a genuine hypothesis, fullness not being inherited by subfamilies. There is no
`Δ_max^{1-β}` factor to absorb, so the loss is `δ^{-ϱ}` and not `δ^{-(ϱ+η)}`, and no upper
bound on `β` is needed; the `+η` and the hypothesis `β ≤ 1` enter one step later, in
`Kakeya.VeryNotSticky.nonslabKKTPow`.

The counting bound `|𝕋[T_{ρ₂*}]| ≤ K · Ccnt · ρ₂^{2+ζ} |𝕋|`, the second display of the
blueprint statement, is a logically independent conclusion with no Katz–Tao content, and is
stated separately as `Kakeya.VeryNotSticky.nonslabFibreCount`, whose count constant `Ccnt` is a
parameter (it was the δ-free `(2 C_{lem:ml2bodyAngle}(C₀))²`
before it); consumers that need both invoke both. -/
theorem nonslabKKT (cfg : VeryNotSticky)
    (hKT : cfg.KTScaleData cfg.ϱ)
    {sub : Finset cfg.ι} (hsub : sub ⊆ cfg.s)
    (hfull : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η)) :
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-cfg.ϱ) * (sub.card : ENNReal) ^ cfg.β :=
  hKT sub hsub
    (ConvexSpaceBody.IsKatzTao.subset
      ((ConvexSpaceBody.IsKatzTao_def cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)).mpr
        cfg.maxDensity_le) hsub) hfull

/-- **Positivity of the angular scale `ρ₂`.**

`ρ₂ = b / r₁` with `0 < δ ≤ a ≤ b` and `r₁ = δ^{exscal} > 0`, so `ρ₂ > 0`. This is the side
condition of `Kakeya.VeryNotSticky.nonslabFibreCount`, read off from the configuration. -/
theorem rho2_pos (cfg : VeryNotSticky) : 0 < cfg.rho2 := by
  have hb_pos : 0 < cfg.b :=
    lt_of_lt_of_le (lt_of_lt_of_le cfg.hδ cfg.hdims.1) cfg.hdims.2.1
  have hr₁ : 0 < cfg.r₁ := by
    simpa [r₁] using NNReal.rpow_pos cfg.hδ
  rw [rho2]
  exact div_pos hb_pos hr₁

/-- **The Katz–Tao bound in powered form** (blueprint `lem:ml2nonslabKKTPow`).

The form of `Kakeya.VeryNotSticky.nonslabKKT` that the splitting actually consumes: the
counting bound is raised to the `β`-th power and substituted into the multiplicity bound, so
that the inner factor is expressed directly against `ρ₂^{2+ζ}|𝕋|`.

This is where `hβ1 : β ≤ 1` is spent, and it is the only place in the non-slab chain that
spends it: raising `|𝕋[T_{ρ₂*}]| ≤ K Ccnt ρ₂^{2+ζ}|𝕋|` to the `β`-th power costs
`(K Ccnt)^β`, and `(K Ccnt)^β ≤ (δ^{-Mη})^β = δ^{-Mηβ} ≤ δ^{-Mη}` by `hCδ` together with
`β ≤ 1`, `0 ≤ M` and `δ ≤ 1`. That loss is then carried into `δ^{-(ϱ + Mη)}`, which is where
the `+Mη` of the conclusion comes from; neither conclusion of `nonslabKKT` carries it.

`K` is the constant of the fibre count `hfib : |𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ K |𝕋|` — `Cu²` for
the hierarchy constant `Cu` of `Tube.UniformTubeSet`, as `Kakeya.VeryNotSticky.SplitInputs`
carries it (GWZ Def 2.1(iii) reads "constant up to a factor `∼ 1`",
`gwz.txt` l.183, so the exact-branching `K = 1` was over-strong). `Ccnt` is the constant of the
count hypothesis `hcount`, and `M` the exponent of the joint threshold; both are **parameters**, which forbids baking a numeral into this lemma. The numerals
live at the call sites: `M = 19` at `Kakeya.VeryNotSticky.nonslabSplitBound`, where
`K = Cu²` costs `δ^{-η}` through `Kakeya.VeryNotSticky.SplitInputs.fibreConstant` and
`Ccnt` costs `δ^{-18η}` through `Kakeya.VeryNotSticky.SplitInputs.countConstant` ( (c) measured the `+1`), and `M = 1` at
`Kakeya.KKTResidual.nonslabKKTPow_of_fibreKTData`, whose datum still fixes
`Ccnt = (2 C_{lem:ml2bodyAngle}(C₀))²`.

That absorption is the hypothesis `hCδ`, blueprint `fibreConstantThreshold`. It is a genuine
extra assumption, not a consequence of the others: without it the statement is false, as
`δ = 1` shows. It is a fixed-scale threshold of the same kind as the four fields of
`Kakeya.VeryNotSticky.CaseScale`, satisfied once `δ` is small with `C₀`, `K` and `η` fixed
first, but it is not one of them, and it does not follow from `scale.rho2Star_le_one` together
with `2η < exscal`: that bounds `2 C_{lem:ml2bodyAngle}(C₀) δ^{exscal}` and says nothing about
`C_{lem:ml2bodyAngle}(C₀)²` on its own. -/
theorem nonslabKKTPow (cfg : VeryNotSticky) (hβ1 : cfg.β ≤ 1)
    (hKT : cfg.KTScaleData cfg.ϱ)
    {K Ccnt : NNReal} {M : ℝ} (hM : 0 ≤ M)
    (hCδ : (K : ENNReal) * (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(M * cfg.η)))
    {sub : Finset cfg.ι} (hsub : sub ⊆ cfg.s)
    (hfull : ShadedBody.fullness sub (fun i ↦ (cfg.T i).toShadedBody) ≥ cfg.δ ^ (2 * cfg.η))
    (N : ℕ) (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (K : ℝ) * (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * (N : ℝ)) :
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + M * cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
  have hmult := nonslabKKT cfg hKT hsub hfull
  have hcard := nonslabFibreCount cfg (rho2_pos cfg) N hfib hcount
  have hpow := nonslabFibreCountPow cfg hβ1 hM hCδ hcard
  have hδne0 : (cfg.δ : ENNReal) ≠ 0 := by
    exact_mod_cast ne_of_gt cfg.hδ
  have hδneTop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hexp : (cfg.δ : ENNReal) ^ (-(M * cfg.η)) * (cfg.δ : ENNReal) ^ (-cfg.ϱ) =
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + M * cfg.η)) := by
    rw [← ENNReal.rpow_add (-(M * cfg.η)) (-cfg.ϱ) hδne0 hδneTop]
    congr
    ring
  calc
    multiplicity sub (fun i ↦ (cfg.T i).toShadedBody) ≤
        (cfg.δ : ENNReal) ^ (-cfg.ϱ) * (sub.card : ENNReal) ^ cfg.β := by
      exact hmult
    _ = (sub.card : ENNReal) ^ cfg.β * (cfg.δ : ENNReal) ^ (-cfg.ϱ) := by
      rw [mul_comm]
    _ ≤ ((cfg.δ : ENNReal) ^ (-(M * cfg.η)) *
          ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β) *
          (cfg.δ : ENNReal) ^ (-cfg.ϱ) := by
      exact mul_le_mul_left hpow _
    _ = (cfg.δ : ENNReal) ^ (-(cfg.ϱ + M * cfg.η)) *
          ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
      have hre : (cfg.δ : ENNReal) ^ (-(M * cfg.η)) *
            ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β *
            (cfg.δ : ENNReal) ^ (-cfg.ϱ) =
          (cfg.δ : ENNReal) ^ (-(cfg.ϱ + M * cfg.η)) *
            ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
        rw [mul_right_comm, hexp]
      exact hre

/-! ### The angular input of the compatible refinement -/

/-- **The non-slab hypothesis in the shape the angular range lemmas want.**

`Kakeya.VeryNotSticky.nonslabSplitBound` receives the non-slab hypothesis as
`b ≤ δ^{2 exscal}`, the shape `Kakeya.VeryNotSticky.CaseScale.body_fits_ball` is stated in,
whereas `Kakeya.VeryNotSticky.rho2_range` and `Kakeya.VeryNotSticky.rho2Star_range` want
`b ≤ δ^{exscal} r₁`. Since `r₁ = δ^{exscal}` the two are the same bound, `δ^{exscal} δ^{exscal}
= δ^{2 exscal}`; only the `NNReal.rpow` bookkeeping differs. -/
theorem b_le_pow_mul_r₁ (cfg : VeryNotSticky) (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal)) :
    cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
  change cfg.b ≤ cfg.δ ^ cfg.exscal * (cfg.δ ^ cfg.exscal)
  rw [← NNReal.rpow_add (ne_of_gt cfg.hδ) cfg.exscal cfg.exscal]
  rw [← two_mul cfg.exscal]
  exact hnotslab

/-- **The thin-case refinement constant is below the fixed-scale threshold.**

The seventh clause `Kakeya.VeryNotSticky.CaseScale.transverse_ballFill` of Configuration
`hyp:ml2scale` reads `1000 · C_transfer(C, C₀) ≤ δ^{-η}` in `NNReal`, and
`Kakeya.ThinCase.transferConstant C C₀` dominates `C` once `1 ≤ C` and `1 ≤ C₀`. This is that
clause read in `ENNReal`, which is where `Kakeya.VeryNotSticky.tangentialSlabMultAbsorb`
consumes it. -/
theorem thinConstant_le (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {B : bd.bι} (hB : B ∈ bd.bs) {τ τ' νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr) :
    (tc.C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have hC1 : (1 : NNReal) ≤ tc.C := (tc.thinBall hB).one_le_C
  have hw1b : (0 : NNReal) ≤ ThinCase.w1Constant bd.C₀ := zero_le
  have h1w : (1 : NNReal) ≤ 1 + ThinCase.w1Constant bd.C₀ := by
    exact le_add_of_nonneg_right hw1b
  have hw1 : (1 : NNReal) ≤ (1 + ThinCase.w1Constant bd.C₀) ^ 3 := by
    simpa using (pow_le_pow_left₀ (zero_le : (0 : NNReal) ≤ 1) h1w 3)
  have hCsq : (1 : NNReal) ≤ tc.C ^ 2 := by
    simpa using (pow_le_pow_left₀ (zero_le : (0 : NNReal) ≤ 1) hC1 2)
  have hbig : (1 : NNReal) ≤ 2 ^ 12 * tc.C ^ 2 := by
    calc
      (1 : NNReal) ≤ 2 ^ 12 := by norm_num
      _ = 2 ^ 12 * 1 := by ring
      _ ≤ 2 ^ 12 * tc.C ^ 2 := mul_le_mul_of_nonneg_left hCsq (by positivity)
  have hC2 : tc.C ≤ 2 ^ 12 * tc.C ^ 3 := by
    calc
      tc.C = tc.C * 1 := by ring
      _ ≤ tc.C * (2 ^ 12 * tc.C ^ 2) :=
        mul_le_mul_of_nonneg_left hbig (zero_le : (0 : NNReal) ≤ tc.C)
      _ = 2 ^ 12 * tc.C ^ 3 := by ring
  have hupper : 2 ^ 12 * tc.C ^ 3 ≤ ThinCase.netUpperConstant tc.C bd.C₀ := by
    calc
      2 ^ 12 * tc.C ^ 3 = (2 ^ 12 * tc.C ^ 3) * 1 := by ring
      _ ≤ (2 ^ 12 * tc.C ^ 3) * (1 + ThinCase.w1Constant bd.C₀) ^ 3 :=
        mul_le_mul_of_nonneg_left hw1 (by positivity)
      _ = 2 ^ 12 * tc.C ^ 3 * (1 + ThinCase.w1Constant bd.C₀) ^ 3 := by ring
      _ ≤ ThinCase.netUpperConstant tc.C bd.C₀ := le_max_right _ _
  have hCnet : tc.C ≤ ThinCase.netUpperConstant tc.C bd.C₀ := le_trans hC2 hupper
  have hnu_le_tr :
      ThinCase.netUpperConstant tc.C bd.C₀ ≤ ThinCase.transferConstant tc.C bd.C₀ := by
    rw [ThinCase.transferConstant]
    calc
      ThinCase.netUpperConstant tc.C bd.C₀ = ThinCase.netUpperConstant tc.C bd.C₀ * 1 := by ring
      _ ≤ ThinCase.netUpperConstant tc.C bd.C₀ * (2 ^ 3 : NNReal) :=
        mul_le_mul_of_nonneg_left (by norm_num : (1 : NNReal) ≤ (2 ^ 3 : NNReal))
          (zero_le : (0 : NNReal) ≤ ThinCase.netUpperConstant tc.C bd.C₀)
      _ ≤ (ThinCase.netUpperConstant tc.C bd.C₀ * (2 ^ 3 : NNReal)) *
            ThinCase.netLowerConstant tc.C := by
        simpa using
          mul_le_mul_of_nonneg_left (ThinCase.one_le_netLowerConstant tc.C)
            (zero_le : (0 : NNReal) ≤
              ThinCase.netUpperConstant tc.C bd.C₀ * (2 ^ 3 : NNReal))
      _ = (2 ^ 3 : NNReal) * ThinCase.netUpperConstant tc.C bd.C₀ *
            ThinCase.netLowerConstant tc.C := by ring
  have hCdom : tc.C ≤ 1000 * ThinCase.transferConstant tc.C bd.C₀ := by
    calc
      tc.C ≤ ThinCase.netUpperConstant tc.C bd.C₀ := hCnet
      _ ≤ ThinCase.transferConstant tc.C bd.C₀ := hnu_le_tr
      _ ≤ 1000 * ThinCase.transferConstant tc.C bd.C₀ := by
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (by norm_num : (1 : NNReal) ≤ (1000 : NNReal))
            (zero_le : (0 : NNReal) ≤ ThinCase.transferConstant tc.C bd.C₀)
  have hC : tc.C ≤ cfg.δ ^ (-cfg.η) := le_trans hCdom scale.transverse_ballFill
  calc
    (tc.C : ENNReal) ≤ ((cfg.δ ^ (-cfg.η) : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hC
    _ = (cfg.δ : ENNReal) ^ (-cfg.η) := ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' _

/-- **The angle between a tube and the axis of its factoring body**, at the configuration
(blueprint `lem:ml2bodyAngle`).

Let `T_B ∈ 𝕋_B` be a segment in the ball `B` and let `T ∈ 𝕋(T_B)` be one of its parent tubes.
By (C3) the segment is an `r₁ × δ × δ` body lying within `C₀δ` of the core line of `T`, and by
(C4) it lies in the factoring body `W = W(T_B)`, an `r₁ × b × a` body. So
`Kakeya.NonSlab.lineAngle_bodyAxis_le` applies and gives
`∠(T, v(W)) ≤ C_{lem:ml2bodyAngle}(C₀) · b/r₁ = C_{lem:ml2bodyAngle}(C₀) ρ₂ = ρ₂*/2`.

The factor `1/2` in the statement is not cosmetic: `Kakeya.VeryNotSticky.angularInnerCount`
doubles the angle when it passes from the axis `v(W)` to a *tube* through the point, and it is
the doubled angle that must be `ρ₂*`. That is exactly how `ρ₂*` is defined. -/
theorem segAngle (cfg : VeryNotSticky.{u}) {bd : BallData cfg} {B : bd.bι} (hB : B ∈ bd.bs)
    {p : bd.σ} (hp : p ∈ bd.segs B) {i : cfg.ι} (hi : i ∈ bd.fam p) :
    NonSlab.lineAngle (cfg.T i).direction (bodyAxis (bd.Wb (bd.blk p))) ≤
      (cfg.rho2Star bd.C₀ : ℝ) / 2 := by
  have hbr₁ : cfg.b ≤ cfg.r₁ := by
    simpa [r₁] using cfg.hdims.2.2
  rcases bd.segs_core B hB p hp i hi with ⟨q, hST⟩
  have hu : ‖(cfg.T i).direction‖ = 1 := (cfg.T i).norm_direction
  have hSW : (bd.Y p).carrier ⊆ (bd.Wb (bd.blk p)).carrier := by
    exact SetLike.coe_subset_coe.mpr (bd.segs_le B hB p hp)
  calc
    NonSlab.lineAngle (cfg.T i).direction (bodyAxis (bd.Wb (bd.blk p))) ≤
        (NonSlab.bodyAngleConstant bd.C₀ : ℝ) * ((cfg.b : ℝ) / (cfg.r₁ : ℝ)) := by
      exact NonSlab.lineAngle_bodyAxis_le (E := EuclideanSpace ℝ (Fin 3)) (C₀ := bd.C₀)
        (δ := cfg.δ) (a := cfg.a) (b := cfg.b) (r₁ := cfg.r₁) (S := (bd.Y p).carrier)
        (p := q) (u := (cfg.T i).direction)
        finrank_euclideanSpace_fin bd.hC₀ cfg.hδ
        cfg.hdims.1 cfg.hdims.2.1 hbr₁ (bd.Wb (bd.blk p))
        (bd.bodies_thickness B hB (bd.blk p) (bd.blk_mem B hB p hp))
        hSW
        (bd.segs_thickness B hB p hp) hu (by simpa using hST)
    _ = (cfg.rho2Star bd.C₀ : ℝ) / 2 := by
      simp [rho2Star, rho2, NNReal.coe_div, NNReal.coe_mul]
      ring

/-- **The compatible refinement at a piece of the partition** (blueprint
`lem:ml2nonslabCompat`, at the configuration).

`Kakeya.NonSlab.compat` instantiated at the ball `B`, with the working shading `Yg := bd.Yg`: its six set-theoretic hypotheses are the fields
`Kakeya.VeryNotSticky.ThinConfig.Y'_subset`, `Kakeya.VeryNotSticky.BallData.parent`,
`Kakeya.VeryNotSticky.BallData.into`, the carrier containment of `bd.Y p`,
`Kakeya.VeryNotSticky.ThinConfig.compat_forward` and
`Kakeya.ThinCase.ThinBall.shade_containment`; its angular hypothesis is
`Kakeya.VeryNotSticky.segAngle`. The conclusion is repackaged as membership in
`Kakeya.VeryNotSticky.angularFibre`, which is the form the counting step consumes; the point
lies in `Y_g(T) ⊆ Y(T)` by `Kakeya.VeryNotSticky.BallData.Yg_subset`. -/
theorem nonslabCompatAt (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (tc : ThinConfig cfg bd)
    {B : bd.bι} (hB : B ∈ bd.bs) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ bd.P B) :
    ∀ i ∈ cfg.s, x ∈ tc.Y' i →
      ∃ j ∈ (tc.thinBall hB).bodies', x ∈ ((tc.thinBall hB).W j).shade ∧
        i ∈ cfg.angularFibre x (bodyAxis (bd.Wb j)) ((cfg.rho2Star bd.C₀ : ℝ) / 2) := by
  classical
  intro i hi hxY'
  rcases Kakeya.NonSlab.compat (I := cfg.s) (Yg := bd.Yg)
      (Y' := tc.Y') (dir := fun i ↦ (cfg.T i).direction) (Pc := bd.P B)
      (segs := bd.segs B) (fam := bd.fam) (carr := fun p ↦ (bd.Y p).carrier)
      (Yb := fun p ↦ (bd.Y p).shade) (Yb' := fun p ↦ ((tc.thinBall hB).Y' p).shade)
      (blk := bd.blk) (bodies' := (tc.thinBall hB).bodies') (Wsh := (tc.thinBall hB).W)
      (ax := fun j ↦ bodyAxis (bd.Wb j)) (ρ := (cfg.rho2Star bd.C₀ : ℝ) / 2)
      tc.Y'_subset (bd.parent B hB) (bd.into B hB)
      (fun p _ ↦ (bd.Y p).shade_subset) (tc.compat_forward B hB)
      ((tc.thinBall hB).shade_containment)
      (fun p hp i' hi' ↦ segAngle cfg hB hp hi') hx i hi hxY' with
    ⟨j, hj, hshade, hxYg, hangle⟩
  refine ⟨j, hj, hshade, ?_⟩
  rw [angularFibre]
  exact Finset.mem_filter.mpr ⟨hi, bd.Yg_subset i hi hxYg, hangle⟩

/-- **The pointwise product bound at the maximising ball** (blueprint
`lem:ml2nonslabPointwiseMult`).

Let `B'` be the piece of the subordinate partition of (C2) containing `x`, which exists by
`Kakeya.VeryNotSticky.BallData.P_cover` (on the working shading `Y_g ⊇ Y'`). Reading
`Kakeya.VeryNotSticky.nonslabCompatAt` there
places every tube of `𝕋_{Y'}(x)` in one of the angular fibres
`{T ∈ 𝕋_Y(x) : ∠(T, v(W)) ≤ ρ₂*/2}`, indexed by the bodies `W ∈ 𝕎'_{B'}` shading `x`. There
are at most `C μ(𝕎'_{B'}, Y_{𝕎'_{B'}}) ≤ C μ(𝕎'_B, Y_{𝕎'_B})` such bodies — the first step by
(T4)(a) and `Kakeya.ShadedBody.pointwiseMultiplicity_le_mul_multiplicity`, the second by the
maximality of `B` — and each fibre, being contained in the angular fibre at the full radius
`ρ₂*`, has at most `A` elements by the hypothesis `hang`. Multiplying the two counts gives the
bound.

`hang` is GWZ's "the cardinality of the inner set is `⪅ μ(ρ₂)`" (`gwz.txt` l.2321), taken as a
bound on the inner angular count at *every* point and direction; the splitting supplies it from
the field `Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult` at the selected node,
with `A = Cang · μ(𝕋[T_{ρ₂*}], Y)` (the separate angular formulation took the angular
multiplicity function `μ(ρ)` of GWZ's step 1, through
`Kakeya.VeryNotSticky.angularFibre_card_le_mul_mu`, as the intermediary). The range binders
`δ ≤ ρ₂* ≤ 1`, which placed `ρ₂*` in the domain of `μ`, are received in lockstep with
`Kakeya.VeryNotSticky.nonslabSplitBound` for the statement's shape only and are not used.

Both losses are independent of `B'`, which is what allows the bound to be stated at the single
maximising ball while the argument runs at the varying ball. -/
theorem nonslabPointwiseBound (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ B' (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {A : ENNReal}
    (hang : ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤ A)
    (_hδρ : (cfg.δ : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ))
    (_hρ1 : (cfg.rho2Star bd.C₀ : ℝ) ≤ 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ShadedBody.iUnionShade cfg.s tc.Y'Body) :
    (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
      ((tc.C : ENNReal) *
          ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W) * A := by
  classical
  rcases Set.mem_iUnion₂.mp hx with ⟨i₀, hi₀s, hxi₀⟩
  rw [ThinConfig.Y'Body_shade tc hi₀s] at hxi₀
  have hxTi₀ : x ∈ bd.Yg i₀ := tc.Y'_subset i₀ hi₀s hxi₀
  rcases Set.mem_iUnion₂.mp (bd.P_cover i₀ hi₀s hxTi₀) with ⟨B', hB', hxB'⟩
  let tb' : ThinCase.ThinBall tc.C bd.C₀ (bd.segs B') bd.Y (bd.bodies B') bd.Wb bd.blk
      cfg.δ cfg.a (2 * cfg.η) := tc.thinBall hB'
  let ρ : ℝ := (cfg.rho2Star bd.C₀ : ℝ) / 2
  let f : bd.ω → Finset cfg.ι := fun j => cfg.angularFibre x (bodyAxis (bd.Wb j)) ρ
  let J : Finset bd.ω := {j ∈ tb'.bodies' | x ∈ (tb'.W j).shade}
  let M : ENNReal := ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
  have hcompat : ∀ i ∈ cfg.s, x ∈ tc.Y' i →
      ∃ j ∈ tb'.bodies', x ∈ (tb'.W j).shade ∧ i ∈ f j := by
    intro i hi hxi
    rcases nonslabCompatAt cfg tc hB' hxB' i hi hxi with ⟨j, hj, hjx, hij⟩
    exact ⟨j, hj, hjx, hij⟩
  have hsub : {i ∈ cfg.s | x ∈ (tc.Y'Body i).shade} ⊆ J.biUnion f := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi₀s, hxi₀⟩
    rw [ThinConfig.Y'Body_shade tc hi₀s] at hxi₀
    rcases hcompat i hi₀s hxi₀ with ⟨j, hj, hjx, hij⟩
    refine Finset.mem_biUnion.mpr ⟨j, ?_, hij⟩
    simp [J, Finset.mem_filter, hj, hjx]
  -- the half-radius fibre sits inside the angular fibre at the full radius `ρ₂*`
  have hρle : ρ ≤ (cfg.rho2Star bd.C₀ : ℝ) := by
    have h0 : (0 : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ) := NNReal.coe_nonneg _
    dsimp [ρ]
    linarith
  have hfsub : ∀ j, f j ⊆ cfg.angularFibre x (bodyAxis (bd.Wb j)) (cfg.rho2Star bd.C₀ : ℝ) := by
    intro j i hi
    change i ∈ cfg.angularFibre x (bodyAxis (bd.Wb j)) ρ at hi
    rw [angularFibre] at hi ⊢
    rcases Finset.mem_filter.mp hi with ⟨his, hxi, hiang⟩
    exact Finset.mem_filter.mpr ⟨his, hxi, hiang.trans hρle⟩
  have hinnerE : ∀ j ∈ J, ((f j).card : ENNReal) ≤ A := by
    intro j _
    calc
      ((f j).card : ENNReal)
          ≤ (((cfg.angularFibre x (bodyAxis (bd.Wb j)) (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) :
              ENNReal) := by
            exact_mod_cast Finset.card_le_card (hfsub j)
      _ ≤ A := hang x (bodyAxis (bd.Wb j))
  have hsumE : (∑ j ∈ J, ((f j).card : ENNReal)) ≤ (J.card : ENNReal) * A := by
    calc
      (∑ j ∈ J, ((f j).card : ENNReal)) ≤ (∑ _j ∈ J, A) := Finset.sum_le_sum hinnerE
      _ = (J.card : ENNReal) * A := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hptw : (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
      (J.card : ENNReal) * A := by
    calc
      (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal)
          ≤ (((J.biUnion f).card : ℕ) : ENNReal) := by
            exact_mod_cast (Finset.card_le_card hsub)
      _ ≤ ((∑ j ∈ J, (f j).card : ℕ) : ENNReal) := by
            exact_mod_cast (Finset.card_biUnion_le (s := J) (t := f))
      _ = (∑ j ∈ J, ((f j).card : ENNReal)) := by
            simp [Nat.cast_sum]
      _ ≤ (J.card : ENNReal) * A := hsumE
  have hC : 0 < tc.C := lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) tb'.one_le_C
  have hrefl : ShadedBody.IsCRefinement tb'.bodies' tb'.W tb'.bodies' tb'.W 1 := by
    refine ⟨?_, ?_⟩
    · exact ⟨Finset.Subset.rfl, fun i _ => ⟨rfl, Set.Subset.rfl⟩⟩
    · simp
  have hne : volume (ShadedBody.iUnionShade tb'.bodies' tb'.W) ≠ 0 :=
    (thinBallPositivity_iUnionShade_pos cfg tc hB' zero_lt_one hrefl).ne'
  have hJcard : (J.card : ENNReal) ≤ (tc.C : ENNReal) * M := by
    calc
      (J.card : ENNReal)
          = (ShadedBody.pointwiseMultiplicity tb'.bodies' tb'.W x : ENNReal) := by simp [J]
      _ ≤ (tc.C : ENNReal) * ShadedBody.multiplicity tb'.bodies' tb'.W := by
            exact pointwiseMultiplicity_le_mul_multiplicity tb'.bodies' tb'.W hC hne
              tb'.constMult_bodies x
      _ ≤ (tc.C : ENNReal) * M := by
            exact mul_le_mul_of_nonneg_left (by simpa [tb', M] using hBmax B' hB')
              (zero_le : 0 ≤ (tc.C : ENNReal))
  calc
    (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
        (J.card : ENNReal) * A := hptw
    _ ≤ ((tc.C : ENNReal) * M) * A := by
          exact mul_le_mul_of_nonneg_right hJcard (zero_le : 0 ≤ A)

/-! ### The splitting bound at one ball, packaged -/

/-- **Input of the non-slab splitting at the ball `B`** (blueprint
`lem:ml2tangentialSplit`(i)–(iii), i.e. `lem:ml2tangential`(c)).

These are the hypotheses that `Kakeya.VeryNotSticky.nonslabKKT` and
`Kakeya.VeryNotSticky.nonslabKKTPow` do not discharge for themselves and that nothing in the
non-slab case discharges either. They mention neither the ball `B` nor the angle `θ`, which
is why they form a bundle over `cfg` and `bd` alone.

* `katzTao` is item (i), the availability of `K_KT(β)` at this fixed `δ` with loss `ϱ` — the
  cross-section that blueprint `lem:ml2ktScaleDataAvail` produces from `δ ≤ δ₀(ϱ, β)` and
  `η ≤ η₁(ϱ, β)`. It is not derivable from `cfg.ktEstimate`, which holds only eventually in
  `δ`, and it is not implied by `Kakeya.VeryNotSticky.CaseParams`.
* `fibreConstant` is item (ii), blueprint `fibreConstantThreshold`: the hypothesis of
  `Kakeya.VeryNotSticky.nonslabKKTPow`, the sole source of the `+η` in `muTTRhoPow`, which
  `δ = 1` falsifies. It also absorbs the hierarchy constant `Cu²`
  of `fibreCount` as well.
* `N`, `Cu`, `uniform`, `k`, `k_le`, `gridScale_ge`, `gridScale_le`, `fibreCount` and
  `fibreScaleCount` **replace** item (iii) of the blueprint statement. Where the blueprint
  assumes the exact fibre count `exactFibreCount` at every `T_{ρ₂*} ∈ 𝕋_{ρ₂*}`, the Lean form
  assumes a uniform hierarchy for `(𝕋, Y)` with a grid level `k` sitting at the dilated scale
  `ρ₂*` up to the grid rounding `δ^{-η}`: its
  assignment classes structurally partition the leaf family, so a *full* fibre can be selected
  without assuming the count. This is a deliberate divergence, recorded in the blueprint
  statement of `lem:ml2tangentialSplit`; `fibreScaleCount` is the price it costs, and
  `fibreCount` is, at its constant `Cu²`, a consequence of `uniform`
  (`Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le`) kept as a field for the
  interface; both are described on the fields themselves.

**The angular clause.** `Cang`, `angularConstant` and `angularFibre_le_fibreMult` carry GWZ's
composed bound at `gwz.txt` l.2321-2322 — "the cardinality of the inner set is `⪅ μ(ρ₂) ≈
μ(𝕋[T_{ρ₂}], Y)`" — at this configuration: the inner angular count at every point and
direction is at most `Cang` times the multiplicity of the fibre of any active node at the
level `k`, with a fixed-scale threshold on `Cang`. The angular multiplicity function `μ(ρ)` of
GWZ's step 1 (blueprint `defmurho`, `lem:ml2murho`), through which GWZ derive that bound, is
not recorded here: GWZ assert (86) on a shading that is not the uniform one and use only this
consequence. See the fields themselves.

**Why the hierarchy is not required to be the one `cfg` already carries — and why it may be.** `cfg.uniform` asserts the existence of a
`ShadedTube.ShadedUniformTubeSet` for `(𝕋, Y)` at the *fixed* grid length
`Tube.ssfGridLen δ = ⌈log log (1/δ)⌉`, that being the grid the sticky/non-sticky
dichotomy of Section 3 runs on. Its levels sit at the scales `δ^{k/⌈log log (1/δ)⌉}`, and
`ρ₂* = 2 C_{lem:ml2bodyAngle}(C₀) b / r₁` is determined by the configuration's dimensions and
by `C₀`; nothing makes it one of those finitely many scales, so an *exact* level at `ρ₂*` —
the field's earlier form, `gridScale_eq : Tube.gridScale cfg.δ N k = cfg.rho2Star bd.C₀` —
would have been unsatisfiable at `N = ssfGridLen δ`, which is why `N` was left free. That
exactness was over-strong against the source: GWZ have the hierarchy only at the grid scales
`δ^{k/M}` (Def 2.1, `gwz.txt` l.177-181) and at every other `ρ ∈ [δ, 1]` only up to `≈` (the
remark after Def 2.2, l.190-195), and they write the same rounding out for the transverse
radius, `θb ≤ r ≤ δ^{-η} θb` (l.2253-2255). The fields `gridScale_ge` and `gridScale_le`
therefore pin the level `k` to `ρ₂*` *two-sidedly*, `ρ₂* ≤ δ^{k/N} ≤ δ^{-η} ρ₂*`. With `N := Tube.ssfGridLen δ` such a level exists once `1 ≤ η · ssfGridLen δ`
(`Kakeya.VeryNotSticky.eventually_gridFine`), because `ρ₂* ∈ [δ, 1]`
(`Kakeya.VeryNotSticky.rho2Star_range`), so `uniform` *may* be the tube part of
`cfg.uniform`'s hierarchy; nothing here requires it, and `N` stays free. In the other direction
the field asks for less than `cfg.uniform` does: only the underlying tube hierarchy is used
(fibre selection and counting are both statements about the assignment classes
`Kakeya.VeryNotSticky.tubeFibre`), so a `Tube.UniformTubeSet` suffices and no
shading-uniformity clause is assumed. The two-sided pin is spent nowhere as an equality:
`Kakeya.VeryNotSticky.exists_full_fibre` and `Kakeya.VeryNotSticky.nonslabFibrePartition`
receive it in lockstep and do not use it. -/
structure SplitInputs (cfg : VeryNotSticky.{u}) (bd : BallData cfg) where
  /-- the number of grid levels of the hierarchy -/
  N : ℕ
  /-- the uniformity constant of the hierarchy -/
  Cu : NNReal
  /-- item (iii): a uniform hierarchy for the family `𝕋` -/
  uniform : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N Cu
  /-- the grid level sitting at the dilated angular scale `ρ₂*`, up to the grid rounding -/
  k : ℕ
  /-- that level is one of the `N` levels -/
  k_le : k ≤ N
  /-- The scale comparison is `ρ₂* ≤ δ^{k/N}`; it is one-sided because
GWZ Definition 2.2 specifies approximate grid scales. -/
  gridScale_ge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ N k
  /-- and from above with the grid rounding loss `δ^{-η}`, `δ^{k/N} ≤ δ^{-η} ρ₂*` — the same
  rounding GWZ write out for the transverse radius, `θb ≤ r ≤ δ^{-η} θb` (l.2253-2255) -/
  gridScale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀
  /-- item (i): `K_KT(β)` at this `δ` with loss `ϱ` -/
  katzTao : cfg.KTScaleData cfg.ϱ
  /-- item (ii): blueprint `fibreConstantThreshold`, with the hierarchy constant `Cu²` of
  `fibreCount` absorbed alongside `(2 C_{lem:ml2bodyAngle}(C₀))²` -/
  fibreConstant : ((Cu : ENNReal) ^ 2) *
      ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 ≤
    (cfg.δ : ENNReal) ^ (-cfg.η)
  /-- Blueprint `uniformSetOfTubes` item (iii) — GWZ Def 2.1(iii), "`|𝕋[T_ρ]|` is constant up
  to a factor `∼ 1`" (`gwz.txt` l.183) — in the inequality shape that
  `Kakeya.VeryNotSticky.nonslabKKTPow` consumes as its hypothesis `hfib`:
  `|𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ Cu² |𝕋|`, uniformly over the nodes at level `k`, with the
  hierarchy's own constant `Cu` squared.

  At this constant the clause *is* derivable from `uniform`:
  `Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le` proves it from
  `Tube.UniformTubeSet.card_class_le`, `le_card_class` and the partition of `cfg.s` into the
  assignment classes. It is kept as a field so that the interface of the splitting is
  unchanged; a producer populates it by that lemma. Stating it for every node is what lets the
  fibre selected by `Kakeya.VeryNotSticky.exists_full_fibre` be used. -/
  fibreCount : ∀ j ∈ uniform.cover.indexSet k,
    ((uniform.cover.indexSet k).card : ℝ) * ((cfg.tubeFibre uniform k j).card : ℝ) ≤
      ((Cu : ℝ) ^ 2) * (cfg.s.card : ℝ)
  /-- The constant of the `ρ₂`-count clause `fibreScaleCount`: a `δ^{-O(η)}` of the same kind
  as `Cang`, and **not** the δ-free `(2 C_{lem:ml2bodyAngle}(C₀))²` this field used to carry.
  A fixed constant independent of `δ` is insufficient for this comparison: the
  field counts bounded-overlap nodes of `cfg.splitHierarchy`, the configuration counts
  essentially distinct covers of a *parent* family
  (`Kakeya.VeryNotSticky.RhoParentData`), and both transports — `ρ₂ → ρ_k` and
  ED-parents → nodes — cost powers of `δ^{-η}` with the wrong sign for a δ-free conclusion. -/
  Ccnt : NNReal
  /-- The fixed-scale threshold on that constant, the exact analogue of `fibreConstant` and of
  `angularConstant`, at the exponent `18` measured by the producer
  `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` (the general form requires `M ≥ 4`). GWZ carry an explicit `δ^{-O(η)}` at exactly
  the site where this count is spent (`gwz.txt` l.2331-2335), and the `≈`/`⪅` of Def 2.1(iii)
  (l.183-195) is `δ^{-O(η)}` in their own bookkeeping. -/
  countConstant : (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η))
  /-- The `ρ₂`-counting input of `Kakeya.VeryNotSticky.nonslabKKTPow`, its hypothesis
  `hcount`: the number of nodes of the hierarchy at the level `k` is at least
  `Ccnt^{-1} ρ₂^{-2-ζ}`.

  In the blueprint this is not a hypothesis: it is `rho2_range` (blueprint `lem:ml2rho2range`),
  which bounds `|𝕋_{ρ₂}| ≥ ρ₂^{-2-ζ}` from below, transported from the scale `ρ₂` to the
  dilated scale `ρ₂*` by `lem:ml2tubeScaleCompare`. Neither step is available for this
  hierarchy at the δ-free constant, and the obstruction is the same at both:

  * `rho2_range` fires only for a family of `ρ₂`-tubes covering `𝕋` that is *pairwise
    essentially distinct*, and `Tube.UniformTubeSet` deliberately does not provide
    that — its `boundedOverlap` replaces essential distinctness, which is unsatisfiable while
    preserving cardinality;
  * `Kakeya.VeryNotSticky.tubeScaleCompare` compares two grid *levels* of one hierarchy, and
    `gridScale_ge`/`gridScale_le` pin a level only at `ρ₂*` (up to `δ^{-η}`); a second level
    at `ρ₂` would still need `rho2_range` there, so it does not help.

  Both are paid for by `Ccnt`/`countConstant`, which is what makes the clause producible:
  `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` derives it from
  `cfg.rho_count`. It is carried in exactly the shape `nonslabKKTPow` consumes, and it travels
  with the rest of item (iii) — it is created by the divergence recorded above, not by the
  blueprint. -/
  fibreScaleCount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
    (Ccnt : ℝ) * ((uniform.cover.indexSet k).card : ℝ)
  /-- The constant hidden in GWZ's "`⪅ μ(ρ₂) ≈ μ(𝕋[T_{ρ₂}], Y)`" (`gwz.txt` l.2321-2322): a
  `δ^{-O(η)}` of dyadic-pigeonhole origin, not absolute. -/
  Cang : NNReal
  /-- The fixed-scale threshold on that constant, the exact analogue of `fibreConstant`. -/
  angularConstant : (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)
  /-- **GWZ (100)–(101) composed** (`gwz.txt` l.2316-2325): at every point `x` and for every
  direction `v`, the tubes of `𝕋_Y(x)` within angle `ρ₂*` of `v` number at most `Cang` times the
  multiplicity of the fibre `𝕋[T_{ρ₂*}]` of any active node of the hierarchy at the level `k`.
  This is what `Kakeya.VeryNotSticky.nonslabPointwiseBound` consumes; the angular multiplicity
  function `μ(ρ)` of GWZ's step 1 (l.1984-1993), through which GWZ derive it, is not recorded:
  GWZ assert (86) on a shading that is not the uniform one and use only this consequence.
  Quantified over the active nodes for the reason recorded on
  `Kakeya.VeryNotSticky.exists_full_fibre`. -/
  angularFibre_le_fibreMult : ∀ j ∈ cfg.activeTubeNodes uniform k,
    ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        (Cang : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre uniform k j) (fun i ↦ (cfg.T i).toShadedBody)

/-- **Projection of the defining fields.** The grid level `k` of a `SplitInputs` sits at the
dilated angular scale `ρ₂*` two-sidedly, `ρ₂* ≤ δ^{k/N} ≤ δ^{-η} ρ₂*`, and not exactly. The
statement is the licensed text of the two fields `gridScale_ge`/`gridScale_le` spelled out, and
the proof is their projection, so this declaration fails to elaborate if either field changes
in either direction — a bound tightened back to an equality, or the rounding loss altered. -/
theorem SplitInputs.gridScale_two_sided {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (si : SplitInputs cfg bd) :
    cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ si.N si.k ∧
      Tube.gridScale cfg.δ si.N si.k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ :=
  ⟨si.gridScale_ge, si.gridScale_le⟩

/-- **Projection of the defining fields.** The fibre count of a `SplitInputs` is at the
hierarchy constant squared, `|𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ Cu² |𝕋|`, and not at the
exact-branching constant `1`. The statement is the licensed text of the field `fibreCount`
spelled out and the proof is its projection, so this declaration fails to elaborate if the
field's constant or quantifier changes. -/
theorem SplitInputs.fibreCount_hierarchy_sq {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (si : SplitInputs cfg bd) :
    ∀ j ∈ si.uniform.cover.indexSet si.k,
      ((si.uniform.cover.indexSet si.k).card : ℝ) *
          ((cfg.tubeFibre si.uniform si.k j).card : ℝ) ≤
        ((si.Cu : ℝ) ^ 2) * (cfg.s.card : ℝ) :=
  si.fibreCount

/-- **Projection of the defining fields.** The `ρ₂`-count clause of a `SplitInputs` is at a
carried constant `Ccnt` bounded by `δ^{-18η}`, and **not** at the δ-free
`(2 C_{lem:ml2bodyAngle}(C₀))²` of the fixed-constant variant. The statement is the licensed
text of the two fields `countConstant`/`fibreScaleCount` spelled out and the proof is their
projection, so this declaration fails to elaborate if either field's constant or exponent
changes — in particular if the δ-free constant is restored. -/
theorem SplitInputs.fibreScaleCount_spelled {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    (si : SplitInputs cfg bd) :
    ((si.Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η))) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
        (si.Ccnt : ℝ) * ((si.uniform.cover.indexSet si.k).card : ℝ) :=
  ⟨si.countConstant, si.fibreScaleCount⟩

/-- **Projection of the defining fields.** The angular input of a `SplitInputs` is GWZ's
composed clause (`gwz.txt` l.2316-2325): at every point and direction the inner angular count
at `ρ₂*` is at most `Cang` times the multiplicity of the fibre of any active node at the level
`k` — with no angular multiplicity function `μ(ρ)` as an intermediary. The statement is the
licensed text of the field `angularFibre_le_fibreMult` spelled out and the proof is its
projection, so this declaration fails to elaborate if the field changes. -/
theorem SplitInputs.angularFibre_le_fibreMult_spelled {cfg : VeryNotSticky.{u}}
    {bd : BallData cfg} (si : SplitInputs cfg bd) :
    ∀ j ∈ cfg.activeTubeNodes si.uniform si.k, ∀ x v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        (si.Cang : ENNReal) *
          ShadedBody.multiplicity (cfg.tubeFibre si.uniform si.k j)
            (fun i ↦ (cfg.T i).toShadedBody) :=
  si.angularFibre_le_fibreMult

/-- **Splitting and Katz–Tao at the ball `B`** (blueprint `lem:ml2tangentialSplit`).

This is the combination, at the fixed ball `B`, of the non-slab splitting
`criticalBoundOnMuTT` of `Kakeya.NonSlab.multSplit` (blueprint `lem:ml2nonslabMultSplit`) with
the Katz–Tao bound `muTTRhoSuingKTbeta` of `Kakeya.VeryNotSticky.nonslabKKT` (blueprint
`lem:ml2nonslabKKT`). Both are stated at the dilated angular scale `ρ₂*`, so they combine
directly:

`μ(𝕋, Y) ⪅ μ(𝕎'_B, Y_{𝕎'_B}) μ(𝕋[T_{ρ₂*}], Y) ⪅ μ(𝕎'_B, Y_{𝕎'_B}) δ^{-(ϱ+η)} (ρ₂^{2+ζ}|𝕋|)^β`,

and the two fixed losses that remain are absorbed into the quarter budget
`δ^{-C_sep(ϱ+η)/4}`, which dominates `δ^{-(ϱ+η)}` with room to spare because
`C_sep/4 = 2^18`. (The factor `4 C_{lem:ml2bodyAngle}(C₀)²` of the comparison between `ρ₂*`-
and `ρ₂`-tubes is *not* among them: `si.fibreConstant` already pays for it inside
`Kakeya.VeryNotSticky.nonslabKKTPow`.)

**The two remaining constants, and what pays for them.** They are the refinement constant of
(T1) — the `C` of `tc.Y'_mass`, entering `Kakeya.NonSlab.multSplit` as `c = tc.C⁻¹` — and the
constant-multiplicity constant of (T4)(a), the `C` of `(tc.thinBall hB).constMult_bodies`.
Both are the *same* number `tc.C`, and both are bounded by a power of `δ` by the seventh
clause `scale.transverse_ballFill` of Configuration `hyp:ml2scale`:
`1000 · C_transfer(tc.C, C₀) ≤ δ^{-η}`, where
`Kakeya.ThinCase.transferConstant C C₀ = 2³ · netUpperConstant C C₀ · netLowerConstant C`
dominates `netUpperConstant C C₀ ≥ 2^12 C³ ≥ C` once `1 ≤ C`, which is
`(tc.thinBall hB).one_le_C`. So `tc.C² ≤ δ^{-2η}`, and
`C_sep(ϱ+η)/4 = 2^18(ϱ+η) ≥ (ϱ+η) + 2η`. Without that clause the conclusion would be
refutable at `δ` near `1`, where every `δ^s` collapses to `1`; naming it here is what keeps
the absorption from being an unstated threshold.

Both hypotheses that the abstract statements need beyond `cfg` are carried explicitly.
`hβ1 : β ≤ 1` is spent raising the counting bound `|𝕋[T_{ρ₂*}]| ≤ K · Ccnt · ρ₂^{2+ζ} |𝕋|` to
the `β`-th power, where it gives `(K Ccnt)^β ≤ (δ^{-Mη})^β ≤ δ^{-Mη}` (blueprint
`lem:ml2nonslabKKTPow`); it is also what
the current Lean interface `Kakeya.VeryNotSticky.nonslabKKT` demands. It is not implied by
`cfg.hβ`, which gives only `0 < β`, so it is threaded down from
`Kakeya.VeryNotSticky.exists_goalMult`, which already carried it for the thick branch.
`hBmax` is the hypothesis of blueprint `lem:ml2nonslabPointwiseMult` that `B` *maximises*
`μ(𝕎'_{B'}, Y_{𝕎'_{B'}})` over the cover; it is discharged in
`Kakeya.VeryNotSticky.goalMult_of_b_le`, which picks the maximising ball rather than an
arbitrary one, and is threaded through both non-slab multiplicity branches.

Items (i)–(iii) of the blueprint statement are the hypotheses that
`Kakeya.VeryNotSticky.nonslabKKT` and `Kakeya.VeryNotSticky.nonslabKKTPow` do not discharge
for themselves and that nothing here discharges either, so they are carried, bundled as
`si : Kakeya.VeryNotSticky.SplitInputs cfg bd`; see that structure for the three items and
for the divergence at item (iii), where the Lean form assumes a uniform hierarchy at the
grid level sitting at `ρ₂*` in place of the blueprint's exact fibre count, and pays for that
divergence with the counting fields `fibreCount`, `Ccnt`/`countConstant` and `fibreScaleCount`.

**The remaining binder groups.** `cfg` is Configuration `hyp:ml2setup`; `bd` and `tc` are
Configuration `hyp:ml2thinsetup`, i.e. (C2)–(C5) and (T1)–(T7); `scale` is Configuration
`hyp:ml2scale`. `hβ1`, `hnotslab` and `B`/`hB`/`hBmax` are the blueprint statement's own three
side conditions. The four implicit binders `τ`, `τ'`, `νA` and `thr` carry no hypothesis of
their own: they exist only as indices of `Kakeya.VeryNotSticky.CaseScale`, and are left free
because the only clause used here, `transverse_ballFill`, mentions none of them. For the same
reason there is no `params : Kakeya.VeryNotSticky.CaseParams …` binder: the proof uses no
relation between the exponents, the budget step being the arithmetic `C_sep/4 = 2^18 ≥ 1`
together with `ϱ, η > 0` and `δ ≤ 1` from `cfg`.

The statement lives here, beside `Kakeya.NonSlab.multSplit` and
`Kakeya.VeryNotSticky.nonslabKKTPow`, the two results it combines, and not in the tangential
leaf: it is shared by both non-slab multiplicity branches, the tangential leaf
`Kakeya.VeryNotSticky.goalMult_of_theta_lt` and the small-multiplicity leaf
`Kakeya.VeryNotSticky.goalMult_of_multBodies_le`, and belongs to neither.

**How the four steps compose.** `Kakeya.VeryNotSticky.exists_full_fibre` selects a node `j` of
the hierarchy at level `k` whose fibre `𝕋[T_{ρ₂*}] = cfg.tubeFibre` is at least as full as `𝕋`,
hence has fullness `≥ δ^η`. `Kakeya.VeryNotSticky.nonslabKKTPow` bounds that fibre's
multiplicity by `δ^{-(ϱ+η)} (ρ₂^{2+ζ}|𝕋|)^β`, with `si.fibreCount` and `si.fibreScaleCount`
matching its `hfib` (at the hierarchy constant `K = Cu²`, which `si.fibreConstant` absorbs) and
`hcount`. `Kakeya.NonSlab.multSplit` splits `μ(𝕋, Y)` into the body factor and that fibre, its
hypothesis `hpt` being manufactured from `Kakeya.VeryNotSticky.nonslabPointwiseBound`, whose
angular input `hang` is `si.angularFibre_le_fibreMult` at the selected node — GWZ's composed
clause "the cardinality of the inner set is `⪅ μ(ρ₂) ≈ μ(𝕋[T_{ρ₂}], Y)`" (`gwz.txt`
l.2321-2322), read directly in terms of the fibre multiplicity. Finally
`Kakeya.VeryNotSticky.tangentialSlabMultAbsorb` absorbs the three constants
`tc.C, tc.C, Cang` and the single power `δ^{-(ϱ+η)}` into the quarter budget, at `k = 3`,
`m = 1`, `ϱ := cfg.ϱ + cfg.η`; the two thin-case constants are paid for by
`Kakeya.VeryNotSticky.thinConstant_le` and the angular one by `si.angularConstant`.

The angular scale bookkeeping is `Kakeya.VeryNotSticky.rho2Star_range`, which needs the
non-slab hypothesis in the `δ^{exscal} r₁` shape supplied by
`Kakeya.VeryNotSticky.b_le_pow_mul_r₁`, and places `ρ₂*` in `[δ, 1]`, the range on which `μ` is
defined. -/
theorem nonslabSplitBound (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (hβ1 : cfg.β ≤ 1)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ B' (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (si : SplitInputs cfg bd) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * (cfg.ϱ + cfg.η) / 4)) *
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W *
        (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β := by
  classical
  -- STEP 0: angular range
  have hnots : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := cfg.b_le_pow_mul_r₁ hnotslab
  have hrange := cfg.rho2Star_range cfg.hδ cfg.hδ1 bd.hC₀ scale.rho2Star_le_one hnots
  have hle12 : cfg.rho2 ≤ 2 * cfg.rho2 := by
    simpa using (mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 2) (by exact zero_le))
  have hδρNN : cfg.δ ≤ cfg.rho2Star bd.C₀ :=
    le_trans (le_trans hrange.1 hle12) hrange.2.1
  have hδρ : (cfg.δ : ℝ) ≤ (cfg.rho2Star bd.C₀ : ℝ) := by exact_mod_cast hδρNN
  have hρ1 : (cfg.rho2Star bd.C₀ : ℝ) ≤ 1 := by exact_mod_cast hrange.2.2
  -- STEP 1: full fibre
  have hs : cfg.s.Nonempty := by
    by_contra hne
    have hcard0 : (cfg.s.card : ENNReal) = 0 := by
      have he : cfg.s = ∅ := by
        apply Finset.ext
        intro i
        constructor
        · intro hi
          exact False.elim (hne ⟨i, hi⟩)
        · simp
      simp [he]
    have hbad : (1 : ENNReal) ≤ 0 := by
      calc
        (1 : ENNReal) ≤ (cfg.δ : ENNReal) * (cfg.s.card : ENNReal) := cfg.tube_count
        _ = 0 := by simp [hcard0]
    exact (by norm_num : ¬ (1 : ENNReal) ≤ 0) hbad
  rcases Kakeya.VeryNotSticky.exists_full_fibre cfg si.uniform si.k si.k_le si.gridScale_ge
      si.gridScale_le hs with
    ⟨j, hj, _hfs, hfull⟩
  have hjIdx : j ∈ si.uniform.cover.indexSet si.k := by
    simpa [VeryNotSticky.activeTubeNodes] using (Finset.mem_filter.mp hj).1
  let F : Finset cfg.ι := cfg.tubeFibre si.uniform si.k j
  -- STEP 2: Katz–Tao on the fibre, at the hierarchy constant `K = Cu²`
  -- and the count constant `Ccnt` of the field `countConstant`. The
  -- joint threshold is `Cu² · Ccnt ≤ δ^{-19η}`: `fibreConstant` gives `Cu² ≤ δ^{-η}` and
  -- `countConstant` gives `Ccnt ≤ δ^{-18η}`, so the product is `δ^{-19η}` and not `δ^{-18η}`
  -- ( (c), which measured the `+1` by compilation).
  have hδne0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt cfg.hδ
  have hδneTop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC1e : (1 : ENNReal) ≤ ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant bd.C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant bd.hC₀)
    exact_mod_cast h1
  have hCsq : (1 : ENNReal) ≤ ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 := by
    rw [pow_two]
    calc (1 : ENNReal) = 1 * 1 := by rw [one_mul]
      _ ≤ ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) *
            ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) :=
          mul_le_mul' hC1e hC1e
  have hCuδ : ((si.Cu ^ 2 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
    have h0 : ((si.Cu ^ 2 : NNReal) : ENNReal) = (si.Cu : ENNReal) ^ 2 := by push_cast; ring
    calc ((si.Cu ^ 2 : NNReal) : ENNReal) = (si.Cu : ENNReal) ^ 2 * 1 := by rw [h0, mul_one]
      _ ≤ (si.Cu : ENNReal) ^ 2 *
            ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 :=
          mul_le_mul' le_rfl hCsq
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := si.fibreConstant
  have hCδK : ((si.Cu ^ 2 : NNReal) : ENNReal) * (si.Ccnt : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(19 * cfg.η)) := by
    have hadd : (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) =
        (cfg.δ : ENNReal) ^ (-(19 * cfg.η)) := by
      rw [← ENNReal.rpow_add _ _ hδne0 hδneTop]
      congr 1
      ring
    calc ((si.Cu ^ 2 : NNReal) : ENNReal) * (si.Ccnt : ENNReal)
        ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) :=
          mul_le_mul' hCuδ si.countConstant
      _ = (cfg.δ : ENNReal) ^ (-(19 * cfg.η)) := hadd
  have hfibK : ((si.uniform.cover.indexSet si.k).card : ℝ) *
      ((cfg.tubeFibre si.uniform si.k j).card : ℝ) ≤
        ((si.Cu ^ 2 : NNReal) : ℝ) * (cfg.s.card : ℝ) := by
    exact_mod_cast si.fibreCount j hjIdx
  have hKKT : ShadedBody.multiplicity F (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ + 19 * cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
    simpa [F] using
      cfg.nonslabKKTPow hβ1 si.katzTao (M := 19) (by norm_num) hCδK
        (cfg.tubeFibre_subset si.uniform si.k j) hfull
        ((si.uniform.cover.indexSet si.k).card) hfibK si.fibreScaleCount
  let M : ENNReal := ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
  let mF : ENNReal := ShadedBody.multiplicity F (fun i ↦ (cfg.T i).toShadedBody)
  let Ctot : NNReal := tc.C * si.Cang
  let X : ENNReal := ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
  -- STEP 3: the pointwise bound of `multSplit`, with the composed angular clause at the node `j`
   
  have hang : ∀ y v : EuclideanSpace ℝ (Fin 3),
      (((cfg.angularFibre y v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
        (si.Cang : ENNReal) * mF := by
    intro y v
    simpa [mF, F] using si.angularFibre_le_fibreMult j hj y v
  have hpt : ∀ x ∈ ShadedBody.iUnionShade cfg.s tc.Y'Body,
      (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
        (Ctot : ENNReal) * M * mF := by
    intro x hx
    have hpb : (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal) ≤
        ((tc.C : ENNReal) * M) * ((si.Cang : ENNReal) * mF) := by
      simpa [M] using cfg.nonslabPointwiseBound tc hB hBmax hang hδρ hρ1 hx
    calc
      (ShadedBody.pointwiseMultiplicity cfg.s tc.Y'Body x : ENNReal)
          ≤ ((tc.C : ENNReal) * M) * ((si.Cang : ENNReal) * mF) := hpb
      _ = (Ctot : ENNReal) * M * mF := by
          simp only [Ctot, ENNReal.coe_mul]
          ring
  -- STEP 4: split
  have hCpos : (0 : NNReal) < tc.C := lt_of_lt_of_le (by norm_num) (tc.thinBall hB).one_le_C
  have href := tc.isCRefinement_Y'Body hCpos
  have hsplit := Kakeya.NonSlab.multSplit (I := cfg.s) (Y := fun i ↦ (cfg.T i).toShadedBody)
      (Y' := tc.Y'Body) (bodies' := (tc.thinBall hB).bodies') (Wsh := (tc.thinBall hB).W)
      (inn := F) (Yin := fun i ↦ (cfg.T i).toShadedBody) (c := tc.C⁻¹) (C := Ctot)
      (inv_pos.mpr hCpos) href (by simpa [M, mF] using hpt)
  have hinv : ((tc.C⁻¹ : NNReal) : ENNReal)⁻¹ = (tc.C : ENNReal) := by
    rw [ENNReal.coe_inv (ne_of_gt hCpos)]
    rw [inv_inv]
  have hsplit1 : X ≤ (tc.C : ENNReal) * (Ctot : ENNReal) * M * mF := by
    simpa [X, M, mF, hinv] using hsplit
  -- STEP 5: combine and shape
  have hrho_pow : ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β
      = (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ cfg.hβ.le]
    rw [← ENNReal.rpow_mul]
  -- The `19η` of `hKKT` is regrouped into the quarter budget's `m`-slot as `19(ϱ+η)`, which
  -- dominates it because `ϱ > 0` (the absorption estimate concludes
  -- `m`-free, so this costs the downstream statement nothing).
  have h19e : (cfg.δ : ENNReal) ^ (-(cfg.ϱ + 19 * cfg.η)) ≤
      (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast cfg.hδ1
    · linarith [cfg.hϱ]
  have hsubKKT : mF ≤ (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
      ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
    have h0 : mF ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + 19 * cfg.η)) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := hKKT
    exact h0.trans (mul_le_mul' h19e le_rfl)
  have hX'' : X ≤ (tc.C : ENNReal) * (Ctot : ENNReal) * M *
      ((cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
        ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β) := by
    exact le_trans hsplit1 (mul_le_mul_of_nonneg_left hsubKKT (by positivity))
  let Cfin : Fin 3 → NNReal := ![tc.C, tc.C, si.Cang]
  have hprod_eq : (∏ j : Fin 3, (Cfin j : ENNReal)) =
      (tc.C : ENNReal) * (tc.C : ENNReal) * (si.Cang : ENNReal) := by
    rw [Fin.prod_univ_three]
    simp [Cfin]
  let R : ENNReal :=
    M * (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β
  have hXabsorb : X ≤ (∏ j : Fin 3, (Cfin j : ENNReal)) *
      (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) * R := by
    calc
      X ≤ (tc.C : ENNReal) * (Ctot : ENNReal) * M *
          ((cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
            ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β) := hX''
      _ = (tc.C : ENNReal) * (Ctot : ENNReal) *
          (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) *
          (M * (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
            (cfg.s.card : ENNReal) ^ cfg.β) := by
          rw [hrho_pow]
          ring
      _ = (∏ j : Fin 3, (Cfin j : ENNReal)) *
          (cfg.δ : ENNReal) ^ (-((19 : ℝ) * (cfg.ϱ + cfg.η))) * R := by
          rw [hprod_eq]
          simp only [Ctot, R, ENNReal.coe_mul]
          ring
  -- STEP 6: absorb
  have hϱsum : 0 < cfg.ϱ + cfg.η := add_pos cfg.hϱ cfg.hη
  have hmono : (cfg.δ : ENNReal) ^ (-cfg.η) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge
    · exact_mod_cast cfg.hδ1
    · linarith [cfg.hϱ]
  have hthin : (tc.C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := cfg.thinConstant_le tc hB scale
  have hangC : (si.Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := si.angularConstant
  have hC : ∀ j : Fin 3, (Cfin j : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := by
    intro j
    have hbase : ∀ c : NNReal, (c : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
        (c : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ + cfg.η)) := fun c hc => hc.trans hmono
    fin_cases j
    · exact hbase _ hthin
    · exact hbase _ hthin
    · exact hbase _ hangC
  have hXabsorb' : X ≤ (∏ j : Fin 3, (Cfin j : ENNReal)) *
      (cfg.δ : ENNReal) ^ (-(((19 : ℕ) : ℝ) * (cfg.ϱ + cfg.η))) * R := by
    simpa using hXabsorb
  have hXabs := Kakeya.VeryNotSticky.tangentialSlabMultAbsorb (δ := cfg.δ) (hδ := cfg.hδ)
      (hδ1 := cfg.hδ1) (ϱ := cfg.ϱ + cfg.η) (hϱ := hϱsum) (k := 3) (m := 19)
      (hkm := by norm_num) (C := Cfin) (hC := hC) (X := X) (R := R) hXabsorb'
  simpa [X, R, M, mul_assoc] using hXabs

end Kakeya.VeryNotSticky
