/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineInheritance

/-!
# Branch (ii) of the geometric core: the outer two factors of the triple product

`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated`  bounds the multiplicity of the
leaf family by a subpolynomial loss times a product of **three** multiplicities,

`μ(s₁, V) ≤ L · μ(𝕋[T_τ], Y') · μ(𝕋_τ[T_θ], Y_τ') · μ(𝕋_θ, Y_θ)`.

This file bounds the two *outer* factors — GWZ `section9.tex:74–79` (the fine factor) and
`section9.tex:81–85` (the coarse factor).  The middle factor is the whole of the rescaled
argument (the estimate … the estimate) and is not touched here.

## the estimate, the fine factor

GWZ argues: Remark 3.3(B) gives `C_KT(𝕋[T_τ], T_τ) ≤ δ^{-η}`, one may *choose* `T_τ` so that
`λ(𝕋[T_τ], Y) ⪆ λ(𝕋, Y)`, and then `K_KT(β)` applied to the fibre rescaled to `B₁` at scale
`δ/τ` gives `μ(𝕋[T_τ], Y) ≤ (δ/τ)^{-η₁} |𝕋[T_τ]|^β`.

**The rescaling is not needed, and this file does not perform it.**  The reason is measured, not
stylistic:

* `C_KT(𝕋[T_τ], T_τ)` is `Δ_max` of the fibre read after *any* affine change of variables taking
  `T_τ` to the unit ball, and `Kakeya.maxDensity` is exactly invariant under such a change
  (`Kakeya.maxDensity_affineImage`), so `C_KT(𝕋[T_τ], T_τ) = Δ_max(𝕋[T_τ])` — the content of
  `Kakeya.ML2Spine.isKatzTao_familyIn_affineImage`, restated here as
  `Kakeya.ML2Core.isKatzTao_fibre_anchored`;
* the fibre already consists of honest `δ`-tubes inside `B₁` (that is exactly what seam
  delivers), so `K_KT(β)` applies to it *at the scale `δ`*, with no rescaling and no outer-tube
  volume loss;
* `(δ/τ)^{-η₁} ≤ δ^{-η₁}` because `τ ≤ 1`, so GWZ's conclusion **implies** the `δ`-form and the
  `δ`-form is the one the assembly consumes: every other loss on branch (ii) is a power of `δ`.

Rescaling would therefore buy a strictly stronger bound that the assembly immediately throws
away, at the price of the distortion package `Kakeya.ML2Reduction.outerTube_spec` (whose
`Δ_max` transport across the enclosing outer tube is *not* in the tree) — so the direct route is
taken.  `Kakeya.ML2Core.exists_fine_factor` is the analytic core and
`Kakeya.ML2Core.exists_fine_factor_at_window` is it wired to output, including GWZ's
"we can choose `T_τ`": the choice is the mediant pigeonhole
`Kakeya.ML2Core.exists_fibre_fullness_le'`, which costs **nothing**, fullness being a ratio.

## the estimate, the coarse factor

`K_KT(β)` at the *coarse* scale `θ` cannot be applied with the fullness bound read at `θ`: what
the argument owns is `λ(𝕋_θ, Y_θ) ⪆ λ(𝕋, Y) ≥ δ^{η}`, and `δ^{η} ≥ θ^{η'}` fails for every fixed
`η` once `θ = δ^{a/M}` with `M = ssfGridLen δ → ∞`.  The lemma that decouples the two scales is
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` (GWZ Remark 3.6 applied to Lemma 3.7),
which reads both the fullness hypothesis and the loss at an auxiliary scale `δ ≤ θ`; that is what
`Kakeya.ML2Core.exists_coarse_factor` uses, and the `Δ_max^{1-β}` factor of Lemma 3.7 is where
the window's `coarse_maxDensity_le` field enters.

Lemma 3.7 carries a smallness threshold **on the tube scale**, here `θ`, and `θ` is not small in
general: at `a = 0` the coarse grid scale is `Tube.gridScale δ M 0 = 1` exactly.  For `1 ≤ a` the
threshold is eventually met, and that is `Kakeya.ML2Core.eventually_gridScale_le`, proved from
the doubly logarithmic size of `Kakeya.ssfGridLen` exactly as
`Kakeya.ML2Core.gridScale_le_quarter` is.  At `a = 0` the only exit is the trivial bound
`Kakeya.ML2Core.multiplicity_le_of_card_le`, which needs a cardinality bound on the retained
coarse node set that output does not carry; the row is left there and the obligation is
named, rather than bridged by a new `Prop`.

The coarse family's ball containment is likewise **not** supplied by the estimate: seam is run
at the *fine* level `b`, and a level-`a` node containing a level-`b` node inside `B₁` is only
inside `B̄(0, 1 + 4θ)` (`Kakeya.ML2Core.coverTube_carrier_subset_closedBall`).  It is therefore an
explicit hypothesis of `Kakeya.ML2Core.exists_coarse_factor_at_window`.
-/

@[expose] public section

open MeasureTheory ShadedBody ConvexSpaceBody Tube Filter
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Bookkeeping shared by the two factors -/

section Bookkeeping

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The union of the shades over `Finset.attach` is the union over the finset. -/
theorem biUnion_shade_attach {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    (⋃ x ∈ s.attach, (V x.1).shade) = ⋃ i ∈ s, (V i).shade := by
  ext y
  simp only [Set.mem_iUnion, Finset.mem_attach, exists_prop, true_and, Subtype.exists]

/-- Multiplicity is unchanged by the `Finset.attach` reindexing.  This is the special case of
`Kakeya.ShadedBody.multiplicity_map` that lets a statement quantified over *all* indices of the
ambient type be applied to a family whose hypotheses hold only on a finset; the general `map`
form lives in a `Plank` module this file does not import. -/
theorem multiplicity_attach_val {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.multiplicity s.attach (fun x => V x.1) = ShadedBody.multiplicity s V := by
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div,
    Finset.sum_attach s (fun i => volume (V i).shade), biUnion_shade_attach]

/-- Fullness is unchanged by the `Finset.attach` reindexing. -/
theorem fullness_attach_val {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) :
    ShadedBody.fullness s.attach (fun x => V x.1) = ShadedBody.fullness s V := by
  rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def,
    Finset.sum_attach s (fun i => volume (V i).shade),
    Finset.sum_attach s (fun i => volume (V i).carrier)]

/-- `Δ_max` is unchanged by the `Finset.attach` reindexing. -/
theorem maxDensity_attach_val {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E) :
    Kakeya.maxDensity s.attach (fun x => W x.1) = Kakeya.maxDensity s W := by
  have h := Kakeya.maxDensity_map s.attach (Function.Embedding.subtype (fun x => x ∈ s)) W
  rw [Finset.attach_map_val] at h
  exact h.symm

/-- **`Δ_max` of a translated subfamily is at most `Δ_max` of the untranslated whole.**

`Kakeya.maxDensity` is translation invariant (`Kakeya.StickyKakeya.maxDensity_tube_translate`)
and monotone in the index set (`Kakeya.maxDensity_mono`); this is the two facts fused in the
shape in which both factors need them, the shaded families of the estimate being *manufactured on the
translated tubes* while every `Δ_max` hypothesis of the reduction is stated upstairs. -/
theorem maxDensity_le_of_translate_subset {θ : NNReal} {ι : Type*} {t u : Finset ι}
    {T : ι → Tube θ E} {Y : ι → ShadedTube θ E} {v : E} (htu : t ⊆ u)
    (hY : ∀ k, (Y k).toTube = (T k).translate v) :
    Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody)
      ≤ Kakeya.maxDensity u (fun k => (T k).toConvexSpaceBody) := by
  have hbody : ∀ k, (Y k).toConvexSpaceBody = ((T k).translate v).toConvexSpaceBody :=
    fun k => congrArg (fun S : Tube θ E => S.toConvexSpaceBody) (hY k)
  calc Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody)
      = Kakeya.maxDensity t (fun k => ((T k).translate v).toConvexSpaceBody) := by
        simp only [hbody]
    _ = Kakeya.maxDensity t (fun k => (T k).toConvexSpaceBody) :=
        Kakeya.StickyKakeya.maxDensity_tube_translate t T v
    _ ≤ Kakeya.maxDensity u (fun k => (T k).toConvexSpaceBody) := Kakeya.maxDensity_mono _ htu

/-- The leaf-level reading of `Kakeya.ML2Core.maxDensity_le_of_translate_subset`: the shaded
family `Y'` the estimate manufactures on the translated leaves has, on any subfamily, at most the
`Δ_max` of the original leaf family. -/
theorem maxDensity_fibre_le {δ : NNReal} {ι : Type*} {s f : Finset ι}
    {V Y : ι → ShadedTube δ E} {v : E} (hfs : f ⊆ s)
    (hY : ∀ i, (Y i).toTube = ((V i).translate v).toTube) :
    Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody)
      ≤ Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) := by
  refine maxDensity_le_of_translate_subset (T := fun i => (V i).toTube) (v := v) hfs ?_
  intro i
  rw [hY i, Kakeya.StickyKakeya.shadedTube_translate_toTube]

/-- **Mediant fibre selection for fullness, at a general ambient space.**

`Kakeya.exists_fibre_fullness_le` is this statement at `E = EuclideanSpace ℝ (Fin 3)`, where its
Proposition-5.1 consumer pinned it; the proof is the same mediant argument, and the general form
is what the branch-(ii) families — stated over an abstract `E` throughout `Reduction/` — need.

Fullness is a *ratio*, not a mass, so passing from the whole family to the fullest fibre costs no
cardinality factor at all.  This is GWZ's "we can choose `T_τ` so that
`λ(𝕋[T_τ], Y) ⪆ λ(𝕋, Y)`", and the `⪆` is in fact an `≥`. -/
theorem exists_fibre_fullness_le' {ι κ : Type*} [DecidableEq κ] (s : Finset ι)
    (V : ι → ShadedBody E) (ts : Finset κ) (p : ι → κ) (hp : ∀ i ∈ s, p i ∈ ts)
    (hts : ts.Nonempty)
    (hB0 : (∑ i ∈ s, volume (V i).carrier) ≠ 0)
    (hBtop : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤) :
    ∃ x ∈ ts, ShadedBody.fullness s V
      ≤ ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V := by
  classical
  let A : ENNReal := ∑ i ∈ s, volume (V i).shade
  let B : ENNReal := ∑ i ∈ s, volume (V i).carrier
  let Ax : κ → ENNReal := fun x => ∑ i ∈ {i ∈ s | p i = x}, volume (V i).shade
  let Bx : κ → ENNReal := fun x => ∑ i ∈ {i ∈ s | p i = x}, volume (V i).carrier
  have hB0' : B ≠ 0 := by simpa [B] using hB0
  have hBtop' : B ≠ ⊤ := by simpa [B] using hBtop
  obtain ⟨x₀, hx₀ts, hx₀⟩ :=
    Finset.exists_max_image ts (fun x => ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V) hts
  have hsumA : (∑ x ∈ ts, Ax x) = A := by
    simpa [Ax, A] using (Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).shade))
  have hsumB : (∑ x ∈ ts, Bx x) = B := by
    simpa [Bx, B] using (Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).carrier))
  have hAmul : (ShadedBody.fullness s V : ENNReal) * B = A := by
    simpa [A, B] using (ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V).symm
  have hAximul : ∀ x : κ,
      Ax x = (ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V : ENNReal) * Bx x := by
    intro x
    simpa [Ax, Bx] using
      (ShadedBody.sum_volumeReal_shade_eq_fullness_mul ({i ∈ s | p i = x} : Finset ι) V)
  have hle : (ShadedBody.fullness s V : ENNReal) * B ≤
      (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * B := by
    calc
      (ShadedBody.fullness s V : ENNReal) * B = A := hAmul
      _ = ∑ x ∈ ts, Ax x := hsumA.symm
      _ = ∑ x ∈ ts, (ShadedBody.fullness ({i ∈ s | p i = x} : Finset ι) V : ENNReal) * Bx x :=
        Finset.sum_congr rfl (fun x _ => hAximul x)
      _ ≤ ∑ x ∈ ts,
          (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * Bx x :=
        Finset.sum_le_sum (fun x hx =>
          mul_le_mul_left (ENNReal.coe_le_coe.mpr (hx₀ x hx)) (Bx x))
      _ = (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * ∑ x ∈ ts, Bx x := by
        rw [← Finset.mul_sum]
      _ = (ShadedBody.fullness ({i ∈ s | p i = x₀} : Finset ι) V : ENNReal) * B := by rw [hsumB]
  exact ⟨x₀, hx₀ts, ENNReal.coe_le_coe.mp ((ENNReal.mul_le_mul_iff_left hB0' hBtop').mp hle)⟩

/-- **The trivial multiplicity bound, in the shape the assembly multiplies.**

`μ ≤ |t|` always, so a cardinality ceiling `C` on the family gives `μ ≤ C^{1-β} |t|^β`.  This is
the only exit available at a degenerate scale, where `K_KT(β)`'s smallness threshold cannot be
met; it is stated here because `Tube.gridScale δ M 0 = 1` makes that case real on branch (ii),
and it needs no smallness, no shading and no density hypothesis. -/
theorem multiplicity_le_of_card_le {ι : Type*} {t : Finset ι} {V : ι → ShadedBody E}
    {β : ℝ} (hβ1 : β ≤ 1) {C : ENNReal} (hC : (t.card : ENNReal) ≤ C) :
    ShadedBody.multiplicity t V ≤ C ^ (1 - β) * (t.card : ENNReal) ^ β := by
  rcases Nat.eq_zero_or_pos t.card with h0 | h0
  · have ht : t = ∅ := Finset.card_eq_zero.mp h0
    subst ht
    simp [ShadedBody.multiplicity]
  · have hc0 : ((t.card : ENNReal)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hctop : ((t.card : ENNReal)) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc ShadedBody.multiplicity t V ≤ (t.card : ENNReal) := ShadedBody.multiplicity_le_card t V
      _ = (t.card : ENNReal) ^ (1 - β) * (t.card : ENNReal) ^ β := by
          rw [← ENNReal.rpow_add _ _ hc0 hctop]
          simp
      _ ≤ C ^ (1 - β) * (t.card : ENNReal) ^ β := by
          have h1b : (0 : ℝ) ≤ 1 - β := by linarith
          gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `ENNReal.ofReal` of a real power of a positive `NNReal` is the `ENNReal` power.  The window's
three density fields are stated with `ENNReal.ofReal`; every consumer wants the `rpow`. -/
theorem ofReal_rpow_coe {ρ : NNReal} (hρ : 0 < ρ) (x : ℝ) :
    ENNReal.ofReal ((ρ : ℝ) ^ x) = (ρ : ENNReal) ^ x := by
  rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_rpow_of_ne_zero hρ.ne']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A negative power is antitone in the base: `δ ≤ θ ≤ 1` and `0 ≤ x` give `θ^{-x} ≤ δ^{-x}`. -/
theorem rpow_neg_le_rpow_neg_of_le {δ θ : NNReal} (hδθ : δ ≤ θ) {x : ℝ} (hx : 0 ≤ x) :
    (θ : ENNReal) ^ (-x) ≤ (δ : ENNReal) ^ (-x) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (by exact_mod_cast hδθ) hx)

end Bookkeeping

/-! ## the estimate: the fine factor (GWZ `section9.tex:74–79`) -/

section FineFactor

variable [Nontrivial E]

omit [Nontrivial E] in
/-- **GWZ Remark 3.3(B) at the Section-9 anchor, with the anchor made explicit.**

`C_KT(𝕋[T_τ], T_τ) ≤ C` — the fibre of `𝕋` inside the `τ`-tube `T_τ`, read after *any* affine
change of variables carrying `T_τ` to the unit ball, is `C`-Katz–Tao as soon as the whole family
is.  This is `Kakeya.ML2Spine.isKatzTao_familyIn_affineImage`; it is recorded here because it is
what licenses the fine factor being taken at the scale `δ` rather than at `δ/τ`: the anchored
constant is `Δ_max` of the fibre and nothing else. -/
theorem isKatzTao_fibre_anchored {δ : NNReal} {ι : Type*} {s : Finset ι}
    {V : ι → ShadedTube δ E} {C : ENNReal}
    (h : Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) ≤ C)
    (K : ConvexSpaceBody E) (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    ConvexSpaceBody.IsKatzTao
      (Kakeya.familyIn s (fun i => (V i).toConvexSpaceBody) K)
      (fun i => ((V i).toConvexSpaceBody).affineImage L.toAffineMap hcont) C :=
  Kakeya.ML2Spine.isKatzTao_familyIn_affineImage h K L hcont

/-- **the estimate, the analytic core: `K_KT(β)` applied to a fibre, at the leaf scale.**

A family of `δ`-tubes in `B₁` with `Δ_max ≤ δ^{-η}` and `λ ≥ δ^{η}` has multiplicity at most
`δ^{-ε} |·|^β`.  This is `Kakeya.KatzTaoEstimate.generalize` read at its own scale — the
`τ`-decoupling it offers is not needed here, the fibre living at the leaf scale `δ`, but the
memberwise ball hypothesis `∀ i ∈ f` (rather than `∀ i`) is, since shaded families are
total functions on the ambient index type and only their retained members are normalised into
`B₁`. -/
theorem exists_fine_factor {β : ℝ} (hβ0 : 0 ≤ β) (hKT : Kakeya.KatzTaoEstimate.{u} E β)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (f : Finset ι) (Y : ι → ShadedTube δ E),
        (∀ i ∈ f, (Y i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        (δ : NNReal) ^ η ≤ ShadedBody.fullness f (fun i => (Y i).toShadedBody) →
        ShadedBody.multiplicity f (fun i => (Y i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-ε) * (f.card : ENNReal) ^ β := by
  obtain ⟨η, hη, hev⟩ := Kakeya.KatzTaoEstimate.generalize E hβ0 hKT ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hδ0
  intro ι f Y hball hmax hfull
  exact hδ δ hδ0 le_rfl f Y hball hmax hfull

/-- **GWZ's "we can choose `T_τ`", as a selection with no loss.**

From first `c`-refinement clause, some retained fine node's fibre is at least as full as
the whole retained leaf family, hence at least `c · λ(s₁, V)`.  Both steps are exact: the
refinement clause is `ShadedBody.IsCRefinement.coe_mul_fullness_le` and the selection is the
mediant `Kakeya.ML2Core.exists_fibre_fullness_le'`. -/
theorem exists_fine_fibre_fullness
    {δ : NNReal} (hδ0 : 0 < δ) {ι κ : Type*} [DecidableEq κ] {s₁ : Finset ι} {t : Finset κ}
    {V Y : ι → ShadedTube δ E} {v : E} {pτ : ι → κ} {c : NNReal}
    (href : ShadedBody.IsCRefinement ({i ∈ s₁ | pτ i ∈ t} : Finset ι)
        (fun i => (Y i).toShadedBody) s₁ (fun i => ((V i).translate v).toShadedBody) c)
    (htne : t.Nonempty)
    (hpos : 0 < c * ShadedBody.fullness s₁ (fun i => (V i).toShadedBody)) :
    ∃ jτ ∈ t, c * ShadedBody.fullness s₁ (fun i => (V i).toShadedBody)
      ≤ ShadedBody.fullness ({i ∈ s₁ | pτ i = jτ} : Finset ι)
          (fun i => (Y i).toShadedBody) := by
  classical
  set s₁' : Finset ι := {i ∈ s₁ | pτ i ∈ t} with hs₁'
  have htr : ShadedBody.fullness s₁ (fun i => ((V i).translate v).toShadedBody)
      = ShadedBody.fullness s₁ (fun i => (V i).toShadedBody) := by
    have hfun : (fun i => ((V i).translate v).toShadedBody)
        = (fun i => ((V i).toShadedBody).translate v) := rfl
    rw [hfun]
    exact ShadedBody.fullness_translate_const s₁ (fun i => (V i).toShadedBody) v
  have h1 : c * ShadedBody.fullness s₁ (fun i => (V i).toShadedBody)
      ≤ ShadedBody.fullness s₁' (fun i => (Y i).toShadedBody) := by
    have h := href.coe_mul_fullness_le
    rw [htr] at h
    exact_mod_cast h
  have hposS : 0 < ShadedBody.fullness s₁' (fun i => (Y i).toShadedBody) :=
    lt_of_lt_of_le hpos h1
  have hne : s₁'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s₁' with h | h
    · rw [h] at hposS; simp [ShadedBody.fullness, ShadedBody.fullness'] at hposS
    · exact h
  obtain ⟨hB0, hBtop⟩ :=
    Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hδ0 s₁' Y hne
  obtain ⟨jτ, hjτ, hfib⟩ :=
    exists_fibre_fullness_le' (E := E) s₁' (fun i => (Y i).toShadedBody) t pτ
      (fun i hi => (Finset.mem_filter.mp hi).2) htne hB0.ne' hBtop
  refine ⟨jτ, hjτ, h1.trans ?_⟩
  have heq : ({i ∈ s₁' | pτ i = jτ} : Finset ι) = ({i ∈ s₁ | pτ i = jτ} : Finset ι) := by
    ext i
    simp only [hs₁', Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, _⟩, h⟩; exact ⟨hi, h⟩
    · rintro ⟨hi, h⟩; exact ⟨⟨hi, h ▸ hjτ⟩, h⟩
  rw [← heq]
  exact hfib

open Classical in
/-- **the estimate, wired to output.**

Every hypothesis below is a clause of `Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated`'s
conclusion or of `Kakeya.ML2Core.exists_windowSeam`'s, except the two the reduction owns: the
`Δ_max` bound on the *original* leaf family (the standing hypothesis of GWZ Main Lemma 2) and the
fullness floor on the retained leaves.  The conclusion is the first factor of triple
product, at the index set the estimate names, in the `δ`-power form the assembly multiplies. -/
theorem exists_fine_factor_at_window {β : ℝ} (hβ0 : 0 ≤ β)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {s s₁ t : Finset ι}
        {V Y : ι → ShadedTube δ E} {v : E} {pτ : ι → ι} {c : NNReal},
        s₁ ⊆ s →
        (∀ i, (Y i).toTube = ((V i).translate v).toTube) →
        (∀ i ∈ s₁, ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ShadedBody.IsCRefinement ({i ∈ s₁ | pτ i ∈ t} : Finset ι)
            (fun i => (Y i).toShadedBody) s₁ (fun i => ((V i).translate v).toShadedBody) c →
        t.Nonempty →
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        (δ : NNReal) ^ η ≤ c * ShadedBody.fullness s₁ (fun i => (V i).toShadedBody) →
        ∃ jτ ∈ t, ShadedBody.multiplicity ({i ∈ s₁ | pτ i = jτ} : Finset ι)
              (fun i => (Y i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-ε) * ((({i ∈ s₁ | pτ i = jτ} : Finset ι)).card : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, hev⟩ := exists_fine_factor.{u} (E := E) hβ0 hKT hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hδ0
  intro ι s s₁ t V Y v pτ c hs₁s hY hball href htne hmax hfull
  have hδ0' : (0 : NNReal) < δ := hδ0
  have hpowpos : (0 : NNReal) < δ ^ η := NNReal.rpow_pos hδ0'
  have hpos : 0 < c * ShadedBody.fullness s₁ (fun i => (V i).toShadedBody) :=
    lt_of_lt_of_le hpowpos hfull
  obtain ⟨jτ, hjτ, hfib⟩ := exists_fine_fibre_fullness (E := E) hδ0' href htne hpos
  refine ⟨jτ, hjτ, ?_⟩
  set f : Finset ι := {i ∈ s₁ | pτ i = jτ} with hf
  have hfs₁ : f ⊆ s₁ := Finset.filter_subset _ _
  refine hδ f Y ?_ ?_ (hfull.trans hfib)
  · intro i hi
    have hc : (Y i).carrier = ((V i).translate v).carrier :=
      congrArg (fun T : Tube δ E => T.carrier) (hY i)
    rw [hc]
    exact hball i (hfs₁ hi)
  · exact (maxDensity_fibre_le (hfs₁.trans hs₁s) hY).trans hmax

end FineFactor

/-! ## the estimate: the coarse factor (GWZ `section9.tex:81–85`) -/

section CoarseFactor

/-- `⌈log log (1/δ)⌉ ≤ log(1/δ)/K + log K` for every `K ≥ 1`: the general form of
`Kakeya.ML2Core.ssfGridLen_le_quarter_log`, which is the case `K = 4` with `log 4 ≤ 2`. -/
theorem ssfGridLen_le_log_div {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {K : ℝ} (hK : 1 ≤ K) :
    (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) / K + Real.log K := by
  set L : ℝ := Real.log (1 / (δ : ℝ)) with hL
  have hd : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hd1 : (δ : ℝ) ≤ 1 := hδ1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hL0 : 0 ≤ L := by
    rw [hL, one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hd.le hd1)
  by_cases h1 : (1 : ℝ) ≤ L
  · have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one h1
    have h : 0 ≤ Real.log L := Real.log_nonneg h1
    have hceil : (⌈Real.log L⌉₊ : ℝ) < Real.log L + 1 := Nat.ceil_lt_add_one h
    have hq : Real.log (L / K) ≤ L / K - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (L / K) = Real.log L - Real.log K := by
      rw [Real.log_div hLpos.ne' hK0.ne']
    have hle : (ssfGridLen δ : ℝ) ≤ Real.log L + 1 := by
      rw [ssfGridLen, ← hL]; exact hceil.le
    rw [hsplit] at hq
    linarith
  · have hlogL : Real.log L ≤ 0 := by
      rcases eq_or_lt_of_le hL0 with h0 | h0
      · rw [← h0]; simp
      · exact Real.log_nonpos h0.le (not_le.mp h1).le
    have hceil0 : ⌈Real.log L⌉₊ = 0 := Nat.ceil_eq_zero.mpr hlogL
    have hz : (ssfGridLen δ : ℝ) = 0 := by rw [ssfGridLen, ← hL, hceil0]; norm_num
    rw [hz]
    have : (0 : ℝ) ≤ L / K := by positivity
    linarith

/-- **For every `c ≥ 0`, `c ⌈log log 1/δ⌉ ≤ log(1/δ)` below an absolute threshold.**

The general form of `Kakeya.ML2Core.exists_threshold_two_mul_ssfGridLen_le_log` (which is `c = 2`,
the value that makes every grid scale of index `≥ 1` at most `1/4`).  The grid length is doubly
logarithmic, so *every* fixed multiple of it is eventually beaten by `log(1/δ)`. -/
theorem exists_threshold_mul_ssfGridLen_le_log {c : ℝ} (hc : 0 ≤ c) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → c * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) := by
  set K : ℝ := max 1 (2 * c) with hKdef
  have hK : (1 : ℝ) ≤ K := le_max_left _ _
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  set B : ℝ := 2 * c * Real.log K + 8 with hBdef
  have hB8 : (8 : ℝ) ≤ B := by
    have : 0 ≤ 2 * c * Real.log K := by positivity
    linarith
  refine ⟨⟨Real.exp (-B), (Real.exp_pos _).le⟩, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_pos]; exact Real.exp_pos _
  · rw [← NNReal.coe_le_coe, NNReal.coe_one]
    change Real.exp (-B) ≤ (1 : ℝ)
    rw [Real.exp_le_one_iff]; linarith
  · intro δ hδ0 hδle
    have hdR : (δ : ℝ) ≤ Real.exp (-B) := hδle
    have hd : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hδ1 : δ ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one]
      refine hdR.trans ?_
      rw [Real.exp_le_one_iff]; linarith
    have hLB : B ≤ Real.log (1 / (δ : ℝ)) := by
      have h1 : Real.log (δ : ℝ) ≤ -B := by simpa using Real.log_le_log hd hdR
      rw [one_div, Real.log_inv]; linarith
    set L : ℝ := Real.log (1 / (δ : ℝ)) with hL
    have hM := ssfGridLen_le_log_div hδ0 hδ1 hK
    rw [← hL] at hM
    have hL0 : 0 ≤ L := by linarith
    have hcK : c / K ≤ 1 / 2 := by
      rcases le_or_gt (2 * c) 1 with h | h
      · have hK1 : K = 1 := by rw [hKdef]; exact max_eq_left h
        rw [hK1]; linarith
      · have hK2 : K = 2 * c := by rw [hKdef]; exact max_eq_right h.le
        rw [hK2]
        have hc0 : 0 < c := by linarith
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
    have hstep1 : c * (L / K) ≤ L / 2 := by
      have hcomm : c * (L / K) = (c / K) * L := by field_simp
      rw [hcomm]
      calc (c / K) * L ≤ (1 / 2) * L := by nlinarith
        _ = L / 2 := by ring
    have hstep2 : c * Real.log K ≤ L / 2 := by
      have h1 : 2 * c * Real.log K ≤ L := by linarith
      linarith
    calc c * (ssfGridLen δ : ℝ) ≤ c * (L / K + Real.log K) := by nlinarith
      _ = c * (L / K) + c * Real.log K := by ring
      _ ≤ L / 2 + L / 2 := by linarith
      _ = L := by ring

/-- **Every grid scale of index `≥ 1` is at most `ρ₀` once `M log(1/ρ₀) ≤ log(1/δ)`.**  The
general form of `Kakeya.ML2Core.gridScale_le_quarter`, whose `ρ₀` is `1/4`. -/
theorem gridScale_le_of_mul_log_le {δ ρ₀ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hρ0 : 0 < ρ₀)
    {M k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M)
    (h : (M : ℝ) * Real.log (1 / (ρ₀ : ℝ)) ≤ Real.log (1 / (δ : ℝ))) :
    Tube.gridScale δ M k ≤ ρ₀ := by
  have hM0 : 0 < M := lt_of_lt_of_le hk hkM
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hd : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hd1 : (δ : ℝ) ≤ 1 := hδ1
  have hr : (0 : ℝ) < (ρ₀ : ℝ) := by exact_mod_cast hρ0
  rw [← NNReal.coe_le_coe]
  have hcoe : ((Tube.gridScale δ M k : NNReal) : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) := by
    rw [Tube.gridScale, NNReal.coe_rpow]
  rw [hcoe]
  have hstep : (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) ≤ (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hd hd1 ?_
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact div_le_div_of_nonneg_right hk1 hMR.le
  refine hstep.trans ?_
  rw [Real.rpow_def_of_pos hd]
  have hlogd : Real.log (δ : ℝ) = -Real.log (1 / (δ : ℝ)) := by rw [one_div, Real.log_inv]; ring
  have hlogr : Real.log (1 / (ρ₀ : ℝ)) = -Real.log (ρ₀ : ℝ) := by rw [one_div, Real.log_inv]
  have hexp : Real.log (δ : ℝ) * ((1 : ℝ) / (M : ℝ)) ≤ Real.log (ρ₀ : ℝ) := by
    rw [hlogd, mul_one_div, neg_div, neg_le, ← hlogr, le_div_iff₀ hMR, mul_comm]
    exact h
  calc Real.exp (Real.log (δ : ℝ) * ((1 : ℝ) / (M : ℝ)))
      ≤ Real.exp (Real.log (ρ₀ : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = (ρ₀ : ℝ) := Real.exp_log hr

/-- **Every grid scale of index `≥ 1` is eventually below any fixed positive `ρ₀`.**

This is the discharge of the smallness threshold that `K_KT(β)` puts on the *tube* scale when it
is applied to the coarse family `𝕋_θ`, whose tubes have thickness `θ = Tube.gridScale δ M a`.  It
holds for `1 ≤ a` and it is false at `a = 0`, where `Tube.gridScale δ M 0 = 1` on the nose
(`Tube.gridScale_zero`). -/
theorem eventually_gridScale_le {ρ₀ : NNReal} (hρ0 : 0 < ρ₀) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ k : ℕ, 1 ≤ k → k ≤ ssfGridLen δ → Tube.gridScale δ (ssfGridLen δ) k ≤ ρ₀ := by
  set c : ℝ := max 0 (Real.log (1 / (ρ₀ : ℝ))) with hc
  have hc0 : 0 ≤ c := le_max_left _ _
  obtain ⟨δ₀, hδ₀0, hδ₀1, hδ₀⟩ := exists_threshold_mul_ssfGridLen_le_log hc0
  filter_upwards [Ioo_mem_nhdsGT hδ₀0] with δ hδ
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδ1 : δ ≤ 1 := hδlt.le.trans hδ₀1
  intro k hk hkM
  refine gridScale_le_of_mul_log_le hδ0 hδ1 hρ0 hk hkM ?_
  have hmono : (ssfGridLen δ : ℝ) * Real.log (1 / (ρ₀ : ℝ)) ≤ (ssfGridLen δ : ℝ) * c :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
  refine hmono.trans ?_
  rw [mul_comm]
  exact hδ₀ δ hδ0 hδlt.le

variable [Nontrivial E]

/-- **the estimate, the analytic core: GWZ Lemma 3.7 with the two scales decoupled.**

At tube scale `θ` and auxiliary scale `dt ≤ θ`, a family of `θ`-tubes in `B₁` with
`λ ≥ dt^{η}` and `Δ_max ≤ dt^{-η_c}` has multiplicity at most `dt^{-(ε + η_c)} |·|^β`.

Two things are load-bearing.  First, the fullness hypothesis is read at `dt`, not at `θ`: what
the reduction owns for the coarse family is `λ(𝕋_θ, Y_θ) ⪆ λ(𝕋, Y) ≥ δ^{η}`, and no fixed `η`
makes that a bound of the form `θ^{η'}` when `θ = δ^{a/M}` with `M = ssfGridLen δ` unbounded.
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` is exactly GWZ Remark 3.6 applied to
Lemma 3.7 and is what decouples them.  Second, `Δ_max` enters only through Lemma 3.7's
`Δ_max^{1-β}` factor, so **no smallness of `η_c` is needed** — which matters, because the window
hands out `η_{j-1}`, an exponent of the ladder that is not small compared with the accuracy.

`θ₀` is the smallness threshold Lemma 3.7 puts on the tube scale; it is discharged for the
window's coarse scale by `Kakeya.ML2Core.eventually_gridScale_le` when `1 ≤ a`. -/
theorem exists_coarse_factor {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : NNReal, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {θ : NNReal}, 0 < θ → θ ≤ θ₀ →
      ∀ (dt : NNReal), 0 < dt → dt ≤ θ →
      ∀ {ηc : ℝ}, 0 ≤ ηc →
      ∀ {ι : Type u} (t : Finset ι) (Y : ι → ShadedTube θ E),
        (∀ k ∈ t, (Y k).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (dt : NNReal) ^ η ≤ ShadedBody.fullness t (fun k => (Y k).toShadedBody) →
        Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ≤ (dt : ENNReal) ^ (-ηc) →
        ShadedBody.multiplicity t (fun k => (Y k).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(ε + ηc)) * (t.card : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, hev⟩ := Kakeya.KatzTaoEstimate.multiplicity_bound_generalize E hβ0 hKT ε hε
  obtain ⟨θ₁, hθ₁0, hth⟩ := Kakeya.StickyKakeya.exists_threshold_of_eventually_nhdsGT hev
  refine ⟨η, hη, min θ₁ 1, lt_min hθ₁0 zero_lt_one, min_le_right _ _, ?_⟩
  intro θ hθ0 hθle dt hdt0 hdtθ ηc hηc ι t Y hball hfull hmax
  have hθ₁ : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθ1 : θ ≤ 1 := hθle.trans (min_le_right _ _)
  have hdt1 : dt ≤ 1 := hdtθ.trans hθ1
  have hdtE1 : (dt : ENNReal) ≤ 1 := by exact_mod_cast hdt1
  have hdtE0 : (dt : ENNReal) ≠ 0 := by simpa using hdt0.ne'
  set Y' : {x // x ∈ t} → ShadedTube θ E := fun x => Y x.1 with hY'
  have hballs : ∀ x : {x // x ∈ t}, (Y' x).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun x => hball x.1 x.2
  have hfull' : ShadedBody.fullness t.attach (fun x => (Y' x).toShadedBody) ≥ dt ^ η := by
    rw [show (fun x : {x // x ∈ t} => (Y' x).toShadedBody)
        = (fun x : {x // x ∈ t} => ((fun i => (Y i).toShadedBody) x.1)) from rfl,
      fullness_attach_val t (fun i => (Y i).toShadedBody)]
    exact hfull
  have hraw := hth hθ0 hθ₁ dt hdt0 hdtθ t.attach Y' hballs hfull'
  rw [show (fun x : {x // x ∈ t} => (Y' x).toShadedBody)
      = (fun x : {x // x ∈ t} => ((fun i => (Y i).toShadedBody) x.1)) from rfl,
    multiplicity_attach_val t (fun i => (Y i).toShadedBody),
    show (fun x : {x // x ∈ t} => (Y' x).toConvexSpaceBody)
      = (fun x : {x // x ∈ t} => ((fun i => (Y i).toConvexSpaceBody) x.1)) from rfl,
    maxDensity_attach_val t (fun i => (Y i).toConvexSpaceBody), Finset.card_attach] at hraw
  refine hraw.trans ?_
  have hdens : Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ^ (1 - β)
      ≤ (dt : ENNReal) ^ (-ηc) := by
    calc Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ^ (1 - β)
        ≤ ((dt : ENNReal) ^ (-ηc)) ^ (1 - β) := ENNReal.rpow_le_rpow hmax (by linarith)
      _ = (dt : ENNReal) ^ (-ηc * (1 - β)) := by rw [← ENNReal.rpow_mul]
      _ ≤ (dt : ENNReal) ^ (-ηc) := by
          refine ENNReal.rpow_le_rpow_of_exponent_ge hdtE1 ?_
          nlinarith
  calc (dt : ENNReal) ^ (-ε) * Kakeya.maxDensity t (fun k => (Y k).toConvexSpaceBody) ^ (1 - β)
        * (t.card : ENNReal) ^ β
      ≤ (dt : ENNReal) ^ (-ε) * (dt : ENNReal) ^ (-ηc) * (t.card : ENNReal) ^ β := by gcongr
    _ = (dt : ENNReal) ^ (-(ε + ηc)) * (t.card : ENNReal) ^ β := by
        rw [← ENNReal.rpow_add _ _ hdtE0 (by simp)]
        ring_nf

open Classical in
/-- **the estimate, wired to the window's `coarse_maxDensity_le` field and coarse family.**

The `Δ_max` hypothesis of `Kakeya.ML2Core.exists_coarse_factor` is discharged in three exact
steps from the window: translation invariance and index-set monotonicity
(`Kakeya.ML2Core.maxDensity_le_of_translate_subset`) carry it from manufactured coarse
shading `Y_θ` back to the hierarchy's own level-`a` nodes, the field
`Kakeya.ML2Reduction.IsKatzTaoDividingWindow.coarse_maxDensity_le` bounds those by
`C_⋆ θ^{-η_{j-1}}`, and `δ ≤ θ ≤ 1` converts the `θ`-power into a `δ`-power.  `C_⋆` is absorbed
by the caller's `hCstar`, which is the standard subpolynomial absorption of the reduction.

`hball` — the level-`a` nodes lying in `B₁` after the seam's translation — is **not** a
consequence of output: seam is run at the fine level `b`, and a level-`a` node
containing a normalised level-`b` node lies only in `B̄(0, 1 + 4θ)`.  It is an explicit
hypothesis; running the seam at the coarse level instead would supply it, and the fine data with
it, by nestedness. -/
theorem exists_coarse_factor_at_window {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : NNReal, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {δ Cst : NNReal} {ι : Type u} {s : Finset ι} {T : ι → Tube δ E}
        {𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cst} {Cstar : ENNReal} {ηl : ℕ → ℝ}
        {εd : ℝ} {N a b m : ℕ} {κ : ℝ} {t : Finset ι}
        {Yθ : ι → ShadedTube (Tube.gridScale δ (ssfGridLen δ) a) E} {v : E},
        0 < δ → δ ≤ 1 →
        Tube.gridScale δ (ssfGridLen δ) a ≤ θ₀ →
        Kakeya.ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar ηl εd N a b m →
        0 ≤ ηl m → 0 ≤ κ →
        Cstar ≤ (δ : ENNReal) ^ (-κ) →
        t ⊆ 𝒰.cover.indexSet a →
        (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
        (∀ k ∈ t, (Yθ k).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (δ : NNReal) ^ η ≤ ShadedBody.fullness t (fun k => (Yθ k).toShadedBody) →
        ShadedBody.multiplicity t (fun k => (Yθ k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(ε + (κ + ηl m))) * (t.card : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, θ₀, hθ₀0, hθ₀1, hcore⟩ := exists_coarse_factor.{u} (E := E) hβ0 hβ1 hKT hε
  refine ⟨η, hη, θ₀, hθ₀0, hθ₀1, ?_⟩
  intro δ Cst ι s T 𝒰 Cstar ηl εd N a b m κ t Yθ v hδ0 hδ1 hθle hw hηm hκ hCstar htu hY hball hfull
  have haM : a ≤ ssfGridLen δ := le_trans hw.coarse_lt_fine.le hw.fine_le_gridLen
  have hθ0 : 0 < Tube.gridScale δ (ssfGridLen δ) a := Tube.gridScale_pos hδ0 _ _
  have hδθ : δ ≤ Tube.gridScale δ (ssfGridLen δ) a := delta_le_gridScale hδ0 hδ1 haM
  have hmax : Kakeya.maxDensity t (fun k => (Yθ k).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-(κ + ηl m)) := by
    have h1 : Kakeya.maxDensity t (fun k => (Yθ k).toConvexSpaceBody)
        ≤ Kakeya.maxDensity (𝒰.cover.indexSet a)
            (fun k => (𝒰.cover.tube a k).toConvexSpaceBody) :=
      maxDensity_le_of_translate_subset htu hY
    have h2 := hw.coarse_maxDensity_le
    have h3 : ENNReal.ofReal (((Tube.gridScale δ (ssfGridLen δ) a : NNReal) : ℝ) ^ (-ηl m))
        = ((Tube.gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal) ^ (-ηl m) :=
      ofReal_rpow_coe hθ0 _
    rw [h3] at h2
    have h4 : ((Tube.gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal) ^ (-ηl m)
        ≤ (δ : ENNReal) ^ (-ηl m) :=
      rpow_neg_le_rpow_neg_of_le hδθ hηm
    have h5 : Cstar * ((Tube.gridScale δ (ssfGridLen δ) a : NNReal) : ENNReal) ^ (-ηl m)
        ≤ (δ : ENNReal) ^ (-κ) * (δ : ENNReal) ^ (-ηl m) :=
      mul_le_mul' hCstar h4
    have hδE0 : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
    have h6 : (δ : ENNReal) ^ (-κ) * (δ : ENNReal) ^ (-ηl m)
        = (δ : ENNReal) ^ (-(κ + ηl m)) := by
      rw [← ENNReal.rpow_add _ _ hδE0 (by simp)]
      ring_nf
    rw [h6] at h5
    exact (h1.trans h2).trans h5
  exact hcore hθ0 hθle δ hδ0 hδθ (by linarith) t Yθ hball hfull hmax

end CoarseFactor

/-! ## compatibility: output is input -/

section Tripwire

variable [Nontrivial E]

open Classical in
/-- **compatibility: the two-scale split and the fine factor compose.**

From the seam's translated configuration and the standing `Δ_max` and fullness hypotheses of GWZ
Main Lemma 2, this produces triple product *together with* the fine factor's bound at a
retained node `jτ` of own choosing.  Its only purpose is that the compiler adjudicate the
interface: the fibre index set, the shaded family and the refinement constant of
`Kakeya.ML2Core.exists_fine_factor_at_window` are, verbatim, the ones
`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated` produces, so no adapter stands between
the component estimates any drift in either statement breaks this declaration. -/
theorem exists_twoScale_with_fine_factor {β : ℝ} (hβ0 : 0 ≤ β)
    (hKT : Kakeya.KatzTaoEstimate.{u} E β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ} {σ : ℕ → NNReal}
        (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ) {a b : ℕ},
        a ≤ b → a ≤ N → b ≤ N → δ ≤ σ b → σ b ≤ σ a → σ a ≤ 1 →
        ∀ (v : E) {t₁ : Finset ι}, t₁ ⊆ Kakeya.ML2Reduction.activeNodes 𝒞 b →
        (∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι),
          ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) →
        Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        (δ : NNReal) ^ η
          ≤ (Kakeya.ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ)⁻¹
            * ShadedBody.fullness ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
                (fun i => (V i).toShadedBody) →
        0 < ∑ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι), volume (V i).shade →
        ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ 𝒞.indexSet a,
          ∃ (Yτ' : ι → ShadedTube (σ b) E) (Yθ : ι → ShadedTube (σ a) E)
            (Y' : ι → ShadedTube δ E),
            (∀ jτ ∈ tτ', ∀ jθ ∈ tθ',
              ShadedBody.multiplicity ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
                  (fun i => (V i).toShadedBody)
                ≤ ((Kakeya.ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                        ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
                      Kakeya.ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b)
                        : NNReal) : ENNReal)
                  * ShadedBody.multiplicity
                      {i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i = jτ}
                      (fun i => (Y' i).toShadedBody)
                  * ShadedBody.multiplicity {j ∈ tτ' | Kakeya.ML2Reduction.coarseNode 𝒞 a b j = jθ}
                      (fun j => (Yτ' j).toShadedBody)
                  * ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)) ∧
            ∃ jτ ∈ tτ',
              ShadedBody.multiplicity
                  ({i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i = jτ} : Finset ι)
                  (fun i => (Y' i).toShadedBody)
                ≤ (δ : ENNReal) ^ (-ε)
                  * ((({i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i = jτ}
                        : Finset ι)).card : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, hev⟩ := exists_fine_factor_at_window.{u} (E := E) hβ0 hKT hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with δ hfine hδ0
  intro ι s V N σ 𝒞 a b hab haN hbN hδτ hτθ hθ1 v t₁ ht₁ hballt hballs hmax hfull hmass
  obtain ⟨tτ', htτ', tθ', htθ', _Yτ, Yτ', Yθ, Y', _hcard, _h1, _h2, _h3, hY'tube, _h5, _h6,
      hne, href1, _href2, _hfull1, _hfull2, hprod⟩ :=
    exists_spineTwoScale_ofChain_translated (E := E) hδ0 𝒞 hab haN hbN hδτ hτθ hθ1 v ht₁
      hballt hballs
  obtain ⟨hτne, _hθne⟩ := hne hmass
  refine ⟨tτ', htτ', tθ', htθ', Yτ', Yθ, Y', hprod, ?_⟩
  exact hfine (Finset.filter_subset _ _) hY'tube hballs href1 hτne hmax hfull

end Tripwire

end Kakeya.ML2Core
