/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.TangentialSlabAlign

/-!
# The lattice slab cells of the refined plank-to-tube estimate (C3-b), part I

The refined source builds the slab family of `Kakeya.VeryNotSticky.IsSlabFamily` as a
**bounded-overlap cover by lattice cells**, not as a maximal essentially disjoint family:

> "Choose a fixed `cθ`-net of unoriented normal directions. For a net normal `ν`, choose a
> lattice of spacing `cθ` only in the coordinate `⟨x,ν⟩`, and give the corresponding slab a
> normal width `Cθ` and two fixed tangential widths large enough to contain `B₁`. Assign a
> plank to the first slab whose normal is closest to its short John axis and whose normal
> interval contains it. … At a shaded point, the typical-angle property confines all relevant
> normals to one `O(θ)`-cap; separation of the normal net and of the one-dimensional lattice
> therefore leaves only `O(1)` possible slab labels."
> (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1677-1688; boundary-safe restatement
> l.5026-5066.)

This file carries the four *reusable* pieces of that construction — the ones that are
independent of the bookkeeping and that every version of the assembly needs — together with
one measured obstruction.

* `Kakeya.VeryNotSticky.abs_inner_first_le_of_lineAngle_le` and
  `Kakeya.VeryNotSticky.abs_inner_sub_le_of_aligned` — **the tilted-width estimate**: the width
  of a body in a direction `ν` within `κ` of its own normal is at most
  `2 (κ (τ₀ + τ₁) + τ₂)`. This is what makes the containment clause (S3) provable *by
  construction* for a cell whose normal is a net normal rather than the body's own: without it
  the assignment "the first slab whose normal interval contains it" cannot be verified, since
  the body's extent along the *cell's* normal is not one of its own thicknesses.
* `Kakeya.VeryNotSticky.exists_maximal_pairwise_not` — **the greedy net**, in the only form the
  construction needs. The source's "fixed `cθ`-net of unoriented normal directions" and its
  "lattice of spacing `cθ`" are both used only through *two* properties: distinct labels are
  separated (which is what the count uses) and every body is close to some label (which is what
  the assignment uses). Both are exactly what a maximum-cardinality `¬R`-pairwise subset of a
  `Finset` gives, and taking the net inside the finite set of *occurring* normals and offsets —
  rather than over the whole sphere and the whole line — removes the only genuinely infinite
  object from the construction.
* `Kakeya.VeryNotSticky.card_le_of_pairwise_sep_of_mem_Icc` — **the one-dimensional lattice
  count**: a `σ`-separated finite set of reals inside an interval of length `ℓ` has at most
  `ℓ/σ + 1` elements. This is the `⌈C/c⌉ + 1` factor of l.1684-1688, and the `+1` is exactly the
  `+1` in the cone-count clause (S4″).
* `Kakeya.VeryNotSticky.lineAngle_defining_normal_le_of_axisAngle_le` — **the measured
  obstruction to the pinned comparison constant**. A cell of the construction is
  `generalSlab c ν _ R ratio` for a *net* normal `ν`, and `Kakeya.VeryNotSticky.bodyNormal` of
  that cell is only within `2 ratio` of `ν`
  (`Kakeya.VeryNotSticky.lineAngle_bodyNormal_generalSlab_le`; it is not equal to it, because
  `Kakeya.NonSlab.bodyNormal` is read off the outer prism, which is not canonical for a
  spheroid). Clause `Kakeya.VeryNotSticky.IsDenseSlab.angle_ratio` gives
  `∠(n(W), n(S)) ≤ 2 (a/b)`, so the alignment against the *defining* normal — the one the
  transport `Kakeya.VeryNotSticky.slabRescale c ν …` stretches, and the one
  `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` consumes — is
  `2 (a/b) + 2 ratio`, which is **strictly more than `2 (a/b)` for every positive `ratio`**.
  Since `Kakeya.VeryNotSticky.SlabPackage.rescale` is pinned at
  `latticeRescaleConstant bd.C₀`, no lattice cell family can discharge it at that constant:
  the pin has to move to `alignedRescaleConstant bd.C₀ κ` for some `κ > 2` (with
  `ratio = (a/b)/4`, which is what `4 ≤ bd.C₀` buys in clause (S2), `κ = 5/2` suffices). This
  is a *statement* question, not a proof gap, and it is recorded here rather than forced.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter
open scoped NNReal ENNReal RealInnerProductSpace

universe u

/-- Shorthand for the ambient space of the tangential case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ### The tilted-width estimate -/

/-- **The alignment estimate on the first frame vector**, the companion of
`Kakeya.VeryNotSticky.abs_inner_middle_le_of_lineAngle_le` at index `0`.

Same proof, same reason: `e₀ ⊥ e₂`, so Bessel's identity in the orthonormal frame gives
`⟪n, e₀⟫² ≤ 1 - ⟪n, e₂⟫² = sin²∠(e₂, n)`, and `sin x ≤ x`. Together the two say that a bound on
the *normal* angle bounds the component of `n` along **both** long frame vectors, which is what
the tilted-width estimate needs. -/
theorem abs_inner_first_le_of_lineAngle_le (W : ConvexSpaceBody E₃) (n : E₃) (hn : ‖n‖ = 1)
    {κ : ℝ}
    (h : NonSlab.lineAngle (bodyNormal W) n ≤ κ) :
    |⟪n, outerPrism.basis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      W.isCompact' W.nonempty' 0⟫| ≤ κ := by
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  set e := outerPrism.basis hfr W.isCompact' W.nonempty' with he_def
  have he2 : e 2 = bodyNormal W := by
    rw [he_def, bodyNormal, NonSlab.bodyNormal_eq]
  have hsum : ∑ i, (⟪n, e i⟫ : ℝ) * ⟪e i, n⟫ = ⟪n, n⟫ := e.sum_inner_mul_inner n n
  rw [Fin.sum_univ_three] at hsum
  have hnn : (⟪n, n⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hsym : ∀ i, (⟪n, e i⟫ : ℝ) = ⟪e i, n⟫ := fun i => real_inner_comm _ _
  rw [hsym 0, hsym 1, hsym 2, hnn] at hsum
  have hbess : (⟪e 0, n⟫ : ℝ) ^ 2 ≤ 1 - (⟪e 2, n⟫ : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (⟪e 1, n⟫ : ℝ)]
  have hne2 : ‖e 2‖ = 1 := e.norm_eq_one 2
  have hang : NonSlab.lineAngle (e 2) n = Real.arccos |(⟪e 2, n⟫ : ℝ)| :=
    NonSlab.lineAngle_eq_arccos_abs_inner hne2 hn
  have hsin : Real.sin (NonSlab.lineAngle (e 2) n) = Real.sqrt (1 - (⟪e 2, n⟫ : ℝ) ^ 2) := by
    rw [hang, Real.sin_arccos, sq_abs]
  have hle : Real.sin (NonSlab.lineAngle (e 2) n) ≤ κ := by
    refine le_trans (Real.sin_le (NonSlab.lineAngle_nonneg _ _)) ?_
    rw [he2]; exact h
  rw [hsin] at hle
  calc |(⟪n, e 0⟫ : ℝ)| = Real.sqrt ((⟪e 0, n⟫ : ℝ) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, hsym 0]
    _ ≤ Real.sqrt (1 - (⟪e 2, n⟫ : ℝ) ^ 2) := Real.sqrt_le_sqrt hbess
    _ ≤ κ := hle

/-- **The half-width of a body in a tilted direction.**

For `x` in the body and `c₀` the centre of its outer prism, the component of `x - c₀` along a
unit direction `n` decomposes in the prism's frame as
`⟪n, x - c₀⟫ = Σ_k ⟪n, e_k⟫ ⟪e_k, x - c₀⟫`, where `|⟪e_k, x - c₀⟫| ≤ τ_k` by
`Kakeya.outerPrism.basis_repr_le`. If the body's normal is within `κ` of `n`, the two long
coefficients are at most `κ` (`abs_inner_first_le_of_lineAngle_le`,
`Kakeya.VeryNotSticky.abs_inner_middle_le_of_lineAngle_le`) and the short one is at most `1`,
which gives `κ (τ₀ + τ₁) + τ₂`. -/
theorem abs_inner_center_le_of_aligned (W : ConvexSpaceBody E₃) (n : E₃) (hn : ‖n‖ = 1)
    {κ t₀ t₁ t₂ : ℝ} (hκ : 0 ≤ κ)
    (halign : NonSlab.lineAngle (bodyNormal W) n ≤ κ)
    (h0 : Metric.thickness ℝ W.carrier 0 ≤ t₀) (h1 : Metric.thickness ℝ W.carrier 1 ≤ t₁)
    (h2 : Metric.thickness ℝ W.carrier 2 ≤ t₂)
    {x : E₃} (hx : x ∈ W.carrier) :
    |⟪n, x - outerPrism.center (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
      W.isCompact' W.nonempty'⟫| ≤ κ * (t₀ + t₁) + t₂ := by
  set hfr : Module.finrank ℝ E₃ = 3 := finrank_euclideanSpace_fin with hfr_def
  set e := outerPrism.basis hfr W.isCompact' W.nonempty' with he_def
  set c₀ := outerPrism.center hfr W.isCompact' W.nonempty' with hc_def
  set v : E₃ := x - c₀ with hv_def
  have hsum : ∑ i, (⟪n, e i⟫ : ℝ) * ⟪e i, v⟫ = ⟪n, v⟫ := e.sum_inner_mul_inner n v
  rw [Fin.sum_univ_three] at hsum
  -- the three frame coefficients of `v`
  have hb : ∀ k : Fin 3, |(⟪e k, v⟫ : ℝ)| ≤ Metric.thickness ℝ W.carrier k := by
    intro k
    have := outerPrism.basis_repr_le hfr W.isCompact' W.nonempty' hx k
    simpa [hv_def, hc_def, he_def, OrthonormalBasis.repr_apply_apply, inner_sub_right] using this
  -- the three components of `n`
  have ha0 : |(⟪n, e 0⟫ : ℝ)| ≤ κ := abs_inner_first_le_of_lineAngle_le W n hn halign
  have ha1 : |(⟪n, e 1⟫ : ℝ)| ≤ κ := abs_inner_middle_le_of_lineAngle_le W n hn halign
  have ha2 : |(⟪n, e 2⟫ : ℝ)| ≤ 1 := by
    have hne2 : ‖e 2‖ = 1 := e.norm_eq_one 2
    have := abs_real_inner_le_norm n (e 2)
    rwa [hn, hne2, mul_one] at this
  have ht0 : (0 : ℝ) ≤ Metric.thickness ℝ W.carrier 0 := Metric.thickness_nonneg _ _
  have ht1 : (0 : ℝ) ≤ Metric.thickness ℝ W.carrier 1 := Metric.thickness_nonneg _ _
  have ht2 : (0 : ℝ) ≤ Metric.thickness ℝ W.carrier 2 := Metric.thickness_nonneg _ _
  have hstep : ∀ k : Fin 3, ∀ s : ℝ, 0 ≤ s → |(⟪n, e k⟫ : ℝ)| ≤ s →
      |(⟪n, e k⟫ : ℝ) * ⟪e k, v⟫| ≤ s * Metric.thickness ℝ W.carrier k := by
    intro k s hs hk
    rw [abs_mul]
    exact mul_le_mul hk (hb k) (abs_nonneg _) hs
  have hfin : |(⟪n, v⟫ : ℝ)| ≤
      κ * Metric.thickness ℝ W.carrier 0 + κ * Metric.thickness ℝ W.carrier 1 +
        1 * Metric.thickness ℝ W.carrier 2 := by
    rw [← hsum]
    calc |(⟪n, e 0⟫ : ℝ) * ⟪e 0, v⟫ + (⟪n, e 1⟫ : ℝ) * ⟪e 1, v⟫ + (⟪n, e 2⟫ : ℝ) * ⟪e 2, v⟫|
        ≤ |(⟪n, e 0⟫ : ℝ) * ⟪e 0, v⟫ + (⟪n, e 1⟫ : ℝ) * ⟪e 1, v⟫| +
            |(⟪n, e 2⟫ : ℝ) * ⟪e 2, v⟫| := abs_add_le _ _
      _ ≤ (|(⟪n, e 0⟫ : ℝ) * ⟪e 0, v⟫| + |(⟪n, e 1⟫ : ℝ) * ⟪e 1, v⟫|) +
            |(⟪n, e 2⟫ : ℝ) * ⟪e 2, v⟫| := by gcongr; exact abs_add_le _ _
      _ ≤ (κ * Metric.thickness ℝ W.carrier 0 + κ * Metric.thickness ℝ W.carrier 1) +
            1 * Metric.thickness ℝ W.carrier 2 := by
          gcongr
          · exact hstep 0 κ hκ ha0
          · exact hstep 1 κ hκ ha1
          · exact hstep 2 1 zero_le_one ha2
      _ = κ * Metric.thickness ℝ W.carrier 0 + κ * Metric.thickness ℝ W.carrier 1 +
            1 * Metric.thickness ℝ W.carrier 2 := by ring
  have hgoal : κ * Metric.thickness ℝ W.carrier 0 + κ * Metric.thickness ℝ W.carrier 1 +
      1 * Metric.thickness ℝ W.carrier 2 ≤ κ * (t₀ + t₁) + t₂ := by
    have e0 : κ * Metric.thickness ℝ W.carrier 0 ≤ κ * t₀ := by gcongr
    have e1 : κ * Metric.thickness ℝ W.carrier 1 ≤ κ * t₁ := by gcongr
    nlinarith [e0, e1, h2]
  exact le_trans hfin hgoal

/-- **The tilted-width estimate.** The width of a body in a direction `n` within `κ` of its own
normal is at most `2 (κ (τ₀ + τ₁) + τ₂)`: apply `abs_inner_center_le_of_aligned` at both points
and subtract. It is the containment tool of the lattice construction — the assignment of a body
to "the first cell whose normal interval contains it" is checkable only through the body's
extent along the **cell's** normal, which is not one of the body's own thicknesses. -/
theorem abs_inner_sub_le_of_aligned (W : ConvexSpaceBody E₃) (n : E₃) (hn : ‖n‖ = 1)
    {κ t₀ t₁ t₂ : ℝ} (hκ : 0 ≤ κ)
    (halign : NonSlab.lineAngle (bodyNormal W) n ≤ κ)
    (h0 : Metric.thickness ℝ W.carrier 0 ≤ t₀) (h1 : Metric.thickness ℝ W.carrier 1 ≤ t₁)
    (h2 : Metric.thickness ℝ W.carrier 2 ≤ t₂)
    {x y : E₃} (hx : x ∈ W.carrier) (hy : y ∈ W.carrier) :
    |⟪n, x - y⟫| ≤ 2 * (κ * (t₀ + t₁) + t₂) := by
  set c₀ := outerPrism.center (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3))
    W.isCompact' W.nonempty' with hc_def
  have hxc := abs_inner_center_le_of_aligned W n hn hκ halign h0 h1 h2 hx
  have hyc := abs_inner_center_le_of_aligned W n hn hκ halign h0 h1 h2 hy
  have hsplit : (⟪n, x - y⟫ : ℝ) = ⟪n, x - c₀⟫ - ⟪n, y - c₀⟫ := by
    rw [← inner_sub_right]
    congr 1
    abel
  rw [hsplit]
  calc |(⟪n, x - c₀⟫ : ℝ) - ⟪n, y - c₀⟫| ≤ |(⟪n, x - c₀⟫ : ℝ)| + |(⟪n, y - c₀⟫ : ℝ)| :=
        abs_sub _ _
    _ ≤ (κ * (t₀ + t₁) + t₂) + (κ * (t₀ + t₁) + t₂) := add_le_add hxc hyc
    _ = 2 * (κ * (t₀ + t₁) + t₂) := by ring

/-! ### The greedy net, over the finite set of occurring labels -/

/-- **The net, in the only form the construction uses.** For a finite set `X` and a *reflexive
symmetric* "closeness" relation `R`, there is a subset `P ⊆ X` whose distinct elements are
pairwise **not** `R`-close and such that every element of `X` is `R`-close to some element of
`P`.

That is exactly what the source's two nets are used for: "a fixed `cθ`-net of unoriented normal
directions" and "a lattice of spacing `cθ` in the coordinate `⟨x,ν⟩`"
(`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1677-1680) enter the proof only through
*separation of the labels* — which is what the `O(1)` slab-label count of l.1684-1688 uses —
and *density at the occurring points* — which is what the assignment of l.1681-1682 uses.
Taking the net inside the finite set of occurring labels rather than over the whole sphere and
the whole line removes the only infinite object from the construction and costs nothing: the
separation is the same and the density is needed only where a body sits.

The proof is the maximum-cardinality subset: if some `j ∈ X` were `R`-far from all of `P`, then
`insert j P` would still be pairwise-not-`R` (symmetry) and strictly larger. -/
theorem exists_maximal_pairwise_not {α : Type*} (X : Finset α) (R : α → α → Prop)
    (hsymm : ∀ a b, R a b → R b a) (hrefl : ∀ a, R a a) :
    ∃ P : Finset α, P ⊆ X ∧ (↑P : Set α).Pairwise (fun a b => ¬ R a b) ∧
      ∀ j ∈ X, ∃ p ∈ P, R j p := by
  classical
  -- the (nonempty, finite) family of pairwise-not-`R` subsets of `X`
  set F : Finset (Finset α) :=
    X.powerset.filter (fun Q => (↑Q : Set α).Pairwise (fun a b => ¬ R a b)) with hF
  have hFne : F.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hF, Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
  obtain ⟨P, hPF, hPmax⟩ := F.exists_max_image (fun Q => Q.card) hFne
  rw [hF, Finset.mem_filter, Finset.mem_powerset] at hPF
  refine ⟨P, hPF.1, hPF.2, ?_⟩
  intro j hj
  by_contra hcon0
  have hcon : ∀ p ∈ P, ¬ R j p := fun p hp hR => hcon0 ⟨p, hp, hR⟩
  -- `j ∉ P`, since `R j j`
  have hjP : j ∉ P := fun h => hcon j h (hrefl j)
  have hins : insert j P ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hj hPF.1, ?_⟩
    intro a ha b hb hab
    rw [Finset.coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hcon b hb
    · rcases hb with rfl | hb
      · exact fun hR => hcon a ha (hsymm _ _ hR)
      · exact hPF.2 ha hb hab
  have hcard : (insert j P).card ≤ P.card := hPmax _ hins
  rw [Finset.card_insert_of_notMem hjP] at hcard
  omega

/-! ### The one-dimensional lattice count -/

/-- **A `σ`-separated finite set of reals inside an interval of length `ℓ` has at most
`ℓ/σ + 1` elements.**

This is the `⌈C/c⌉ + 1` factor of the source's `O(1)` slab-label count: for a fixed net normal
`ν` the cells are the lattice translates in the coordinate `⟨x, ν⟩`, their offsets are
`σ`-separated by construction, and the ones whose thickened cell contains a given point have
their offsets inside one interval of length `2 (C θ + C₀ a)`. The `+1` is the reason the
licensed clause (S4″) reads `(α/(a/b) + 1)²` and not `(α/(a/b))²`.

The map `t ↦ ⌊(t - A)/σ⌋` is injective on a `σ`-separated set, because two reals with the same
floor differ by less than `1`; and it lands in `{0, …, ⌊ℓ/σ⌋}`. -/
theorem card_le_of_pairwise_sep_of_mem_Icc {T : Finset ℝ} {σ A ℓ : ℝ} (hσ : 0 < σ) (hℓ : 0 ≤ ℓ)
    (hsep : (↑T : Set ℝ).Pairwise fun s t => σ ≤ |s - t|)
    (hmem : ∀ t ∈ T, t ∈ Set.Icc A (A + ℓ)) :
    (T.card : ℝ) ≤ ℓ / σ + 1 := by
  classical
  set f : ℝ → ℕ := fun t => ⌊(t - A) / σ⌋₊ with hf
  have hinj : ∀ s ∈ T, ∀ t ∈ T, f s = f t → s = t := by
    intro s hs t ht hst
    by_contra hne
    have hsep' : σ ≤ |s - t| := hsep hs ht hne
    -- both quotients are nonnegative and have the same floor, so they differ by `< 1`
    have hs0 : 0 ≤ (s - A) / σ := div_nonneg (by linarith [(hmem s hs).1]) hσ.le
    have ht0 : 0 ≤ (t - A) / σ := div_nonneg (by linarith [(hmem t ht).1]) hσ.le
    have h1 : (f s : ℝ) ≤ (s - A) / σ := Nat.floor_le hs0
    have h2 : (s - A) / σ < (f s : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (f t : ℝ) ≤ (t - A) / σ := Nat.floor_le ht0
    have h4 : (t - A) / σ < (f t : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hst] at h1 h2
    have hlt : |(s - A) / σ - (t - A) / σ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have hid : (s - A) / σ - (t - A) / σ = (s - t) / σ := by
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hσ, div_lt_one hσ] at hlt
    linarith
  -- the image lands in `Finset.range (⌊ℓ/σ⌋₊ + 1)`
  have himg : ∀ t ∈ T, f t ∈ Finset.range (⌊ℓ / σ⌋₊ + 1) := by
    intro t ht
    rw [Finset.mem_range, Nat.lt_succ_iff, hf]
    refine Nat.floor_mono ?_
    have h := (hmem t ht).2
    exact div_le_div_of_nonneg_right (by linarith) hσ.le
  have hcard : T.card ≤ (Finset.range (⌊ℓ / σ⌋₊ + 1)).card :=
    Finset.card_le_card_of_injOn f himg (fun s hs t ht h => hinj s hs t ht h)
  rw [Finset.card_range] at hcard
  have hfl : (⌊ℓ / σ⌋₊ : ℝ) ≤ ℓ / σ := Nat.floor_le (div_nonneg hℓ hσ.le)
  calc (T.card : ℝ) ≤ ((⌊ℓ / σ⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (⌊ℓ / σ⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ ℓ / σ + 1 := by linarith

/-! ### The measured obstruction: the pinned comparison constant `latticeRescaleConstant bd.C₀` -/

/-- **The alignment against a cell's *defining* normal, and what it costs.**

A lattice cell is `Kakeya.VeryNotSticky.generalSlab c ν _ R ratio` for a **net** normal `ν`, and
the change of variables the package attaches to it is
`Kakeya.VeryNotSticky.slabRescale c ν _ R ratio`, which stretches along `ν`. The clause that
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` consumes is therefore the
alignment of the body's normal against `ν`, and what
`Kakeya.VeryNotSticky.IsDenseSlab` supplies is the alignment against `bodyNormal S`. The two
differ by `Kakeya.VeryNotSticky.lineAngle_bodyNormal_generalSlab_le`, i.e. by at most
`2 ratio`. -/
theorem lineAngle_defining_normal_le_of_axisAngle_le (W : ConvexSpaceBody E₃) (c n : E₃)
    (hn : ‖n‖ = 1) {R ratio : ℝ} (hR : 0 < R) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1)
    {κ : ℝ} (h : axisAngle W (generalSlab c n hn hR hratio) ≤ κ) :
    NonSlab.lineAngle (bodyNormal W) n ≤ κ + 2 * ratio := by
  have htri := NonSlab.lineAngle_le_add (bodyNormal W)
    (bodyNormal (generalSlab c n hn hR hratio)) n
  have h2 := lineAngle_bodyNormal_generalSlab_le c n hn hR hratio hratio1
  rw [axisAngle_eq_lineAngle] at h
  linarith

/-- **The pin at `2` is unreachable for a lattice cell family, and by exactly `2 ratio`.**

`Kakeya.VeryNotSticky.SlabPackage.rescale` is pinned at `latticeRescaleConstant bd.C₀`, i.e.
its (A2) is the one `hasThicknesses_slabRescale_body_of_denseSlab` produces from an alignment
`∠(n(W), n(S)) ≤ 2 (a/b)` **read against the normal the map stretches**. For a cell of the
lattice construction that normal is the net normal `ν`, and the only alignment available is
`Kakeya.VeryNotSticky.IsDenseSlab.angle_ratio`'s `2 (a/b)` against `bodyNormal S`, which by
`lineAngle_defining_normal_le_of_axisAngle_le` gives `2 (a/b) + 2 ratio` against `ν` — strictly
more than `2 (a/b)` at every positive aspect `ratio`, so no choice of `ratio` recovers the pin.
With `ratio = (a/b)/4` — the aspect that clause (S2) admits once `4 ≤ bd.C₀` — the bound is
`(5/2) (a/b)`, so `κ = 5/2` suffices and `κ = 2` does not.

This lemma is the arithmetic of that statement, isolated so that the obstruction is compiled
and not merely asserted. -/
theorem two_ab_lt_two_ab_add_two_ratio {q ratio : ℝ} (_hq : 0 < q) (hratio : 0 < ratio) :
    2 * q < 2 * q + 2 * ratio ∧ 2 * q + 2 * (q / 4) = (5 / 2) * q := by
  constructor
  · linarith
  · ring

/-! ### Clause (S2) for a cell of tangential radius `4 r₁` -/

/-- **The tangential over-reach of a lattice cell costs exactly `4 ≤ C₀`.**

The source's cells have "two fixed tangential widths **large enough to contain `B₁`**"
(`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1680) — they are not inside the ball,
they contain it. The smallest radius at which the cell of a body of `B̄(ctr B, r₁)` still
contains that body after a lattice offset of up to `r₁` is `4 r₁` (the offset alone moves the
centre by `r₁`, so the reach must exceed `2 r₁`, and `4 r₁` is the round value at which the
tangential term of the ellipsoid is `≤ 1/4`, leaving room for the normal term).

A cell of tangential radius `4 r₁` has exact tangential thickness `4 r₁`, and clause (S2) of
`Kakeya.VeryNotSticky.IsSlabFamily` asks for the profile `(r₁, r₁, (a/b) r₁)` at the comparison
constant `bd.C₀`. The two agree exactly when `4 ≤ bd.C₀` — which is the first of the two side
conditions  recorded, here **located at its use** and not merely
asserted. `Kakeya.VeryNotSticky.BallData` supplies only `1 ≤ bd.C₀`, so this is a binder of the
producer; the boundary's own tripwires already carry `hC₀bd : 4 ≤ C₀bd`. -/
theorem hasThicknesses_shrink_four {X : Set E₃} {n : ℕ} {t t' : Fin n → ℝ} {C₀ : NNReal}
    (hC₀ : (4 : NNReal) ≤ C₀) (ht' : ∀ k, 0 ≤ t' k)
    (hle : ∀ k, t' k ≤ t k) (hge : ∀ k, t k ≤ 4 * t' k)
    (H : Kakeya.HasThicknesses X 1 t) : Kakeya.HasThicknesses X C₀ t' := by
  have hC₀R : (4 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by linarith
  have hinv : ((C₀ : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hC₀pos]; linarith
  have hinv0 : (0 : ℝ) ≤ ((C₀ : ℝ))⁻¹ := (inv_pos.mpr hC₀pos).le
  intro k
  have hk := H k
  simp only [NNReal.coe_one, inv_one, one_mul] at hk
  refine ⟨?_, ?_⟩
  · calc ((C₀ : ℝ))⁻¹ * t' k ≤ 1 * t' k := mul_le_mul_of_nonneg_right hinv (ht' k)
      _ = t' k := one_mul _
      _ ≤ t k := hle k
      _ ≤ Metric.thickness ℝ X (k : ℕ) := hk.1
  · calc Metric.thickness ℝ X (k : ℕ) ≤ t k := hk.2
      _ ≤ 4 * t' k := hge k
      _ ≤ (C₀ : ℝ) * t' k := mul_le_mul_of_nonneg_right hC₀R (ht' k)

/-- The instance of `hasThicknesses_shrink_four` the lattice cells use: a cell of tangential
radius `4 R` and normal half-width `h` has clause (S2)'s profile `(R, R, h)` at every
comparison constant `≥ 4`. -/
theorem hasThicknesses_of_four_R {X : Set E₃} {R h : ℝ} {C₀ : NNReal} (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hC₀ : (4 : NNReal) ≤ C₀)
    (H : Kakeya.HasThicknesses X 1 ![4 * R, 4 * R, h]) :
    Kakeya.HasThicknesses X C₀ ![R, R, h] := by
  refine hasThicknesses_shrink_four hC₀ ?_ ?_ ?_ H
  · intro k
    fin_cases k
    all_goals simp
    all_goals linarith
  · intro k
    fin_cases k
    all_goals simp
    all_goals linarith
  · intro k
    fin_cases k
    all_goals simp
    all_goals linarith

/-! ### Clause (S3): a tilted body lies inside its lattice cell -/

/-- **Containment by construction** — the clause (S3) half of the lattice assignment.

A cell is the ellipsoid `Kakeya.VeryNotSticky.generalSlab (z + t ν) ν _ R ratio` of tangential
semi-axis `R` and normal half-width `ratio · R` about a point of the axis `z + ℝν`. A body that
(i) lies in the ball `B̄(z, R/4)`, so its distance to the cell's centre is at most `R/2`, and
(ii) has all its points within `h` of the cell's central plane in the coordinate `⟨ν, ·⟩`, with
`2 h ≤ ratio · R`, lies in the cell: by `Kakeya.VeryNotSticky.norm_sq_aniLin` the normalised
norm squared is `R⁻²(‖v‖² − ⟪ν,v⟫²) + (ratio R)⁻² ⟪ν,v⟫² ≤ 1/4 + 1/4 ≤ 1`.

Hypothesis (ii) is what `Kakeya.VeryNotSticky.abs_inner_sub_le_of_aligned` supplies for a body
whose normal is close to `ν` and whose offset is close to `t`: the source's "assign a plank to
the first slab whose normal is closest to its short John axis and whose **normal interval
contains it**" (l.1681-1682) is exactly this pair of conditions, and this lemma is the step
that turns them into the tree's containment clause. -/
theorem subset_generalSlab_of_normal_bound {X : Set E₃} (z ν : E₃) (hν : ‖ν‖ = 1)
    {R ratio t h : ℝ} (hR : 0 < R) (hratio : 0 < ratio) (hh : 0 ≤ h)
    (hball : X ⊆ Metric.closedBall z (R / 4)) (ht : |t| ≤ R / 4)
    (hnorm : ∀ x ∈ X, |⟪ν, x - (z + t • ν)⟫| ≤ h)
    (hsmall : 2 * h ≤ ratio * R) :
    X ⊆ (generalSlab (z + t • ν) ν hν hR hratio).carrier := by
  intro x hx
  rw [mem_generalSlab_iff]
  set c : E₃ := z + t • ν with hc
  set v : E₃ := x - c with hv
  have hrp : (0 : ℝ) < ratio * R := mul_pos hratio hR
  -- `‖v‖ ≤ R/2`
  have hvnorm : ‖v‖ ≤ R / 2 := by
    have h1 : ‖x - z‖ ≤ R / 4 := by
      have := hball hx
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    have h2 : ‖c - z‖ ≤ R / 4 := by
      rw [hc, show z + t • ν - z = t • ν by abel, norm_smul, hν, mul_one, Real.norm_eq_abs]
      exact ht
    calc ‖v‖ = ‖(x - z) - (c - z)‖ := by rw [hv]; congr 1; abel
      _ ≤ ‖x - z‖ + ‖c - z‖ := norm_sub_le _ _
      _ ≤ R / 4 + R / 4 := add_le_add h1 h2
      _ = R / 2 := by ring
  -- `|⟪ν, v⟫| ≤ h`
  have hinner : |(⟪ν, v⟫ : ℝ)| ≤ h := hnorm x hx
  -- the two summands of the normalised norm
  have hcs : (⟪ν, v⟫ : ℝ) ^ 2 ≤ ‖v‖ ^ 2 := inner_sq_le_norm_sq ν hν v
  have hsq := norm_sq_aniLin ν hν R⁻¹ (ratio * R)⁻¹ v
  have hRne : (R : ℝ) ≠ 0 := hR.ne'
  have hrpne : (ratio * R : ℝ) ≠ 0 := hrp.ne'
  have hi2 : (⟪ν, v⟫ : ℝ) ^ 2 ≤ h ^ 2 := by
    have := abs_nonneg (⟪ν, v⟫ : ℝ)
    nlinarith [sq_abs (⟪ν, v⟫ : ℝ), hinner, hh]
  have hA : (0 : ℝ) < R⁻¹ := inv_pos.mpr hR
  have hAu : R⁻¹ * ‖v‖ ≤ 1 / 2 := by
    calc R⁻¹ * ‖v‖ ≤ R⁻¹ * (R / 2) := mul_le_mul_of_nonneg_left hvnorm hA.le
      _ = 1 / 2 := by field_simp
  have hterm1 : (R⁻¹) ^ 2 * (‖v‖ ^ 2 - (⟪ν, v⟫ : ℝ) ^ 2) ≤ 1 / 4 := by
    have h0 : (0 : ℝ) ≤ R⁻¹ * ‖v‖ := mul_nonneg hA.le (norm_nonneg v)
    nlinarith [hAu, h0, mul_nonneg (sq_nonneg (R⁻¹)) (sq_nonneg (⟪ν, v⟫ : ℝ))]
  have hB : (0 : ℝ) < (ratio * R)⁻¹ := inv_pos.mpr hrp
  have hBw : (ratio * R)⁻¹ * |(⟪ν, v⟫ : ℝ)| ≤ 1 / 2 := by
    have h1 : (ratio * R)⁻¹ * |(⟪ν, v⟫ : ℝ)| ≤ (ratio * R)⁻¹ * h :=
      mul_le_mul_of_nonneg_left hinner hB.le
    have h2 : (ratio * R)⁻¹ * h ≤ (ratio * R)⁻¹ * ((ratio * R) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hB.le
    have h3 : (ratio * R)⁻¹ * ((ratio * R) / 2) = 1 / 2 := by field_simp
    linarith
  have hterm2 : ((ratio * R)⁻¹) ^ 2 * (⟪ν, v⟫ : ℝ) ^ 2 ≤ 1 / 4 := by
    have h0 : (0 : ℝ) ≤ (ratio * R)⁻¹ * |(⟪ν, v⟫ : ℝ)| := mul_nonneg hB.le (abs_nonneg _)
    nlinarith [hBw, h0, sq_abs (⟪ν, v⟫ : ℝ)]
  have hnorm2 : ‖aniLin ν R⁻¹ (ratio * R)⁻¹ v‖ ^ 2 ≤ 1 := by
    rw [hsq]; linarith
  nlinarith [norm_nonneg (aniLin ν R⁻¹ (ratio * R)⁻¹ v), hnorm2]

/-! ### The count of a two-level net inside a cone — the engine of clause (S4″) -/

/-- **`O(1)` slab labels at a point, counted.**

This is the source's count of l.1684-1688 — "at a shaded point, the typical-angle property
confines all relevant normals to one `O(θ)`-cap; separation of the normal net and of the
one-dimensional lattice therefore leaves only `O(1)` possible slab labels" — stated for the
abstract two-level net the lattice construction produces, and proved.

A label carries a **normal** `nrm i` and an **offset** `off i`, and the construction's
separation is exactly the hypothesis `hsep`: two distinct labels either sit on different net
normals, which are `ε`-separated, or on the *same* net normal, in which case their lattice
offsets are `σ`-separated. Restricting to the labels whose normal lies in the `α`-cone about
`v` and whose offset lies in an interval of length `ℓ` — which is what "the thickened cell
contains `x`" gives — the count is at most

`C_{lem:coneDirectionCount} (α/ε)² · (ℓ/σ + 1)`,

the product of the number of net cells in the cap (`Kakeya.NonSlab.card_le_coneDirectionCount`,
applied to the *image* of `nrm`, which is `ε`-separated) and the number of lattice translates
per normal (`card_le_of_pairwise_sep_of_mem_Icc`, applied fibrewise). Both factors are `δ`-free
once `ε ∝ a/b`, `σ ∝ (a/b) r₁` and `ℓ ∝ (a/b) r₁`, and the shape `(α/ε)²·(ℓ/σ + 1)` is exactly
the licensed clause (S4″)'s `slabConeCountConstant · (α/(a/b) + 1)²` after those
substitutions. -/
theorem card_le_cone_lattice {ι : Type*} (L : Finset ι) (nrm : ι → E₃) (off : ι → ℝ)
    {v : E₃} (hv : ‖v‖ = 1) {ε σ α ℓ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hℓ : 0 ≤ ℓ)
    (hεα : ε ≤ α)
    (hunit : ∀ i ∈ L, ‖nrm i‖ = 1)
    (hcone : ∀ i ∈ L, NonSlab.lineAngle (nrm i) v ≤ α)
    (hoff : ∀ i ∈ L, ∀ j ∈ L, nrm i = nrm j → |off i - off j| ≤ ℓ)
    (hsep : ∀ i ∈ L, ∀ j ∈ L, i ≠ j →
      ε ≤ NonSlab.lineAngle (nrm i) (nrm j) ∨ (nrm i = nrm j ∧ σ ≤ |off i - off j|)) :
    (L.card : ℝ) ≤
      (NonSlab.coneDirectionCountConstant : ℝ) * (α / ε) ^ 2 * (2 * ℓ / σ + 1) := by
  classical
  -- the fibration of `L` over the finitely many net normals it uses
  have hfib : L.card = ∑ b ∈ L.image nrm, (L.filter fun i => nrm i = b).card :=
    Finset.card_eq_sum_card_image nrm L
  -- (1) the net normals are `ε`-separated and sit in the `α`-cone: the packing bound applies
  have hDsep : ((L.image nrm : Finset E₃) : Set E₃).Pairwise
      fun w w' => ε ≤ NonSlab.lineAngle w w' := by
    intro w hw w' hw' hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw')
    rcases hsep i hi j hj (fun h => hne (by rw [h])) with h | h
    · exact h
    · exact absurd h.1 hne
  have hDcard : ((L.image nrm).card : ℝ) ≤
      (NonSlab.coneDirectionCountConstant : ℝ) * (α / ε) ^ 2 := by
    refine NonSlab.card_le_coneDirectionCount hε hεα hv (L.image nrm) ?_ ?_ hDsep
    · intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact hunit i hi
    · intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact hcone i hi
  -- (2) each fibre is a `σ`-separated set of offsets inside an interval of length `ℓ`
  have hfibre : ∀ b ∈ L.image nrm,
      (((L.filter fun i => nrm i = b).card : ℕ) : ℝ) ≤ 2 * ℓ / σ + 1 := by
    intro b hb
    obtain ⟨i₀, hi₀, hb₀⟩ := Finset.mem_image.mp hb
    have hbnorm : ‖b‖ = 1 := by rw [← hb₀]; exact hunit i₀ hi₀
    have hb0 : b ≠ 0 := by
      intro h; rw [h, norm_zero] at hbnorm; norm_num at hbnorm
    set Fb := L.filter fun i => nrm i = b with hFb
    -- on the fibre, distinct labels have `σ`-separated offsets, hence distinct offsets
    have hoffsep : ∀ i ∈ Fb, ∀ j ∈ Fb, i ≠ j → σ ≤ |off i - off j| := by
      intro i hi j hj hij
      have hiL : i ∈ L := (Finset.mem_filter.mp hi).1
      have hjL : j ∈ L := (Finset.mem_filter.mp hj).1
      have hib : nrm i = b := (Finset.mem_filter.mp hi).2
      have hjb : nrm j = b := (Finset.mem_filter.mp hj).2
      rcases hsep i hiL j hjL hij with h | h
      · rw [hib, hjb, NonSlab.lineAngle_self hb0] at h
        linarith
      · exact h.2
    have hinj : ∀ i ∈ Fb, ∀ j ∈ Fb, off i = off j → i = j := by
      intro i hi j hj hoffeq
      by_contra hij
      have := hoffsep i hi j hj hij
      rw [hoffeq, sub_self, abs_zero] at this
      linarith
    have hcardeq : (Fb.image off).card = Fb.card :=
      Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h)
    have hTsep : ((Fb.image off : Finset ℝ) : Set ℝ).Pairwise fun s t => σ ≤ |s - t| := by
      intro s hs t ht hne
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht)
      exact hoffsep i hi j hj (fun h => hne (by rw [h]))
    have hi₀Fb : i₀ ∈ Fb := by
      rw [hFb, Finset.mem_filter]
      exact ⟨hi₀, hb₀⟩
    have hTmem : ∀ t ∈ Fb.image off, t ∈ Set.Icc (off i₀ - ℓ) ((off i₀ - ℓ) + 2 * ℓ) := by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      have hiL : i ∈ L := (Finset.mem_filter.mp hi).1
      have hib : nrm i = b := (Finset.mem_filter.mp hi).2
      have hsame : nrm i = nrm i₀ := by rw [hib, hb₀]
      have hdiff : |off i - off i₀| ≤ ℓ := hoff i hiL i₀ hi₀ hsame
      rw [abs_le] at hdiff
      constructor <;> [linarith [hdiff.1]; linarith [hdiff.2]]
    have := card_le_of_pairwise_sep_of_mem_Icc hσ (by linarith : (0:ℝ) ≤ 2 * ℓ) hTsep hTmem
    rwa [hcardeq] at this
  -- (3) put the two factors together
  have hsum : (L.card : ℝ) ≤ ((L.image nrm).card : ℝ) * (2 * ℓ / σ + 1) := by
    rw [hfib]
    push_cast
    calc (∑ b ∈ L.image nrm, ((L.filter fun i => nrm i = b).card : ℝ))
        ≤ ∑ _b ∈ L.image nrm, (2 * ℓ / σ + 1) := Finset.sum_le_sum hfibre
      _ = ((L.image nrm).card : ℝ) * (2 * ℓ / σ + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) ≤ 2 * ℓ / σ + 1 := by positivity
  calc (L.card : ℝ) ≤ ((L.image nrm).card : ℝ) * (2 * ℓ / σ + 1) := hsum
    _ ≤ ((NonSlab.coneDirectionCountConstant : ℝ) * (α / ε) ^ 2) * (2 * ℓ / σ + 1) :=
      mul_le_mul_of_nonneg_right hDcard hpos

/-! ### R7 dissolved: clause (A2′) from clause (A2), with no alignment of the thickened body -/

/-- **The image of a thickening lies in the thickening of the image**, at the map's operator
norm `max α β` (`Kakeya.VeryNotSticky.norm_aniLin_le_max`). For a *compact* `X` the thickening
is the union of the closed balls about its points (`IsCompact.cthickening_eq_biUnion_closedBall`),
and the affine map moves each ball into a ball of `max α β` times the radius. -/
theorem aniRescale_image_cthickening_subset (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) {X : Set E₃} (hX : IsCompact X) {r : ℝ} (hr : 0 ≤ r) :
    aniRescale c n hn hα.ne' hβ.ne' '' Metric.cthickening r X ⊆
      Metric.cthickening (max α β * r) (aniRescale c n hn hα.ne' hβ.ne' '' X) := by
  have hM : (0 : ℝ) ≤ max α β := le_max_of_le_left hα.le
  rintro _ ⟨x, hx, rfl⟩
  rw [hX.cthickening_eq_biUnion_closedBall hr] at hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  have hdist : dist (aniRescale c n hn hα.ne' hβ.ne' x) (aniRescale c n hn hα.ne' hβ.ne' w)
      ≤ max α β * r := by
    rw [aniRescale_dist]
    calc ‖aniLin n α β (x - w)‖ ≤ max α β * ‖x - w‖ :=
          norm_aniLin_le_max n hn hα.le hβ.le (x - w)
      _ ≤ max α β * r := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          rw [← dist_eq_norm]
          exact Metric.mem_closedBall.mp hxw
  refine Metric.mem_cthickening_of_dist_le _ _ (max α β * r)
    (aniRescale c n hn hα.ne' hβ.ne' '' X) ⟨w, hw, rfl⟩ hdist

/-- **Clause (A2′) is a consequence of clause (A2) — the R7 obligation dissolves.**

The existing (A2′) producer `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_cthickening_of_aligned`
carries the alignment of the **thickened** body's own normal as a hypothesis, and that hypothesis
— "R7", `∠(n(N_r W), n(W)) ≲ r/τ₁(W)` — was the last piece of geometry the tangential package
owed. It is **not needed**: (A2′) follows from (A2) by two facts about thickenings and nothing
about normals at all.

* *Lower halves*: `X ⊆ N_r(X)`, so the images nest and `Metric.thickness` is monotone
  (`Kakeya.Metric.thickness_monotone`); the lower bound at `Cmp` is therefore inherited at the
  weaker constant `2 Cmp`.
* *Upper halves*: `L(N_r(X)) ⊆ N_{Mr}(L(X))` with `M = max α β`
  (`aniRescale_image_cthickening_subset`), and thickening a set by `s` raises each thickness by
  at most `s` (`Kakeya.Metric.thickness_cthickening_le`). So
  `τ_k(L(N_r X)) ≤ τ_k(L X) + M r ≤ Cmp t_k + M r`, and the hypothesis `hslack : M r ≤ Cmp t_k`
  closes it at `2 Cmp t_k`.

At the tangential instance `M r = (b/(a r₁)) · τ₂(W) ≤ (b/(a r₁)) · C₀ a = C₀ (b/r₁) = C₀ ρ₂`,
while `Cmp t_k` is `Cmp` at `k = 0` and `Cmp ρ₂` at `k = 1, 2`, so `hslack` is exactly
`C₀ ≤ Cmp` together with `ρ₂ ≤ 1` — both available (`le_alignedRescaleConstant`). **The factor
`2` of the existing clause (A2′) is thereby explained**: it is the one thickening step, not a
second alignment loss. -/
theorem hasThicknesses_aniRescale_cthickening_of_image (c n : E₃) (hn : ‖n‖ = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) {X : Set E₃} (hX : IsCompact X) (hXne : X.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) {Cmp : NNReal} (hCmp : 1 ≤ Cmp) {m : ℕ} {t : Fin m → ℝ}
    (ht : ∀ k, 0 ≤ t k)
    (hprof : Kakeya.HasThicknesses (aniRescale c n hn hα.ne' hβ.ne' '' X) Cmp t)
    (hslack : ∀ k, max α β * r ≤ (Cmp : ℝ) * t k) :
    Kakeya.HasThicknesses
      (aniRescale c n hn hα.ne' hβ.ne' '' Metric.cthickening r X) (2 * Cmp) t := by
  have hCmpR : (1 : ℝ) ≤ (Cmp : ℝ) := by exact_mod_cast hCmp
  have hCmppos : (0 : ℝ) < (Cmp : ℝ) := by linarith
  have hM : (0 : ℝ) ≤ max α β := le_max_of_le_left hα.le
  have h2Cmp : ((2 * Cmp : NNReal) : ℝ) = 2 * (Cmp : ℝ) := by push_cast; ring
  -- the image of `X` sits inside the image of the thickening
  have hsub : aniRescale c n hn hα.ne' hβ.ne' '' X ⊆
      aniRescale c n hn hα.ne' hβ.ne' '' Metric.cthickening r X :=
    Set.image_mono (Metric.self_subset_cthickening _)
  -- and the image of the thickening inside a thickening of the image
  have hsub2 := aniRescale_image_cthickening_subset c n hn hα hβ hX hr
  have hcont : Continuous (aniRescale c n hn hα.ne' hβ.ne') :=
    AffineEquiv.continuous_of_finiteDimensional (aniRescale c n hn hα.ne' hβ.ne')
  have hXimg : IsCompact (aniRescale c n hn hα.ne' hβ.ne' '' X) := hX.image hcont
  have hcthimg : IsCompact (aniRescale c n hn hα.ne' hβ.ne' '' Metric.cthickening r X) :=
    (hX.cthickening (r := r)).image hcont
  have hcthbdd : Bornology.IsBounded
      (Metric.cthickening (max α β * r) (aniRescale c n hn hα.ne' hβ.ne' '' X)) :=
    hXimg.isBounded.cthickening
  have hgrow := Metric.thickness_cthickening_le hXimg.isBounded
    (hXne.image _) (mul_nonneg hM hr)
  intro k
  refine ⟨?_, ?_⟩
  · -- lower: inherited from `hprof` at the weaker constant
    have hmono : Metric.thickness ℝ (aniRescale c n hn hα.ne' hβ.ne' '' X) (k : ℕ) ≤
        Metric.thickness ℝ (aniRescale c n hn hα.ne' hβ.ne' '' Metric.cthickening r X) (k : ℕ) :=
      Metric.thickness_monotone (𝕜 := ℝ) hcthimg.isBounded hsub (k : ℕ)
    have hlow := (hprof k).1
    have hinv : ((2 * Cmp : NNReal) : ℝ)⁻¹ * t k ≤ ((Cmp : NNReal) : ℝ)⁻¹ * t k := by
      rw [h2Cmp]
      refine mul_le_mul_of_nonneg_right ?_ (ht k)
      rw [inv_le_inv₀ (by linarith) hCmppos]
      linarith
    linarith [hinv, hlow, hmono]
  · -- upper: one thickening step, paid by `hslack`
    have hmono2 : Metric.thickness ℝ
        (aniRescale c n hn hα.ne' hβ.ne' '' Metric.cthickening r X) (k : ℕ) ≤
        Metric.thickness ℝ
          (Metric.cthickening (max α β * r) (aniRescale c n hn hα.ne' hβ.ne' '' X)) (k : ℕ) :=
      Metric.thickness_monotone (𝕜 := ℝ) hcthbdd hsub2 (k : ℕ)
    have hup := (hprof k).2
    have hgrowk := hgrow (k : ℕ)
    have hsl := hslack k
    rw [h2Cmp]
    linarith [hmono2, hgrowk, hup, hsl]

/-! ### The cell's two shape constants -/

/-- **The tangential semi-axis of a lattice cell**, `4 r₁`. The source's cells have "two fixed
tangential widths large enough to contain `B₁`"
(`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1680); `4 r₁` is the least round value at
which a body of `B̄(ctr B, r₁)` still lies in its cell after a lattice offset of up to `r₁`
(`subset_generalSlab_of_normal_bound` needs `‖x − c‖ ≤ R/2`, and the offset alone costs `r₁`). -/
noncomputable def latticeCellRadius (cfg : VeryNotSticky.{u}) : ℝ := 4 * (cfg.r₁ : ℝ)

/-- **The aspect of a lattice cell**, `(a/b)/4`, chosen so that the normal half-width
`ratio · R` is exactly `(a/b) r₁` — the width clause (S2) asks for. -/
noncomputable def latticeCellRatio (cfg : VeryNotSticky.{u}) : ℝ :=
  ((cfg.a / cfg.b : NNReal) : ℝ) / 2

theorem latticeCellRadius_pos (cfg : VeryNotSticky.{u}) : 0 < latticeCellRadius cfg := by
  have := r₁_pos cfg
  rw [latticeCellRadius]; linarith

theorem latticeCellRatio_pos (cfg : VeryNotSticky.{u}) : 0 < latticeCellRatio cfg := by
  have := cfg_ratio_pos cfg
  rw [latticeCellRatio]; linarith

theorem latticeCellRatio_le_one (cfg : VeryNotSticky.{u}) : latticeCellRatio cfg ≤ 1 := by
  have := cfg_ratio_le_one cfg
  rw [latticeCellRatio]; linarith

/-- The cell's normal half-width is `2 (a/b) r₁` — **twice** the width clause (S2) asks for,
which is the source's own `C θ` against the lattice spacing `c θ` with `C > c` (l.1677-1680):
the cover is boundedly overlapping, not a tiling, and the slack is what carries the *thickened*
body of clause (A1′) inside the cell. -/
theorem latticeCell_width (cfg : VeryNotSticky.{u}) :
    latticeCellRatio cfg * latticeCellRadius cfg
      = 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)) := by
  rw [latticeCellRatio, latticeCellRadius]; ring

/-- The cell's tangential profile, as `hasThicknesses_of_four_R` reads it. -/
theorem latticeCell_hasThicknesses (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (hC₀4 : (4 : NNReal) ≤ bd.C₀) (c n : E₃) (hn : ‖n‖ = 1) :
    Kakeya.HasThicknesses
      (generalSlab c n hn (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg)).carrier bd.C₀
      ![(cfg.r₁ : ℝ), (cfg.r₁ : ℝ), ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)] := by
  have hbase := hasThicknesses_generalSlab c n hn (latticeCellRadius_pos cfg)
    (latticeCellRatio_pos cfg) (latticeCellRatio_le_one cfg) (C := 1) le_rfl
  rw [latticeCell_width] at hbase
  have hq0 : (0 : ℝ) ≤ ((cfg.a / cfg.b : NNReal) : ℝ) := NNReal.coe_nonneg _
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := NNReal.coe_nonneg _
  have hq0' : (0 : ℝ) ≤ (cfg.a : ℝ) / (cfg.b : ℝ) := by positivity
  have hqr : (0 : ℝ) ≤ (cfg.a : ℝ) / (cfg.b : ℝ) * (cfg.r₁ : ℝ) := by positivity
  have hqr0 : (0 : ℝ) ≤ ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ) := by positivity
  refine hasThicknesses_shrink_four hC₀4 ?_ ?_ ?_ hbase
  · intro k
    fin_cases k
    · exact hr0
    · exact hr0
    · exact hqr0
  · intro k
    fin_cases k
    all_goals simp [latticeCellRadius]
    all_goals nlinarith [hq0, hr0, hq0', hqr]
  · intro k
    fin_cases k
    all_goals simp [latticeCellRadius]
    all_goals nlinarith [hq0, hr0, hq0', hqr]

/-- The cone-count constant of clause (S4″) dominates what the lattice construction produces:
`coneDirectionCountConstant · (32 C₀)² · 33`, the product of the net factor (mesh
`(a/b)/(32 C₀)`) and the lattice factor (`⌈·⌉ + 1 ≤ 33`). -/
theorem latticeCount_le_slabConeCountConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    (NonSlab.coneDirectionCountConstant : ℝ) * (64 * (C₀ : ℝ)) ^ 2 * 49
      ≤ (slabConeCountConstant C₀ : ℝ) := by
  have hC₀R : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀0 : (0 : ℝ) < (C₀ : ℝ) := by linarith
  have hsep : (slabAxisSeparationConstant C₀ : ℝ) = ((2 : ℝ) ^ 10 * (C₀ : ℝ) ^ 4)⁻¹ := by
    rw [slabAxisSeparationConstant]
    push_cast
    ring
  have hcdc : (NonSlab.coneDirectionCountConstant : ℝ) = 2 ^ 10 := by
    rw [NonSlab.coneDirectionCountConstant]; push_cast; ring
  have hscc : (slabConeCountConstant C₀ : ℝ) =
      (NonSlab.coneDirectionCountConstant : ℝ) * (3 / (slabAxisSeparationConstant C₀ : ℝ)) ^ 2 := by
    rw [slabConeCountConstant]; push_cast; ring
  rw [hscc, hsep, hcdc]
  have hpow : ((3 : ℝ) / ((2 : ℝ) ^ 10 * (C₀ : ℝ) ^ 4)⁻¹) = 3 * (2 ^ 10 * (C₀ : ℝ) ^ 4) := by
    rw [div_inv_eq_mul]
  rw [hpow]
  have h8 : (C₀ : ℝ) ^ 2 ≤ (C₀ : ℝ) ^ 8 := by
    exact pow_le_pow_right₀ hC₀R (by norm_num)
  nlinarith [h8, hC₀0, sq_nonneg ((C₀ : ℝ))]

/-! ### The lattice slab family, assembled -/

set_option maxHeartbeats 2000000 in
-- The construction carries two greedy nets, a choice function for each, and six clause proofs
-- in one term; the `S4″` fibration alone exhausts the default budget.
/-- **`hfam` — the tangential slab family at a general `(a, b)`, constructed.**

This is the producer  specified and did not build, and it is the refined
source's own construction (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1677-1688,
boundary-safe form l.5026-5066) with the two nets taken *inside the finite set of occurring
labels* rather than over the sphere and the line:

* a `κ(a/b)`-net of normals at mesh `ε = (a/b)/(32 C₀)`, produced by
  `Kakeya.VeryNotSticky.exists_maximal_pairwise_not` on the finite set
  `{n(W_j) : j ∈ 𝕎''_B}` — separated by construction, and dense **where a body sits**, which is
  all the assignment needs;
* for each net normal, a lattice of offsets at spacing `σ = (a/b) r₁/4` in the coordinate
  `⟨x, ν⟩` only, by the same lemma;
* the cell of a label `m` is the ellipsoid
  `generalSlab (ctr B + ⟨ν, w_m − ctr B⟩ ν) ν _ (4 r₁) ((a/b)/4)`, of tangential semi-axis
  `4 r₁` — "two fixed tangential widths large enough to contain `B₁`" (l.1680) — and normal
  half-width exactly `(a/b) r₁`;
* `slabOf j` is the cell of the label the two nets assign to `j`: "the first slab whose normal
  is closest to its short John axis and whose normal interval contains it" (l.1681-1682).

All six clauses hold **by construction**: (S2)-profile by
`latticeCell_hasThicknesses` (the `4 ≤ bd.C₀` side condition, located there), (S2)-ball by the
cell's own centre, (S3)-containment by `subset_generalSlab_of_normal_bound` fed by the
tilted-width estimate `abs_inner_sub_le_of_aligned` (the `16 C₀ b ≤ r₁` side condition, a
`∀ᶠ δ` threshold on the tangential path, enters exactly here), (S3)-angle and (S3′) by the net
mesh plus `lineAngle_bodyNormal_generalSlab_le`, and **(S4″) by `card_le_cone_lattice`** — the
source's `O(1)`-slab-labels count, at the `δ`-free `slabConeCountConstant`.

The two extra data returned, `nrmOf` and `ctrOf` with the shape equation, are what the (A1) and
(A2) producers of `MainLemma2/TangentialSlabAlign.lean` consume; see
`exists_slabPackageData_lattice`. -/
theorem exists_isSlabFamily_lattice (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ')
    (hC₀4 : (4 : NNReal) ≤ bd.C₀)
    (hbr₁ : 32 * (bd.C₀ : ℝ) * (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ))
    (hmargin : ∀ j ∈ bd.bodies B,
      Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
        Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) :
    ∃ (nrmOf ctrOf : ConvexSpaceBody E₃ → E₃) (𝕊 : Set (ConvexSpaceBody E₃))
      (slabOf : bd.ω → ConvexSpaceBody E₃),
      IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf ∧
      (∀ S, ‖nrmOf S‖ = 1) ∧
      (∀ S ∈ 𝕊, ∀ hn : ‖nrmOf S‖ = 1,
        S = generalSlab (ctrOf S) (nrmOf S) hn
          (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg)) ∧
      (∀ j ∈ ta.sel, Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
        (slabOf j).carrier) ∧
      ∀ j ∈ ta.sel, NonSlab.lineAngle (bodyNormal (bd.Wb j)) (nrmOf (slabOf j))
        ≤ 3 * ((cfg.a / cfg.b : NNReal) : ℝ) := by
  classical
  -- ## scales
  have hq0 : (0 : ℝ) < ((cfg.a / cfg.b : NNReal) : ℝ) := cfg_ratio_pos cfg
  have hq1 : ((cfg.a / cfg.b : NNReal) : ℝ) ≤ 1 := cfg_ratio_le_one cfg
  have hr0 : (0 : ℝ) < (cfg.r₁ : ℝ) := r₁_pos cfg
  have hC₀R : (4 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast hC₀4
  have hC₀0 : (0 : ℝ) < (bd.C₀ : ℝ) := by linarith
  have hb0 : (0 : ℝ) < (cfg.b : ℝ) := by
    have : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
    exact_mod_cast this
  have ha0 : (0 : ℝ) < (cfg.a : ℝ) := by
    have : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact_mod_cast this
  have hqb : ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.b : ℝ) = (cfg.a : ℝ) := cfg_ratio_mul_b cfg
  have hC₀b : (bd.C₀ : ℝ) * (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ) := by nlinarith [hbr₁, hb0, hC₀0]
  have hbr : (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ) := by nlinarith [hC₀b, hC₀R, hb0]
  set ε : ℝ := ((cfg.a / cfg.b : NNReal) : ℝ) / (32 * (bd.C₀ : ℝ)) with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hεq : ε * (32 * (bd.C₀ : ℝ)) = ((cfg.a / cfg.b : NNReal) : ℝ) := by
    rw [hεdef]; field_simp
  have hεsmall : ε * 128 ≤ ((cfg.a / cfg.b : NNReal) : ℝ) := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hq0, hC₀R]
  set σ : ℝ := ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ) / 4 with hσdef
  have hσ0 : 0 < σ := by rw [hσdef]; positivity
  -- ## per-body data
  set ν : bd.ω → E₃ := fun j => bodyNormal (bd.Wb j) with hνdef
  have hνu : ∀ j, ‖ν j‖ = 1 := fun j => norm_bodyNormal _
  have hνne : ∀ j, ν j ≠ 0 := fun j => bodyNormal_ne_zero _
  set w : bd.ω → E₃ := fun j => (bd.Wb j).nonempty'.choose with hwdef
  have hwm : ∀ j, w j ∈ (bd.Wb j).carrier := fun j => (bd.Wb j).nonempty'.choose_spec
  have hjB : ∀ j ∈ ta.sel, j ∈ bd.bodies B := fun j hj =>
    (tc.thinBall hB).bodies'_subset (ta.hsel hj)
  have hball : ∀ j ∈ ta.sel, (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ) :=
    fun j hj => bd.bodies_subset_ball B hB j (hjB j hj)
  have hprof : ∀ j ∈ ta.sel, Kakeya.HasThicknesses (bd.Wb j).carrier bd.C₀
      ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)] :=
    fun j hj => bd.bodies_thickness B hB j (hjB j hj)
  -- ## level 1: the net of normals
  obtain ⟨N, hNsub, hNpair, hNcov⟩ :=
    exists_maximal_pairwise_not ta.sel (fun a b => NonSlab.lineAngle (ν a) (ν b) ≤ ε)
      (fun a b h => by rwa [NonSlab.lineAngle_comm] at h)
      (fun a => by rw [NonSlab.lineAngle_self (hνne a)]; exact hε0.le)
  have hichoice : ∀ j : bd.ω, ∃ p : bd.ω,
      j ∈ ta.sel → p ∈ N ∧ NonSlab.lineAngle (ν j) (ν p) ≤ ε := by
    intro j
    by_cases hj : j ∈ ta.sel
    · obtain ⟨p, hp, hple⟩ := hNcov j hj
      exact ⟨p, fun _ => ⟨hp, hple⟩⟩
    · exact ⟨j, fun h => absurd h hj⟩
  choose iOf hiOf using hichoice
  -- ## level 2: the lattice of offsets, per net normal
  have hlvl2 : ∀ i : bd.ω, ∃ P : Finset bd.ω,
      P ⊆ ta.sel.filter (fun j => iOf j = i) ∧
      (↑P : Set bd.ω).Pairwise (fun a b => ¬ |(⟪ν i, w a - w b⟫ : ℝ)| ≤ σ) ∧
      ∀ j ∈ ta.sel.filter (fun j => iOf j = i), ∃ p ∈ P, |(⟪ν i, w j - w p⟫ : ℝ)| ≤ σ := by
    intro i
    refine exists_maximal_pairwise_not _ (fun a b => |(⟪ν i, w a - w b⟫ : ℝ)| ≤ σ) ?_ ?_
    · intro a b h
      rwa [show w b - w a = -(w a - w b) by abel, inner_neg_right, abs_neg]
    · intro a
      simp only [sub_self, inner_zero_right, abs_zero]
      exact hσ0.le
  choose O hOsub hOpair hOcov using hlvl2
  have hmchoice : ∀ j : bd.ω, ∃ m : bd.ω,
      j ∈ ta.sel → m ∈ O (iOf j) ∧ |(⟪ν (iOf j), w j - w m⟫ : ℝ)| ≤ σ := by
    intro j
    by_cases hj : j ∈ ta.sel
    · have hjJ : j ∈ ta.sel.filter (fun k => iOf k = iOf j) := Finset.mem_filter.mpr ⟨hj, rfl⟩
      obtain ⟨p, hp, hple⟩ := hOcov (iOf j) j hjJ
      exact ⟨p, fun _ => ⟨hp, hple⟩⟩
    · exact ⟨j, fun h => absurd h hj⟩
  choose mOf hmOf using hmchoice
  -- ## the labels and the cells
  set Lab : Finset bd.ω := N.biUnion O with hLabdef
  have hLab_spec : ∀ m ∈ Lab, iOf m ∈ N ∧ m ∈ O (iOf m) ∧ m ∈ ta.sel := by
    intro m hm
    obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp hm
    have hie : iOf m = i := (Finset.mem_filter.mp (hOsub i hmi)).2
    have hmsel : m ∈ ta.sel := (Finset.mem_filter.mp (hOsub i hmi)).1
    refine ⟨?_, ?_, hmsel⟩
    · rw [hie]; exact hi
    · rw [hie]; exact hmi
  set off : bd.ω → ℝ := fun m => (⟪ν (iOf m), w m - bd.ctr B⟫ : ℝ) with hoffdef
  set ctrC : bd.ω → E₃ := fun m => bd.ctr B + off m • ν (iOf m) with hctrCdef
  set cell : bd.ω → ConvexSpaceBody E₃ := fun m =>
    generalSlab (ctrC m) (ν (iOf m)) (hνu (iOf m)) (latticeCellRadius_pos cfg)
      (latticeCellRatio_pos cfg) with hcelldef
  -- the offset of a label is within `r₁` of the ball's centre
  have hoffle : ∀ m ∈ ta.sel, |off m| ≤ (cfg.r₁ : ℝ) := by
    intro m hm
    have hwB : w m ∈ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ) := hball m hm (hwm m)
    have hnorm : ‖w m - bd.ctr B‖ ≤ (cfg.r₁ : ℝ) := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hwB
    calc |off m| ≤ ‖ν (iOf m)‖ * ‖w m - bd.ctr B‖ := abs_real_inner_le_norm _ _
      _ = ‖w m - bd.ctr B‖ := by rw [hνu, one_mul]
      _ ≤ (cfg.r₁ : ℝ) := hnorm
  -- ## the family
  set nrmOf : ConvexSpaceBody E₃ → E₃ := fun S =>
    if h : ∃ m, m ∈ Lab ∧ cell m = S then ν (iOf h.choose) else bodyNormal S with hnrmOfdef
  set ctrOf : ConvexSpaceBody E₃ → E₃ := fun S =>
    if h : ∃ m, m ∈ Lab ∧ cell m = S then ctrC h.choose else 0 with hctrOfdef
  have hnrmu : ∀ S, ‖nrmOf S‖ = 1 := by
    intro S
    by_cases h : ∃ m, m ∈ Lab ∧ cell m = S
    · rw [hnrmOfdef]; simp only [dif_pos h]; exact hνu _
    · rw [hnrmOfdef]; simp only [dif_neg h]; exact norm_bodyNormal S
  have hshape : ∀ S ∈ (↑(Lab.image cell) : Set (ConvexSpaceBody E₃)),
      ∀ hn : ‖nrmOf S‖ = 1,
      S = generalSlab (ctrOf S) (nrmOf S) hn
        (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) := by
    intro S hS hn
    obtain ⟨m, hm, hmS⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS)
    have hex : ∃ m, m ∈ Lab ∧ cell m = S := ⟨m, hm, hmS⟩
    have hc := hex.choose_spec
    have hnS : nrmOf S = ν (iOf hex.choose) := by
      rw [hnrmOfdef]; simp only [dif_pos hex]
    have hcS : ctrOf S = ctrC hex.choose := by
      rw [hctrOfdef]; simp only [dif_pos hex]
    have key : ∀ (m : bd.ω) (c n : E₃) (hn' : ‖n‖ = 1), c = ctrC m → n = ν (iOf m) →
        cell m = generalSlab c n hn'
          (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) := by
      intro m c n hn' hc' hn''
      subst hc'
      subst hn''
      rw [hcelldef]
    calc S = cell hex.choose := hc.2.symm
      _ = generalSlab (ctrOf S) (nrmOf S) hn
            (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) :=
        key hex.choose (ctrOf S) (nrmOf S) hn hcS hnS
  -- ## the assignment's two facts
  have hmOfLab : ∀ j ∈ ta.sel, mOf j ∈ Lab ∧ iOf (mOf j) = iOf j := by
    intro j hj
    have h1 := (hmOf j hj).1
    have h2 : mOf j ∈ ta.sel.filter (fun k => iOf k = iOf j) := hOsub (iOf j) h1
    exact ⟨Finset.mem_biUnion.mpr ⟨iOf j, (hiOf j hj).1, h1⟩, (Finset.mem_filter.mp h2).2⟩
  -- ## the cell's shape, in a form free of dependent rewriting
  have hcellshape : ∀ (m : bd.ω) (c n : E₃) (hn : ‖n‖ = 1), c = ctrC m → n = ν (iOf m) →
      cell m = generalSlab c n hn (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) := by
    intro m c n hn hc' hn''
    subst hc'
    subst hn''
    rw [hcelldef]
  -- ## the cell's own normal is within `2 · ratio` of its net normal
  have hcellnrm : ∀ m : bd.ω, NonSlab.lineAngle (bodyNormal (cell m)) (ν (iOf m))
      ≤ 2 * latticeCellRatio cfg := by
    intro m
    rw [hcelldef]
    exact lineAngle_bodyNormal_generalSlab_le (ctrC m) (ν (iOf m)) (hνu (iOf m))
      (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) (latticeCellRatio_le_one cfg)
  -- ## the body-to-cell angle
  have hratio2 : 2 * latticeCellRatio cfg = ((cfg.a / cfg.b : NNReal) : ℝ) := by
    rw [latticeCellRatio]; ring
  have hangle : ∀ j ∈ ta.sel,
      axisAngle (bd.Wb j) (cell (mOf j)) ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ) := by
    intro j hj
    have h1 : NonSlab.lineAngle (ν j) (ν (iOf (mOf j))) ≤ ε := by
      rw [(hmOfLab j hj).2]; exact (hiOf j hj).2
    have h2 := hcellnrm (mOf j)
    rw [NonSlab.lineAngle_comm] at h2
    have h3 := NonSlab.lineAngle_le_add (ν j) (ν (iOf (mOf j))) (bodyNormal (cell (mOf j)))
    rw [axisAngle_eq_lineAngle]
    rw [hratio2] at h2
    have : NonSlab.lineAngle (bodyNormal (bd.Wb j)) (bodyNormal (cell (mOf j)))
        = NonSlab.lineAngle (ν j) (bodyNormal (cell (mOf j))) := rfl
    rw [this]
    linarith [h1, h2, h3, hεsmall, hq0]
  -- the thin scale of a body is at most `C₀ a`
  have hscale : ∀ j ∈ ta.sel, (bd.Wb j).scale ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
    intro j hj
    have h2 := (bd.bodies_thickness B hB j (hjB j hj) 2).2
    simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    have hs : (bd.Wb j).scale = Metric.thickness ℝ (bd.Wb j).carrier 2 := by
      change Metric.thickness ℝ (bd.Wb j).carrier
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) = _
      rw [finrank_euclideanSpace_fin]
    rw [hs]
    exact h2
  -- the margin containment: the *thickened* body already sits in its cell
  have hcth : ∀ j ∈ ta.sel, Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
      (cell (mOf j)).carrier := by
    intro j hj
    have hmsel : mOf j ∈ ta.sel := (hLab_spec _ (hmOfLab j hj).1).2.2
    have hcelleq : cell (mOf j)
        = generalSlab (bd.ctr B + off (mOf j) • ν (iOf j)) (ν (iOf j)) (hνu (iOf j))
            (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) := by
      refine hcellshape (mOf j) _ _ (hνu (iOf j)) ?_ ?_
      · rw [hctrCdef]; simp only; rw [(hmOfLab j hj).2]
      · rw [(hmOfLab j hj).2]
    rw [hcelleq]
    refine subset_generalSlab_of_normal_bound (bd.ctr B) (ν (iOf j)) (hνu (iOf j))
      (h := 2 * (ε * ((bd.C₀ : ℝ) * (cfg.r₁ : ℝ) + (bd.C₀ : ℝ) * (cfg.b : ℝ))
        + (bd.C₀ : ℝ) * (cfg.a : ℝ)) + σ + (bd.C₀ : ℝ) * (cfg.a : ℝ))
      (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) ?_ ?_ ?_ ?_ ?_
    · have := NNReal.coe_nonneg (bd.C₀)
      positivity
    · rw [show latticeCellRadius cfg / 4 = (cfg.r₁ : ℝ) by rw [latticeCellRadius]; ring]
      exact hmargin j (hjB j hj)
    · rw [show latticeCellRadius cfg / 4 = (cfg.r₁ : ℝ) by rw [latticeCellRadius]; ring]
      exact hoffle _ hmsel
    · intro x hx
      have hsc0 : (0 : ℝ) ≤ (bd.Wb j).scale := by
        have hsdef : (bd.Wb j).scale = Metric.thickness ℝ (bd.Wb j).carrier
            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) := rfl
        rw [hsdef]
        exact Metric.thickness_nonneg _ _
      rw [(bd.Wb j).isCompact'.cthickening_eq_biUnion_closedBall hsc0] at hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      have hd : ‖x - y‖ ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
        rw [← dist_eq_norm]
        exact le_trans (Metric.mem_closedBall.mp hxy) (hscale j hj)
      have hnn : (⟪ν (iOf j), ν (iOf j)⟫ : ℝ) = 1 := by
        rw [real_inner_self_eq_norm_sq, hνu]; norm_num
      have hoffm : off (mOf j) = (⟪ν (iOf j), w (mOf j) - bd.ctr B⟫ : ℝ) := by
        rw [hoffdef]; simp only; rw [(hmOfLab j hj).2]
      have hsplit : (⟪ν (iOf j), x - (bd.ctr B + off (mOf j) • ν (iOf j))⟫ : ℝ)
          = ⟪ν (iOf j), x - y⟫ + (⟪ν (iOf j), y - w j⟫ + ⟪ν (iOf j), w j - w (mOf j)⟫) := by
        simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hnn, mul_one,
          hoffm]
        ring
      have hbody : |(⟪ν (iOf j), y - w j⟫ : ℝ)|
          ≤ 2 * (ε * ((bd.C₀ : ℝ) * (cfg.r₁ : ℝ) + (bd.C₀ : ℝ) * (cfg.b : ℝ))
            + (bd.C₀ : ℝ) * (cfg.a : ℝ)) := by
        refine abs_inner_sub_le_of_aligned (bd.Wb j) (ν (iOf j)) (hνu (iOf j)) hε0.le
          ((hiOf j hj).2) ?_ ?_ ?_ hy (hwm j)
        · have := (hprof j hj 0).2; simpa using this
        · have := (hprof j hj 1).2; simpa using this
        · have := (hprof j hj 2).2; simpa using this
      have hoff2 : |(⟪ν (iOf j), w j - w (mOf j)⟫ : ℝ)| ≤ σ := (hmOf j hj).2
      have hxy' : |(⟪ν (iOf j), x - y⟫ : ℝ)| ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
        calc |(⟪ν (iOf j), x - y⟫ : ℝ)| ≤ ‖ν (iOf j)‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
          _ = ‖x - y‖ := by rw [hνu, one_mul]
          _ ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := hd
      rw [hsplit]
      calc |(⟪ν (iOf j), x - y⟫ : ℝ) + (⟪ν (iOf j), y - w j⟫ + ⟪ν (iOf j), w j - w (mOf j)⟫)|
          ≤ |(⟪ν (iOf j), x - y⟫ : ℝ)|
            + |(⟪ν (iOf j), y - w j⟫ : ℝ) + ⟪ν (iOf j), w j - w (mOf j)⟫| := abs_add_le _ _
        _ ≤ |(⟪ν (iOf j), x - y⟫ : ℝ)|
            + (|(⟪ν (iOf j), y - w j⟫ : ℝ)| + |(⟪ν (iOf j), w j - w (mOf j)⟫ : ℝ)|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ 2 * (ε * ((bd.C₀ : ℝ) * (cfg.r₁ : ℝ) + (bd.C₀ : ℝ) * (cfg.b : ℝ))
              + (bd.C₀ : ℝ) * (cfg.a : ℝ)) + σ + (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
              linarith [hxy', hbody, hoff2]
    · rw [latticeCell_width, hσdef]
      have hεr : ε * (32 * (bd.C₀ : ℝ)) = ((cfg.a / cfg.b : NNReal) : ℝ) := hεq
      nlinarith [hεr, hbr, hbr₁, hqb, hq0, hr0, hC₀0, hC₀R, hb0, ha0, hε0]
  -- the value of `nrmOf` on a cell
  have hnrmOfval : ∀ S ∈ (↑(Lab.image cell) : Set (ConvexSpaceBody E₃)),
      ∃ m, m ∈ Lab ∧ cell m = S ∧ nrmOf S = ν (iOf m) := by
    intro S hS
    obtain ⟨m0, hm0, hm0S⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS)
    have hex : ∃ m, m ∈ Lab ∧ cell m = S := ⟨m0, hm0, hm0S⟩
    refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
    rw [hnrmOfdef]; simp only [dif_pos hex]
  refine ⟨nrmOf, ctrOf, ↑(Lab.image cell), fun j => cell (mOf j), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    hnrmu, hshape, hcth, ?_⟩
  · -- finite
    exact (Lab.image cell).finite_toSet
  · -- (S2) profile
    intro S hS
    obtain ⟨m, _hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS)
    rw [hcelldef]
    exact latticeCell_hasThicknesses cfg hC₀4 (ctrC m) (ν (iOf m)) (hνu (iOf m))
  · -- (S2) the cell meets the ball, at its own centre
    intro S hS
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS)
    have hmsel : m ∈ ta.sel := (hLab_spec m hm).2.2
    refine ⟨ctrC m, ?_, ?_⟩
    · rw [hcelldef]
      have : ctrC m ∈ (generalSlab (ctrC m) (ν (iOf m)) (hνu (iOf m))
          (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg)).carrier := by
        rw [mem_generalSlab_iff]
        simp
      exact this
    · rw [Metric.mem_closedBall, dist_eq_norm, hctrCdef]
      simp only
      rw [show bd.ctr B + off m • ν (iOf m) - bd.ctr B = off m • ν (iOf m) by abel,
        norm_smul, hνu, mul_one, Real.norm_eq_abs]
      exact hoffle m hmsel
  · -- (S3)
    intro j hj
    refine ⟨?_, ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨mOf j, (hmOfLab j hj).1, rfl⟩)
    · -- containment
      exact (Metric.self_subset_cthickening _).trans (hcth j hj)
    · -- the angle, at `2 θ`
      have h := hangle j hj
      have hθ : ((cfg.a / cfg.b : NNReal) : ℝ) ≤ (ta.θ : ℝ) := by exact_mod_cast ta.hθab'
      have hθ0 : (0 : ℝ) ≤ (ta.θ : ℝ) := NNReal.coe_nonneg _
      linarith [h, hθ, hθ0]
  · -- (S3′)
    intro j hj
    have h := hangle j hj
    linarith [h, hq0]
  · -- (S4″), the cone-restricted count
    intro x v α hα
    have hqne : ((cfg.a / cfg.b : NNReal) : ℝ) ≠ 0 := hq0.ne'
    have hRHS0 : (0 : ℝ) ≤ (slabConeCountConstant bd.C₀ : ℝ) *
        (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (slabConeCountConstant bd.C₀ : ℝ) := NNReal.coe_nonneg _
      positivity
    set Lf : Finset bd.ω := Lab.filter (fun m =>
      x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) (cell m).carrier ∧
        NonSlab.lineAngle (bodyNormal (cell m)) v ≤ α) with hLfdef
    have hGsub : {S ∈ (↑(Lab.image cell) : Set (ConvexSpaceBody E₃)) |
        x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) v ≤ α} ⊆ ↑(Lf.image cell) := by
      rintro S ⟨hS𝕊, hxS, hvS⟩
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hS𝕊)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨m, Finset.mem_filter.mpr ⟨hm, hxS, hvS⟩, rfl⟩)
    have hcardG : (({S ∈ (↑(Lab.image cell) : Set (ConvexSpaceBody E₃)) |
        x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) v ≤ α}.ncard : ℕ) : ℝ) ≤ (Lf.card : ℝ) := by
      have h1 := Set.ncard_le_ncard hGsub (Lf.image cell).finite_toSet
      rw [Set.ncard_coe_finset] at h1
      have h2 : (Lf.image cell).card ≤ Lf.card := Finset.card_image_le
      exact_mod_cast h1.trans h2
    rcases Finset.eq_empty_or_nonempty Lf with hLfe | hLfne
    · rw [hLfe] at hcardG
      simp only [Finset.card_empty, Nat.cast_zero] at hcardG
      linarith [hcardG, hRHS0]
    obtain ⟨m₀, hm₀⟩ := hLfne
    -- the scale of a `lineAngle` argument is irrelevant
    have hsmul : ∀ (u y : E₃) (c : ℝ), 0 < c →
        NonSlab.lineAngle u (c • y) = NonSlab.lineAngle u y := by
      intro u y c hc
      rw [NonSlab.lineAngle, NonSlab.lineAngle,
        InnerProductGeometry.angle_smul_right_of_pos _ _ hc,
        show -(c • y) = c • (-y) by rw [smul_neg],
        InnerProductGeometry.angle_smul_right_of_pos _ _ hc]
    -- a unit axis for the cone
    obtain ⟨v', hv'u, hv'cone⟩ : ∃ v' : E₃, ‖v'‖ = 1 ∧
        ∀ m ∈ Lf, NonSlab.lineAngle (ν (iOf m)) v'
          ≤ max (α + 2 * latticeCellRatio cfg) ε := by
      have hpihalf : ∀ u y : E₃, NonSlab.lineAngle u y ≤ Real.pi / 2 := by
        intro u y
        rw [NonSlab.lineAngle, InnerProductGeometry.angle_neg_right]
        rcases le_total (InnerProductGeometry.angle u y) (Real.pi / 2) with h | h
        · exact le_trans (min_le_left _ _) h
        · exact le_trans (min_le_right _ _) (by linarith)
      rcases eq_or_ne v 0 with rfl | hv0
      · refine ⟨ν (iOf m₀), hνu _, ?_⟩
        intro m hm
        have hzero : NonSlab.lineAngle (bodyNormal (cell m)) (0 : E₃) = Real.pi / 2 := by
          rw [NonSlab.lineAngle]
          simp [InnerProductGeometry.angle_zero_right]
        have hαpi : Real.pi / 2 ≤ α := by
          have h := (Finset.mem_filter.mp hm).2.2
          rwa [hzero] at h
        have hr2 : (0 : ℝ) ≤ 2 * latticeCellRatio cfg := by
          have := latticeCellRatio_pos cfg; linarith
        calc NonSlab.lineAngle (ν (iOf m)) (ν (iOf m₀)) ≤ Real.pi / 2 := hpihalf _ _
          _ ≤ α + 2 * latticeCellRatio cfg := by linarith
          _ ≤ max (α + 2 * latticeCellRatio cfg) ε := le_max_left _ _
      · have hvn : (0 : ℝ) < ‖v‖⁻¹ := by
          have : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
          positivity
        refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm]
          field_simp
        · intro m hm
          rw [hsmul _ _ _ hvn]
          have h1 : NonSlab.lineAngle (ν (iOf m)) (bodyNormal (cell m))
              ≤ 2 * latticeCellRatio cfg := by
            rw [NonSlab.lineAngle_comm]; exact hcellnrm m
          have h2 := (Finset.mem_filter.mp hm).2.2
          have h3 := NonSlab.lineAngle_le_add (ν (iOf m)) (bodyNormal (cell m)) v
          calc NonSlab.lineAngle (ν (iOf m)) v ≤ 2 * latticeCellRatio cfg + α := by
                linarith [h1, h2, h3]
            _ = α + 2 * latticeCellRatio cfg := by ring
            _ ≤ max (α + 2 * latticeCellRatio cfg) ε := le_max_left _ _
    -- the offsets of two labels sharing a normal, both seeing `x`, are close
    have hxbound : ∀ m ∈ Lf, |(⟪ν (iOf m), x - bd.ctr B⟫ : ℝ) - off m|
        ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ)
          + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)) := by
      intro m hm
      have hxth : x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) (cell m).carrier :=
        (Finset.mem_filter.mp hm).2.1
      have hCa0 : (0 : ℝ) ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by positivity
      rw [(cell m).isCompact'.cthickening_eq_biUnion_closedBall hCa0] at hxth
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hxth
      have hd : ‖x - y‖ ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hxy
      have hy' : y ∈ (generalSlab (ctrC m) (ν (iOf m)) (hνu (iOf m))
          (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg)).carrier := by
        rw [hcelldef] at hy; exact hy
      have hyc : |(⟪ν (iOf m), y - ctrC m⟫ : ℝ)|
          ≤ latticeCellRatio cfg * latticeCellRadius cfg :=
        abs_inner_le_of_mem_generalSlab (ctrC m) (ν (iOf m)) (hνu (iOf m))
          (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) hy'
      rw [latticeCell_width] at hyc
      have hnn : (⟪ν (iOf m), ν (iOf m)⟫ : ℝ) = 1 := by
        rw [real_inner_self_eq_norm_sq, hνu]; norm_num
      have heq : (⟪ν (iOf m), x - bd.ctr B⟫ : ℝ) - off m
          = ⟪ν (iOf m), x - y⟫ + ⟪ν (iOf m), y - ctrC m⟫ := by
        rw [hctrCdef]
        simp only [inner_sub_right, inner_add_right, real_inner_smul_right, hnn, mul_one]
        ring
      have hxy' : |(⟪ν (iOf m), x - y⟫ : ℝ)| ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
        calc |(⟪ν (iOf m), x - y⟫ : ℝ)| ≤ ‖ν (iOf m)‖ * ‖x - y‖ :=
              abs_real_inner_le_norm _ _
          _ = ‖x - y‖ := by rw [hνu, one_mul]
          _ ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := hd
      rw [heq]
      calc |(⟪ν (iOf m), x - y⟫ : ℝ) + ⟪ν (iOf m), y - ctrC m⟫|
          ≤ |(⟪ν (iOf m), x - y⟫ : ℝ)| + |(⟪ν (iOf m), y - ctrC m⟫ : ℝ)| := abs_add_le _ _
        _ ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ)
            + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)) := add_le_add hxy' hyc
    -- the count
    have hcount := card_le_cone_lattice Lf (fun m => ν (iOf m)) off hv'u hε0 hσ0
      (ℓ := 2 * ((bd.C₀ : ℝ) * (cfg.a : ℝ)
        + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ))))
      (by positivity) (le_max_right _ _) (fun m _ => hνu _) hv'cone ?_ ?_
    rotate_left
    · -- the per-fibre offset diameter
      intro m hm m' hm' hnn'
      have h1 := hxbound m hm
      have h2 := hxbound m' hm'
      have hnn2 : ν (iOf m') = ν (iOf m) := hnn'.symm
      rw [hnn2] at h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> [linarith [h1.1, h1.2, h2.1, h2.2]; linarith [h1.1, h1.2, h2.1, h2.2]]
    · -- the separation of distinct labels
      intro m hm m' hm' hne
      have hmLab : m ∈ Lab := (Finset.mem_filter.mp hm).1
      have hm'Lab : m' ∈ Lab := (Finset.mem_filter.mp hm').1
      by_cases hi : iOf m = iOf m'
      · right
        refine ⟨by rw [hi], ?_⟩
        have hmO : m ∈ O (iOf m) := (hLab_spec m hmLab).2.1
        have hm'O : m' ∈ O (iOf m) := by
          have := (hLab_spec m' hm'Lab).2.1
          rwa [← hi] at this
        have hpair := hOpair (iOf m) (Finset.mem_coe.mpr hmO) (Finset.mem_coe.mpr hm'O) hne
        have hoffsub : off m - off m' = (⟪ν (iOf m), w m - w m'⟫ : ℝ) := by
          have e1 : off m = (⟪ν (iOf m), w m - bd.ctr B⟫ : ℝ) := by rw [hoffdef]
          have e2 : off m' = (⟪ν (iOf m), w m' - bd.ctr B⟫ : ℝ) := by
            rw [hoffdef]; simp only; rw [← hi]
          have e3 : (⟪ν (iOf m), w m - w m'⟫ : ℝ)
              = ⟪ν (iOf m), w m - bd.ctr B⟫ - ⟪ν (iOf m), w m' - bd.ctr B⟫ := by
            rw [← inner_sub_right]
            congr 1
            abel
          rw [e1, e2, e3]
        rw [hoffsub]
        exact le_of_not_ge hpair
      · left
        have hmN : iOf m ∈ N := (hLab_spec m hmLab).1
        have hm'N : iOf m' ∈ N := (hLab_spec m' hm'Lab).1
        have := hNpair (Finset.mem_coe.mpr hmN) (Finset.mem_coe.mpr hm'N) hi
        exact le_of_not_ge this
    -- the arithmetic
    have hAle : max (α + 2 * latticeCellRatio cfg) ε
        ≤ 2 * (α + ((cfg.a / cfg.b : NNReal) : ℝ)) := by
      refine max_le ?_ ?_
      · rw [hratio2]; linarith [hq0, hα]
      · linarith [hεsmall, hq0, hα]
    have hAeps : max (α + 2 * latticeCellRatio cfg) ε / ε
        ≤ 64 * (bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) := by
      rw [div_le_iff₀ hε0]
      have hid : 64 * (bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) * ε
          = 2 * (α + ((cfg.a / cfg.b : NNReal) : ℝ)) := by
        rw [hεdef]; field_simp; ring
      rw [hid]; exact hAle
    have hlat : 2 * (2 * ((bd.C₀ : ℝ) * (cfg.a : ℝ)
        + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)))) / σ + 1 ≤ 49 := by
      have hstep : 2 * (2 * ((bd.C₀ : ℝ) * (cfg.a : ℝ)
          + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)))) ≤ 48 * σ := by
        rw [hσdef]
        nlinarith [hC₀b, hqb, hq0, hr0, hC₀0, hb0]
      have := (div_le_iff₀ hσ0).mpr hstep
      linarith [this]
    have hfrac0 : (0 : ℝ) ≤ α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1 := by positivity
    have hcdc0 : (0 : ℝ) ≤ (NonSlab.coneDirectionCountConstant : ℝ) := NNReal.coe_nonneg _
    have h0 : (0 : ℝ) ≤ max (α + 2 * latticeCellRatio cfg) ε / ε := by positivity
    have hsq : (max (α + 2 * latticeCellRatio cfg) ε / ε) ^ 2
        ≤ (64 * (bd.C₀ : ℝ)) ^ 2 * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 := by
      have hmul : (0 : ℝ) ≤ 64 * (bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) := by
        positivity
      calc (max (α + 2 * latticeCellRatio cfg) ε / ε) ^ 2
          ≤ (64 * (bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1)) ^ 2 := by
            exact pow_le_pow_left₀ h0 hAeps 2
        _ = (64 * (bd.C₀ : ℝ)) ^ 2 * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 := by ring
    have hdom := latticeCount_le_slabConeCountConstant (C₀ := bd.C₀) (by linarith [hC₀R] :
      (1 : NNReal) ≤ bd.C₀)
    have hlat0 : (0 : ℝ) ≤ 2 * (2 * ((bd.C₀ : ℝ) * (cfg.a : ℝ)
        + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)))) / σ + 1 := by positivity
    have hcdcsq0 : (0 : ℝ) ≤ (NonSlab.coneDirectionCountConstant : ℝ) *
        ((64 * (bd.C₀ : ℝ)) ^ 2 * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2) := by
      positivity
    refine le_trans hcardG (le_trans hcount ?_)
    calc (NonSlab.coneDirectionCountConstant : ℝ)
          * (max (α + 2 * latticeCellRatio cfg) ε / ε) ^ 2
          * (2 * (2 * ((bd.C₀ : ℝ) * (cfg.a : ℝ)
              + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)))) / σ + 1)
        ≤ (NonSlab.coneDirectionCountConstant : ℝ)
          * ((64 * (bd.C₀ : ℝ)) ^ 2 * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2)
          * (2 * (2 * ((bd.C₀ : ℝ) * (cfg.a : ℝ)
              + 2 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)))) / σ + 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq hcdc0) hlat0
      _ ≤ (NonSlab.coneDirectionCountConstant : ℝ)
          * ((64 * (bd.C₀ : ℝ)) ^ 2 * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2) * 49 :=
          mul_le_mul_of_nonneg_left hlat hcdcsq0
      _ = ((NonSlab.coneDirectionCountConstant : ℝ) * (64 * (bd.C₀ : ℝ)) ^ 2 * 49)
          * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 := by ring
      _ ≤ (slabConeCountConstant bd.C₀ : ℝ)
          * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hdom (sq_nonneg _)
  · -- the alignment against the cell's defining normal
    intro j hj
    have hmem : cell (mOf j) ∈ (↑(Lab.image cell) : Set (ConvexSpaceBody E₃)) :=
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨mOf j, (hmOfLab j hj).1, rfl⟩)
    obtain ⟨m, _hmLab, hmc, hnv⟩ := hnrmOfval (cell (mOf j)) hmem
    rw [hnv]
    have h1 : NonSlab.lineAngle (ν j) (bodyNormal (cell m))
        ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ) := by
      rw [hmc]
      have := hangle j hj
      rwa [axisAngle_eq_lineAngle] at this
    have h2 := hcellnrm m
    have h3 := NonSlab.lineAngle_le_add (ν j) (bodyNormal (cell m)) (ν (iOf m))
    rw [hratio2] at h2
    have : NonSlab.lineAngle (bodyNormal (bd.Wb j)) (ν (iOf m))
        = NonSlab.lineAngle (ν j) (ν (iOf m)) := rfl
    rw [this]
    linarith [h1, h2, h3, hq0]

/-! ### Clauses (A2) and (A2′) for a lattice cell, at a parameter `κ` -/

/-- **Route R-c's three elementary facts**.

`Kakeya.VeryNotSticky.SlabPackage.L` is a **free field**: the producer chooses the
normalisation. Choosing the map that normalises the **doubled** cell rather than the cell puts
the cell itself inside `B̄(0, 1/2)`, and the half-ball of slack is exactly what carries the
bodies' `τ₂`-neighbourhoods — clause (A1′) — inside `B̄(0,1)`, **for every `Wd`**, with no clause
added to `Kakeya.VeryNotSticky.IsDenseSlab` and no numeral changed in any binder. -/
theorem aniLin_smul (n : E₃) (t α β : ℝ) (v : E₃) :
    aniLin n (t * α) (t * β) v = t • aniLin n α β v := by
  simp only [aniLin_apply, smul_add, smul_smul]
  rw [show t * β - t * α = t * (β - α) by ring, mul_assoc]

/-- The map of the **doubled** cell is the map of the cell, halved. -/
theorem aniLin_half (n : E₃) {R ratio : ℝ} (hR : 0 < R) (hratio : 0 < ratio) (v : E₃) :
    aniLin n (2 * R)⁻¹ (ratio * (2 * R))⁻¹ v
      = (2 : ℝ)⁻¹ • aniLin n R⁻¹ (ratio * R)⁻¹ v := by
  rw [show (2 * R)⁻¹ = (2 : ℝ)⁻¹ * R⁻¹ by field_simp,
    show (ratio * (2 * R))⁻¹ = (2 : ℝ)⁻¹ * (ratio * R)⁻¹ by field_simp]
  exact aniLin_smul n _ _ _ v

/-- **The margin.** `slabRescale` at the doubled radius carries the cell into `B̄(0, 1/2)`. -/
theorem image_generalSlab_subset_half (c ν : E₃) (hν : ‖ν‖ = 1) {R ratio : ℝ}
    (hR : 0 < R) (hratio : 0 < ratio) :
    slabRescale c ν hν (by linarith : (0 : ℝ) < 2 * R) hratio ''
        (generalSlab c ν hν hR hratio).carrier
      ⊆ Metric.closedBall (0 : E₃) (1 / 2) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_generalSlab_iff c ν hν hR hratio] at hx
  rw [Metric.mem_closedBall, dist_zero_right, slabRescale_apply, aniLin_half ν hR hratio,
    norm_smul]
  simp only [norm_inv, Real.norm_ofNat]
  calc (2 : ℝ)⁻¹ * ‖aniLin ν R⁻¹ (ratio * R)⁻¹ (x - c)‖ ≤ (2 : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
    _ = 1 / 2 := by norm_num

/-- The cell sits inside the doubled cell. -/
theorem generalSlab_subset_doubled (c ν : E₃) (hν : ‖ν‖ = 1) {R ratio : ℝ}
    (hR : 0 < R) (hratio : 0 < ratio) :
    (generalSlab c ν hν hR hratio).carrier
      ⊆ (generalSlab c ν hν (by linarith : (0 : ℝ) < 2 * R) hratio).carrier := by
  intro x hx
  rw [mem_generalSlab_iff c ν hν hR hratio] at hx
  rw [mem_generalSlab_iff, aniLin_half ν hR hratio, norm_smul]
  simp only [norm_inv, Real.norm_ofNat]
  calc (2 : ℝ)⁻¹ * ‖aniLin ν R⁻¹ (ratio * R)⁻¹ (x - c)‖ ≤ (2 : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
    _ ≤ 1 := by norm_num

/-- Thickening a ball enlarges its radius by the thickening parameter. -/
theorem cthickening_closedBall_subset (ρ s : ℝ) (hρ : 0 ≤ ρ) :
    Metric.cthickening ρ (Metric.closedBall (0 : E₃) s)
      ⊆ Metric.closedBall (0 : E₃) (s + ρ) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hsub := Metric.cthickening_subset_thickening' (δ₁ := ρ) (δ₂ := ρ + ε)
    (by linarith) (by linarith) (Metric.closedBall (0 : E₃) s)
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp (hsub hx)
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  have h1 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by simpa using norm_le_norm_add_norm_sub' x y
  have h2 : ‖x - y‖ < ρ + ε := by rwa [← dist_eq_norm]
  linarith

/-- **Clause (A1′) at radius `1`, for an ARBITRARY `Wd`** — the whole of route R-c. The only
thing used about a body is `IsDenseSlab.bodies_subset` (`X ⊆ S`) and the scale bound
`r ≤ ratio · R`, which at the tangential instance is `C₀ b ≤ 2 r₁`, implied by the producer's
own `∀ᶠ δ` binder `32 C₀ b ≤ r₁`. -/
theorem image_cthickening_subset_ball_of_doubled (c ν : E₃) (hν : ‖ν‖ = 1) {R ratio r : ℝ}
    (hR : 0 < R) (hratio : 0 < ratio) (hratio1 : ratio ≤ 1) (hr : 0 ≤ r)
    {X : Set E₃} (hXc : IsCompact X) (hX : X ⊆ (generalSlab c ν hν hR hratio).carrier)
    (hsmall : r ≤ ratio * R) :
    slabRescale c ν hν (by linarith : (0 : ℝ) < 2 * R) hratio '' Metric.cthickening r X
      ⊆ Metric.closedBall (0 : E₃) 1 := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  have hα : (0 : ℝ) < (2 * R)⁻¹ := by positivity
  have hβ : (0 : ℝ) < (ratio * (2 * R))⁻¹ := by positivity
  have hMax : max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ = (ratio * (2 * R))⁻¹ := by
    refine max_eq_right (inv_anti₀ (by positivity) ?_)
    nlinarith
  have hMr : max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ * r ≤ 1 / 2 := by
    rw [hMax, inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hstep := aniRescale_image_cthickening_subset c ν hν hα hβ hXc hr
  have himg : aniRescale c ν hν hα.ne' hβ.ne' '' X ⊆ Metric.closedBall (0 : E₃) (1 / 2) :=
    le_trans (Set.image_mono hX) (image_generalSlab_subset_half c ν hν hR hratio)
  have hMpos : (0 : ℝ) ≤ max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ * r := by
    have : (0 : ℝ) ≤ max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ := le_max_of_le_left hα.le
    positivity
  have s1 : Metric.cthickening (max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ * r)
      (aniRescale c ν hν hα.ne' hβ.ne' '' X)
      ⊆ Metric.cthickening (max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ * r)
        (Metric.closedBall (0 : E₃) (1 / 2)) :=
    Metric.cthickening_subset_of_subset _ himg
  have s2 := cthickening_closedBall_subset
    (max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ * r) (1 / 2) hMpos
  have s3 : Metric.closedBall (0 : E₃)
      (1 / 2 + max (2 * R)⁻¹ (ratio * (2 * R))⁻¹ * r) ⊆ Metric.closedBall (0 : E₃) 1 :=
    Metric.closedBall_subset_closedBall (by linarith [hMr])
  exact hstep.trans (s1.trans (s2.trans s3))

set_option maxHeartbeats 1000000 in
-- The engine is instantiated at the doubled radius, so the profile slot moves by 8 and 4.
/-- **Clause (A2) for a lattice cell at the DOUBLED map**, with the comparison constant carried
as a parameter. The existing engine
`Kakeya.VeryNotSticky.hasThicknesses_slabRescale_image_of_aligned` is general in the radius and
the aspect, so it applies once two `δ`-free bookkeeping moves are made: the body's profile
`(r₁, b, a)` at `bd.C₀` is read as `(8 r₁, 8 b, 4 a)` at `8 bd.C₀` — the doubled cell's radius
is `8 r₁`, and the conclusion's middle entry `8 b/(8 r₁) = ρ₂` is unchanged — and the
alignment is read at the cell's aspect, `κ · ratio = κ (a/b)/2`, so the `3 (a/b)` that
`Kakeya.VeryNotSticky.IsDenseSlab.angle_ratio` (`2 (a/b)`) and
`Kakeya.VeryNotSticky.lineAngle_bodyNormal_generalSlab_le` (`(a/b)`) supply needs `6 ≤ κ`.
`Kakeya.VeryNotSticky.route_B1_le_lattice` is exactly `κ = 6` under the pin. -/
theorem hasThicknesses_latticeCell_body (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (c n : E₃) (hn : ‖n‖ = 1) {κ : NNReal} (hκ : 6 ≤ κ) (W : ConvexSpaceBody E₃)
    (hprof : Kakeya.HasThicknesses W.carrier bd.C₀
      ![(cfg.r₁ : ℝ), (cfg.b : ℝ), (cfg.a : ℝ)])
    (hsub : W.carrier ⊆ (generalSlab c n hn
      (by linarith [latticeCellRadius_pos cfg] : (0 : ℝ) < 2 * latticeCellRadius cfg)
      (latticeCellRatio_pos cfg)).carrier)
    (halign : NonSlab.lineAngle (bodyNormal W) n
      ≤ 3 * ((cfg.a / cfg.b : NNReal) : ℝ)) :
    Kakeya.HasThicknesses
      (slabRescale c n hn
        (by linarith [latticeCellRadius_pos cfg] : (0 : ℝ) < 2 * latticeCellRadius cfg)
        (latticeCellRatio_pos cfg) '' W.carrier)
      (alignedRescaleConstant (8 * bd.C₀) κ) ![1, (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
  have hq0 : (0 : ℝ) < ((cfg.a / cfg.b : NNReal) : ℝ) := cfg_ratio_pos cfg
  have hr0 : (0 : ℝ) < (cfg.r₁ : ℝ) := r₁_pos cfg
  have hC₀R : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
  have hC₀0 : (0 : ℝ) < (bd.C₀ : ℝ) := by linarith
  have hb0 : (0 : ℝ) < (cfg.b : ℝ) := by
    have : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
    exact_mod_cast this
  have ha0 : (0 : ℝ) < (cfg.a : ℝ) := by
    have : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact_mod_cast this
  have hab : (cfg.a : ℝ) ≤ (cfg.b : ℝ) := by exact_mod_cast cfg.hdims.2.1
  have hκR : (6 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  have hC8 : ((8 * bd.C₀ : NNReal) : ℝ) = 8 * (bd.C₀ : ℝ) := by push_cast; ring
  have hinv8 : ((8 * bd.C₀ : NNReal) : ℝ)⁻¹ = ((bd.C₀ : ℝ))⁻¹ / 8 := by
    push_cast
    rw [mul_inv]
    ring
  have hinv0 : (0 : ℝ) < ((bd.C₀ : ℝ))⁻¹ := inv_pos.mpr hC₀0
  have hgen8 : ∀ t s : ℝ, 0 ≤ s → ((bd.C₀ : ℝ))⁻¹ * s ≤ t → t ≤ (bd.C₀ : ℝ) * s →
      ((8 * bd.C₀ : NNReal) : ℝ)⁻¹ * (8 * s) ≤ t ∧
        t ≤ ((8 * bd.C₀ : NNReal) : ℝ) * (8 * s) := by
    intro t s hs hlo hhi
    rw [hinv8, hC8]
    constructor
    · nlinarith [hlo]
    · nlinarith [hhi, hs, hC₀0]
  have hgen4 : ∀ t s : ℝ, 0 ≤ s → ((bd.C₀ : ℝ))⁻¹ * s ≤ t → t ≤ (bd.C₀ : ℝ) * s →
      ((8 * bd.C₀ : NNReal) : ℝ)⁻¹ * (4 * s) ≤ t ∧
        t ≤ ((8 * bd.C₀ : NNReal) : ℝ) * (4 * s) := by
    intro t s hs hlo hhi
    rw [hinv8, hC8]
    constructor
    · nlinarith [hlo, hs, hinv0]
    · nlinarith [hhi, hs, hC₀0]
  have hRR : 2 * latticeCellRadius cfg = 8 * (cfg.r₁ : ℝ) := by
    change 2 * (4 * (cfg.r₁ : ℝ)) = 8 * (cfg.r₁ : ℝ)
    ring
  have hprof8 : Kakeya.HasThicknesses W.carrier (8 * bd.C₀)
      ![8 * (cfg.r₁ : ℝ), 8 * (cfg.b : ℝ), 4 * (cfg.a : ℝ)] := by
    intro k
    have hk := hprof k
    fin_cases k
    · exact hgen8 _ _ hr0.le hk.1 hk.2
    · exact hgen8 _ _ hb0.le hk.1 hk.2
    · exact hgen4 _ _ ha0.le hk.1 hk.2
  have halign' : NonSlab.lineAngle (bodyNormal W) n ≤ (κ : ℝ) * latticeCellRatio cfg := by
    rw [latticeCellRatio]
    nlinarith [halign, hκR, hq0]
  have hmain := hasThicknesses_slabRescale_image_of_aligned c n hn
    (r₁ := 2 * latticeCellRadius cfg) (ratio := latticeCellRatio cfg)
    (a := 4 * (cfg.a : ℝ)) (b := 8 * (cfg.b : ℝ)) (C₀ := 8 * bd.C₀) (κ := κ)
    (by linarith [latticeCellRadius_pos cfg]) (latticeCellRatio_pos cfg)
    (latticeCellRatio_le_one cfg) (by linarith) (by linarith) (by linarith) ?_ ?_
    (le_trans (by norm_num) hκ) W ?_ hsub halign'
  · have hmid : 8 * (cfg.b : ℝ) / (2 * latticeCellRadius cfg) = (cfg.rho2 : ℝ) := by
      rw [hRR, cfg_rho2_coe]
      field_simp
    rwa [hmid] at hmain
  · rw [latticeCellRatio]
    have h := cfg_ratio_mul_b cfg
    field_simp
    linarith [h]
  · calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 8 * bd.C₀ := by gcongr; · norm_num
                          · exact bd.hC₀
  · rw [hRR]
    exact hprof8

/-! ### The tangential slab package at a general `(a, b)`, and conjunct 3 -/

set_option maxHeartbeats 1000000 in
-- Four clause producers in one term, each carrying the cell's shape through `hshape`.
/-- **`exists_slabPackage_general` with binders `{hCμ, hCΔ}`** — conjunct 3's conclusion,
obtained by doubling the normalization cell: `Kakeya.VeryNotSticky.SlabPackage.L` is a
free field, so the producer normalises the **doubled** cell. The cell then lands in `B̄(0,1/2)`
and the bodies' `τ₂`-neighbourhoods still land in `B̄(0,1)`, so clause (A1′) holds for **every**
`Wd` and **no statement moves anywhere** — neither a margin clause on
`Kakeya.VeryNotSticky.IsDenseSlab` (option R-a) nor a radius `2` in the binder (option R-b,
rejected: it would force the unit-ball convention of
`Kakeya.VeryNotSticky.KTRho2ScaleDataAt`, hence conjunct 4 a third time).

Beyond the two constant thresholds the theorem takes exactly the three side conditions this
file located and measured: `4 ≤ bd.C₀` (the cell's tangential radius), `32 C₀ b ≤ r₁` (a
`∀ᶠ δ` threshold, which also supplies route R-c's `C₀ b ≤ 2 r₁`), and the margin
`N_{τ₂(W_j)}(W_j) ⊆ B̄(ctr B, r₁)` that the existing degenerate producer already takes. -/
theorem exists_slabPackage_general_of_lattice (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ')
    (hCμ : ((degenerateCμ bd.C₀ ta.Ctyp : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-τ'))
    (hCΔ : ((degenerateCΔ (latticeRescaleConstant bd.C₀) bd.Cbias : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)))
    (hC₀4 : (4 : NNReal) ≤ bd.C₀)
    (hbr₁ : 32 * (bd.C₀ : ℝ) * (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ))
    (hmargin : ∀ j ∈ bd.bodies B,
      Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
        Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) :
    Nonempty (SlabPackage cfg ta) := by
  obtain ⟨nrmOf, ctrOf, 𝕊, slabOf, hfam, hnrm, hshape, _hcth, _halign⟩ :=
    exists_isSlabFamily_lattice cfg ta hC₀4 hbr₁ hmargin
  have hRpos := latticeCellRadius_pos cfg
  have h2R : (0 : ℝ) < 2 * latticeCellRadius cfg := by linarith
  have hC₀R : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
  have hC₀0 : (0 : ℝ) < (bd.C₀ : ℝ) := by linarith
  have hr0 : (0 : ℝ) < (cfg.r₁ : ℝ) := r₁_pos cfg
  have hq0 : (0 : ℝ) < ((cfg.a / cfg.b : NNReal) : ℝ) := cfg_ratio_pos cfg
  have hq1 : ((cfg.a / cfg.b : NNReal) : ℝ) ≤ 1 := cfg_ratio_le_one cfg
  have hb0 : (0 : ℝ) < (cfg.b : ℝ) := by
    have : (0 : NNReal) < cfg.b := lt_of_lt_of_le cfg.hδ (cfg.hdims.1.trans cfg.hdims.2.1)
    exact_mod_cast this
  have ha0 : (0 : ℝ) < (cfg.a : ℝ) := by
    have : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact_mod_cast this
  have hqb : ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.b : ℝ) = (cfg.a : ℝ) := cfg_ratio_mul_b cfg
  have hC₀b : (bd.C₀ : ℝ) * (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ) := by nlinarith [hbr₁, hb0, hC₀0]
  have hjB : ∀ (Wd : Finset bd.ω), Wd ⊆ ta.sel → ∀ j ∈ Wd, j ∈ bd.bodies B :=
    fun Wd hWd j hj => (tc.thinBall hB).bodies'_subset (ta.hsel (hWd hj))
  -- the thin scale of a body, and the scale bound route R-c needs
  have hscale : ∀ (Wd : Finset bd.ω), Wd ⊆ ta.sel → ∀ j ∈ Wd,
      (bd.Wb j).scale ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
    intro Wd hWd j hj
    have h2 := (bd.bodies_thickness B hB j (hjB Wd hWd j hj) 2).2
    simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
    have hs : (bd.Wb j).scale = Metric.thickness ℝ (bd.Wb j).carrier 2 := by
      change Metric.thickness ℝ (bd.Wb j).carrier
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) = _
      rw [finrank_euclideanSpace_fin]
    rw [hs]; exact h2
  have hsc0 : ∀ j : bd.ω, (0 : ℝ) ≤ (bd.Wb j).scale := by
    intro j
    have hsdef : (bd.Wb j).scale = Metric.thickness ℝ (bd.Wb j).carrier
        (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) := rfl
    rw [hsdef]; exact Metric.thickness_nonneg _ _
  have hsmall : ∀ (Wd : Finset bd.ω), Wd ⊆ ta.sel → ∀ j ∈ Wd,
      (bd.Wb j).scale ≤ latticeCellRatio cfg * latticeCellRadius cfg := by
    intro Wd hWd j hj
    rw [latticeCell_width]
    have h := hscale Wd hWd j hj
    nlinarith [h, hC₀b, hqb, hq0, hr0, hb0, ha0, hC₀0]
  -- the alignment against the cell's defining normal, for an arbitrary dense slab
  have halignS : ∀ (S : ConvexSpaceBody E₃) (Wd : Finset bd.ω), IsDenseSlab cfg ta 𝕊 S Wd →
      ∀ j ∈ Wd, NonSlab.lineAngle (bodyNormal (bd.Wb j)) (nrmOf S)
        ≤ 3 * ((cfg.a / cfg.b : NNReal) : ℝ) := by
    intro S Wd hslab j hj
    have hS := hshape S hslab.mem (hnrm S)
    have h1 : NonSlab.lineAngle (bodyNormal (bd.Wb j)) (bodyNormal S)
        ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ) := by
      have := hslab.angle_ratio j hj
      rwa [axisAngle_eq_lineAngle] at this
    have h2 : NonSlab.lineAngle (bodyNormal S) (nrmOf S) ≤ 2 * latticeCellRatio cfg := by
      have hg := lineAngle_bodyNormal_generalSlab_le (ctrOf S) (nrmOf S) (hnrm S)
        (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) (latticeCellRatio_le_one cfg)
      rwa [← hS] at hg
    have h3 := NonSlab.lineAngle_le_add (bodyNormal (bd.Wb j)) (bodyNormal S) (nrmOf S)
    have h4 : 2 * latticeCellRatio cfg = ((cfg.a / cfg.b : NNReal) : ℝ) := by
      rw [latticeCellRatio]; ring
    rw [h4] at h2
    linarith [h1, h2, h3]
  -- (A2), for an arbitrary dense slab
  have hA2 : ∀ (S : ConvexSpaceBody E₃) (Wd : Finset bd.ω), IsDenseSlab cfg ta 𝕊 S Wd →
      ∀ j ∈ Wd, Kakeya.HasThicknesses
        (slabRescale (ctrOf S) (nrmOf S) (hnrm S) h2R (latticeCellRatio_pos cfg)
          '' (bd.Wb j).carrier)
        (latticeRescaleConstant bd.C₀) ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
    intro S Wd hslab j hj
    have hS := hshape S hslab.mem (hnrm S)
    have hsub : (bd.Wb j).carrier ⊆ (generalSlab (ctrOf S) (nrmOf S) (hnrm S) h2R
        (latticeCellRatio_pos cfg)).carrier := by
      refine le_trans ?_ (generalSlab_subset_doubled (ctrOf S) (nrmOf S) (hnrm S)
        (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg))
      rw [← hS]; exact hslab.bodies_subset j hj
    have hκ : (6 : NNReal) ≤ 10 + 4 * bd.C₀ ^ 2 :=
      le_trans (by norm_num) (le_self_add : (10 : NNReal) ≤ 10 + 4 * bd.C₀ ^ 2)
    exact hasThicknesses_latticeCell_body cfg (ctrOf S) (nrmOf S) (hnrm S) hκ (bd.Wb j)
      (bd.bodies_thickness B hB j (hjB Wd hslab.subset j hj)) hsub (halignS S Wd hslab j hj)
  refine ⟨exists_slabPackage_general cfg ta hCμ hCΔ 𝕊 slabOf hfam
    (fun S => slabRescale (ctrOf S) (nrmOf S) (hnrm S) h2R (latticeCellRatio_pos cfg))
    ?_ ?_ hA2 ?_ |>.some⟩
  · -- (A1)
    intro S Wd hslab j hj
    have hS := hshape S hslab.mem (hnrm S)
    calc slabRescale (ctrOf S) (nrmOf S) (hnrm S) h2R (latticeCellRatio_pos cfg)
          '' (bd.Wb j).carrier
        ⊆ slabRescale (ctrOf S) (nrmOf S) (hnrm S) h2R (latticeCellRatio_pos cfg) ''
            (generalSlab (ctrOf S) (nrmOf S) (hnrm S) h2R (latticeCellRatio_pos cfg)).carrier := by
          refine Set.image_mono (le_trans ?_ (generalSlab_subset_doubled (ctrOf S) (nrmOf S)
            (hnrm S) (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg)))
          rw [← hS]; exact hslab.bodies_subset j hj
      _ = Metric.closedBall 0 1 := slabRescale_image_generalSlab _ _ _ _ _
  · -- (A1′) — route R-c: the doubled map, no clause added
    intro S Wd hslab j hj
    have hS := hshape S hslab.mem (hnrm S)
    rw [ConvexSpaceBody.cthickening_carrier]
    refine image_cthickening_subset_ball_of_doubled (ctrOf S) (nrmOf S) (hnrm S)
      (latticeCellRadius_pos cfg) (latticeCellRatio_pos cfg) (latticeCellRatio_le_one cfg)
      (hsc0 j) (bd.Wb j).isCompact' ?_ (hsmall Wd hslab.subset j hj)
    rw [← hS]; exact hslab.bodies_subset j hj
  · -- (A2′), from (A2): R7 is not used
    intro S Wd hslab j hj
    have hwpos : (0 : ℝ) < latticeCellRatio cfg * (2 * latticeCellRadius cfg) :=
      mul_pos (latticeCellRatio_pos cfg) h2R
    have hαpos : (0 : ℝ) < (2 * latticeCellRadius cfg)⁻¹ := inv_pos.mpr h2R
    have hβpos : (0 : ℝ) < (latticeCellRatio cfg * (2 * latticeCellRadius cfg))⁻¹ :=
      inv_pos.mpr hwpos
    have hCmp1 : (1 : NNReal) ≤ latticeRescaleConstant bd.C₀ :=
      one_le_latticeRescaleConstant bd.hC₀
    have hCmpC₀ : (bd.C₀ : ℝ) ≤ (latticeRescaleConstant bd.C₀ : ℝ) := by
      exact_mod_cast le_latticeRescaleConstant bd.hC₀
    have hCmp0 : (0 : ℝ) ≤ (latticeRescaleConstant bd.C₀ : ℝ) := NNReal.coe_nonneg _
    have hrho : ((cfg.rho2 : NNReal) : ℝ) = (cfg.b : ℝ) / (cfg.r₁ : ℝ) := cfg_rho2_coe cfg
    have hrho0 : (0 : ℝ) ≤ ((cfg.rho2 : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hrho1 : ((cfg.rho2 : NNReal) : ℝ) ≤ 1 := by
      rw [hrho, div_le_one hr0]
      nlinarith [hC₀b, hC₀R, hb0]
    have hmax : max (2 * latticeCellRadius cfg)⁻¹
        (latticeCellRatio cfg * (2 * latticeCellRadius cfg))⁻¹
        = (latticeCellRatio cfg * (2 * latticeCellRadius cfg))⁻¹ := by
      refine max_eq_right (inv_anti₀ (by positivity) ?_)
      nlinarith [latticeCellRatio_le_one cfg, latticeCellRatio_pos cfg, h2R]
    rw [ConvexSpaceBody.cthickening_carrier]
    refine hasThicknesses_aniRescale_cthickening_of_image (ctrOf S) (nrmOf S) (hnrm S)
      hαpos hβpos (bd.Wb j).isCompact' (bd.Wb j).nonempty' (hsc0 j) hCmp1 ?_
      (hA2 S Wd hslab j hj) ?_
    · intro k
      fin_cases k
      · norm_num
      · exact NNReal.coe_nonneg _
      · exact NNReal.coe_nonneg _
    · intro k
      have hkey : max (2 * latticeCellRadius cfg)⁻¹
          (latticeCellRatio cfg * (2 * latticeCellRadius cfg))⁻¹ * (bd.Wb j).scale
          ≤ (latticeRescaleConstant bd.C₀ : ℝ) * ((cfg.rho2 : NNReal) : ℝ) := by
        rw [hmax, hrho]
        have hw : latticeCellRatio cfg * (2 * latticeCellRadius cfg)
            = 4 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)) := by
          change ((cfg.a / cfg.b : NNReal) : ℝ) / 2 * (2 * (4 * (cfg.r₁ : ℝ))) = _
          ring
        rw [hw, inv_mul_le_iff₀ (by positivity)]
        have hst := hscale Wd hslab.subset j hj
        have hab' : 4 * (((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ))
            * ((cfg.b : ℝ) / (cfg.r₁ : ℝ)) = 4 * (cfg.a : ℝ) := by
          field_simp; linarith [hqb]
        nlinarith [hst, hab', hCmpC₀, hq0, hr0, hb0, ha0, hC₀0]
      have htk : ((cfg.rho2 : NNReal) : ℝ)
          ≤ ![(1 : ℝ), ((cfg.rho2 : NNReal) : ℝ), ((cfg.rho2 : NNReal) : ℝ)] k := by
        fin_cases k
        · exact hrho1
        · exact le_rfl
        · exact le_rfl
      exact le_trans hkey (mul_le_mul_of_nonneg_left htk hCmp0)

/-- **The general boundary's `hslabPackage` binder, discharged** — conjunct 3 at general
`(a, b)`, byte-for-byte the text `Kakeya.VeryNotSticky.sideDataResidue_of_obligations_general`
carries (`SetupSideDataGeneral.lean:501-511`). The `32 C₀ b ≤ r₁` side condition is a `∀ᶠ δ`
threshold: `b ≤ δ^{2 exscal}` and `r₁ = δ^{exscal}` reduce it to `32 C₀ δ^{exscal} ≤ 1`. -/
theorem eventually_slabPackage_general_of_lattice {β exscal ϱ η τ' : ℝ} (hη : 0 < η)
    (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hητ' : η < τ') (C₀bd Cbias : NNReal)
    (hC₀bd : (4 : NNReal) ≤ C₀bd) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a ≤ cfg.δ ^ (1 - τ') → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) →
      bd.C₀ = C₀bd → bd.Cbias = Cbias →
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
          Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta) := by
  filter_upwards [eventually_degenerateCμ_le C₀bd hη hexscal.le hητ',
    eventually_degenerateCΔ_le (latticeRescaleConstant C₀bd) Cbias hϱ,
    eventually_rpow_le_of_pos_nnreal hexscal (c := (32 * C₀bd)⁻¹)
      (by
        have hpos : (0 : NNReal) < 32 * C₀bd := by
          have : (0 : NNReal) < C₀bd := lt_of_lt_of_le (by norm_num) hC₀bd
          positivity
        simpa using inv_pos.mpr hpos)] with d hCμ hCΔ hthr
  intro cfg bd tc hδ _hβ hη' hex hϱ' _ha hb hC₀ hCb hmargin B hB ta
  subst hδ
  subst hη'
  subst hex
  subst hϱ'
  subst hC₀
  subst hCb
  have hC₀0 : (0 : NNReal) < 32 * bd.C₀ := by
    have : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le (by norm_num) hC₀bd
    positivity
  have hbr₁ : 32 * (bd.C₀ : ℝ) * (cfg.b : ℝ) ≤ (cfg.r₁ : ℝ) := by
    have hr : cfg.r₁ = cfg.δ ^ cfg.exscal := rfl
    have h2 : cfg.δ ^ (2 * cfg.exscal) = cfg.δ ^ cfg.exscal * cfg.δ ^ cfg.exscal := by
      rw [two_mul, NNReal.rpow_add cfg.hδ.ne']
    have hstep : 32 * bd.C₀ * cfg.b ≤ cfg.r₁ := by
      calc 32 * bd.C₀ * cfg.b
          ≤ 32 * bd.C₀ * (cfg.δ ^ cfg.exscal * cfg.δ ^ cfg.exscal) := by
            rw [← h2]; gcongr
        _ = (32 * bd.C₀ * cfg.δ ^ cfg.exscal) * cfg.δ ^ cfg.exscal := by ring
        _ ≤ 1 * cfg.δ ^ cfg.exscal := by
            gcongr
            calc 32 * bd.C₀ * cfg.δ ^ cfg.exscal ≤ 32 * bd.C₀ * (32 * bd.C₀)⁻¹ := by
                  gcongr
              _ = 1 := mul_inv_cancel₀ hC₀0.ne'
        _ = cfg.r₁ := by rw [hr, one_mul]
    exact_mod_cast hstep
  exact exists_slabPackage_general_of_lattice cfg ta (hCμ ta.Ctyp ta.hCtyp) hCΔ hC₀bd hbr₁
    (hmargin B hB)

end

end Kakeya.VeryNotSticky
