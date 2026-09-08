/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.CollarPlankPresentation
public import Kakeya.DimensionThree.Plank.EDConflictFromDilation
public import Kakeya.Factoring.FlatPrisms

/-!
# The plank-presented Part-(B) outer family has a bounded conflict degree

`Kakeya/DimensionThree/Plank/CollarPlankEDRefutation.lean` refutes both the identification
`(W x).toPrism3D = D.factor.repr x` and the transport `ED(reprs) ⟹ ED(presented planks)`, so the
essential distinctness that `Kakeya.factoringAndMultPropGlobal` exports must be **produced** for the
presented family, by extraction.  `Kakeya/DimensionThree/Plank/EDConflictFromDilation.lean` shows
the extraction consumes exactly one number: a bound on

`card {j ∈ s | (W j).carrier ⊆ (Λ-dilation of (W i).toPrism3D)}`.

This file supplies that number, and it needs no packing count, no direction cap and no comparison of
orthonormal frames.  **The datum's own Katz--Tao hypothesis on the cell bodies is the count.**

## The argument

`Kakeya.collarPlank`'s plank contains the shrunk collar of the body
(`Kakeya.scaledCollar_le_collarPlank`), and the shrink is *one common homothety about the origin*.
So a containment of presented planks pulls back **exactly** — by the inverse homothety, not by any
geometric comparison — to a containment of bodies in a single prism:

`Kakeya.collarConflictContainer`, the `Λ`-dilation of the anchor's presented plank scaled by
`(comparablePlankEnvelope.shrink (windowPlankEnvelope.windowConst R Cw))⁻¹`,

whose volume is the plank volume `8ab` inflated by the absolute factor `(Λ / shrink)³`
(`Kakeya.volume_collarConflictContainer`).  Now count: every cell body has
`volume ≥ (Cw³)⁻¹ · c₃ · ab` (`Kakeya.IsPlankOfDimensions.volume_lower`), and
`ConvexSpaceBody.isKatzTao_iff` bounds the total volume of the bodies inside the container by
`C₀ · |container|`.  Both `a` and `b` cancel, and the count is

`C₀ · Kakeya.collarConflictConst R Cw Λ`,  `collarConflictConst = 8 (Λ/shrink)³ Cw³ / c₃`,

with the constant depending on `R`, `Cw`, `Λ` and the dimension alone — not on `a`, `b` or `δ`.

## What this costs, and where the cost lands

The count is `C₀ ·` absolute, not absolute: it is proportional to the datum's Katz--Tao constant,
which Proposition 6.6(B) constrains only by `C₀ ≤ δ ^ (-η)`.  So the extraction loss `d + 1` of
`Kakeya.exists_pairwise_ED_collarPlank_subfamily` is **sub-polynomial**, which is the currency the
Part-(B) assembly already runs on — but it is *not* absolute, and
`Kakeya.factoringAndMultPropGlobal` currently exports its multiplicity split with an **absolute**
`Csplit` fixed before `δ` exists.  A producer that shrinks `ts` to the extracted subfamily must pay
`d + 1` there (`ShadedBody.multiplicity_le_of_isCRefinement`), so that clause has to become
`Csplit * δ ^ (-η)`.  `Kakeya.subpoly_split_absorb` below is the consumer-side check that this is
free: the single call site absorbs `Csplit · δ ^ (-η) · Ccard ^ β` into its `δ ^ (-(ε/6))` slot on
the same threshold argument it already runs for `Csplit · Ccard ^ β`, as soon as the leaf's produced
`η` is at most `ε / 12`.

An **absolute** count is also available, by a different route: send the containment through the
representative planks — which *are* pairwise essentially distinct, by the datum's own hypothesis —
and apply the anisotropic packing count.  That route needs a comparison of the
presented plank's frame with the representative's, and it is not taken here.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

open comparablePlankEnvelope windowPlankEnvelope

variable {ι : Type*}

/-- The pull-back container. -/
def collarConflictContainer {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) (Λ : ℝ≥0)
    (Ki : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Yi : ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  (((collarPlank hR hCw hab hb1 Ki Yi).toPrism3D.toPrismNDim).dilation Λ).homothety 0
    (shrink (windowConst R Cw))⁻¹

/-- A body whose presented plank lies in the `Λ`-dilation of the anchor's lies in the container. -/
theorem le_collarConflictContainer {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {Λ : ℝ≥0}
    {Ki Kj : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {Yi Yj : ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hj : IsCollarPresentable R Cw a b Kj Yj)
    (hsub : ((collarPlank hR hCw hab hb1 Kj Yj).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((((collarPlank hR hCw hab hb1 Ki Yi).toPrism3D.toPrismNDim).dilation Λ).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))) :
    Kj ≤ (collarConflictContainer hR hCw hab hb1 Λ Ki Yi).toConvexSpaceBody := by
  have hC : 1 ≤ windowConst R Cw := one_le_windowConst hR hCw
  have hlam : 0 < shrink (windowConst R Cw) := shrink_pos hC
  have hlaminv : 0 < (shrink (windowConst R Cw))⁻¹ := by positivity
  intro x hx
  -- the shrunk body is inside the shrunk collar, hence inside the presented plank
  have hxc : x ∈ Metric.cthickening (scaleRadius Kj : ℝ) (Kj.carrier : Set _) :=
    Metric.self_subset_cthickening _ hx
  have himg : AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3))
      ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) x ∈
      ((scaledCollar (windowConst R Cw) Kj).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    ⟨x, hxc, rfl⟩
  have hplank : AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3))
      ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) x ∈
      ((collarPlank hR hCw hab hb1 Kj Yj).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    scaledCollar_le_collarPlank hR hCw hab hb1 hj himg
  have hdil := hsub hplank
  -- pull back by the inverse homothety
  have hkey := (PrismNDim.mem_homothety_iff
    (((collarPlank hR hCw hab hb1 Ki Yi).toPrism3D.toPrismNDim).dilation Λ) 0 hlaminv
    (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3))
      ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) x)).mpr hdil
  have hcancel : AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3))
      (((shrink (windowConst R Cw))⁻¹ : ℝ≥0) : ℝ)
      (AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3))
        ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) x) = x := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero,
      smul_smul, NNReal.coe_inv]
    rw [inv_mul_cancel₀ (by exact_mod_cast hlam.ne' : ((shrink (windowConst R Cw) : ℝ≥0) : ℝ) ≠ 0),
      one_smul]
  rwa [hcancel] at hkey

/-- The container's volume: the plank volume `8ab` inflated by the absolute factor
`(Λ / shrink)³`. -/
theorem volume_collarConflictContainer {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) (Λ : ℝ≥0)
    (Ki : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Yi : ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    volume ((collarConflictContainer hR hCw hab hb1 Λ Ki Yi).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
      = 8 * (((shrink (windowConst R Cw))⁻¹ * Λ : ℝ≥0) : ENNReal) ^ 3
          * (a : ENNReal) * (b : ENNReal) := by
  rw [PrismNDim.volume_carrier, finrank_euclideanSpace_fin, Fin.prod_univ_three]
  have hth : ∀ i : Fin 3, (collarConflictContainer hR hCw hab hb1 Λ Ki Yi).thicknesses i
      = (shrink (windowConst R Cw))⁻¹ * (Λ * (![a, b, 1] : Fin 3 → ℝ≥0) i) := by
    intro i
    rfl
  rw [hth 0, hth 1, hth 2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  push_cast
  ring

/-- The absolute constant of the conflict count: the container-to-body volume ratio. -/
def collarConflictConst (R Cw Λ : ℝ≥0) : ℝ≥0 :=
  8 * ((shrink (windowConst R Cw))⁻¹ * Λ) ^ 3 * Cw ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹

open Classical in
/-- **The dilation count for the plank-presented family, from the datum's own Katz--Tao
constant.** -/
theorem card_filter_collarPlank_subset_dilation_le {R Cw a b : ℝ≥0}
    (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1) (ha : 0 < a) {Λ C₀ : ℝ≥0}
    (s : Finset ι) (K : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hdim : ∀ j ∈ s, IsPlankOfDimensions Cw a b (K j))
    (hpres : ∀ j ∈ s, IsCollarPresentable R Cw a b (K j) (Y j))
    (hKT : ConvexSpaceBody.IsKatzTao s K (C₀ : ENNReal)) (i : ι) :
    ((s.filter fun j =>
        ((collarPlank hR hCw hab hb1 (K j) (Y j)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((((collarPlank hR hCw hab hb1 (K i) (Y i)).toPrism3D.toPrismNDim).dilation
              Λ).carrier : Set (EuclideanSpace ℝ (Fin 3)))).card : ENNReal)
      ≤ (C₀ : ENNReal) * (collarConflictConst R Cw Λ : ENNReal) := by
  classical
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hCw0 : (Cw : ENNReal) ≠ 0 := by
    simpa using (lt_of_lt_of_le zero_lt_one hCw).ne'
  have hc0 : (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
  set Q := collarConflictContainer hR hCw hab hb1 Λ (K i) (Y i) with hQdef
  set F := s.filter (fun j =>
    ((collarPlank hR hCw hab hb1 (K j) (Y j)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((((collarPlank hR hCw hab hb1 (K i) (Y i)).toPrism3D.toPrismNDim).dilation Λ).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))) with hFdef
  set X : ENNReal := ((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) with hXdef
  -- every counted body lies in the container
  have hFG : F ⊆ s.filter (fun j => K j ≤ Q.toConvexSpaceBody) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hj'.1,
      le_collarConflictContainer hR hCw hab hb1 (hpres j hj'.1) hj'.2⟩
  -- each counted body has volume at least `X * (a * b)`
  have hlow : ∀ j ∈ F, X * ((a : ENNReal) * (b : ENNReal)) ≤ volume (K j).carrier := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    simpa [hXdef, mul_assoc] using
      (hdim j hj'.1).volume_lower (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
  have hcard : (F.card : ENNReal) * (X * ((a : ENNReal) * (b : ENNReal)))
      ≤ ∑ j ∈ F, volume (K j).carrier := by
    simpa [nsmul_eq_mul] using Finset.card_nsmul_le_sum F _ _ hlow
  have hKTQ : ∑ j ∈ s.filter (fun j => K j ≤ Q.toConvexSpaceBody), volume (K j).carrier
      ≤ (C₀ : ENNReal) * volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    (ConvexSpaceBody.isKatzTao_iff s K _).mp hKT Q.toConvexSpaceBody
  have hchain : (F.card : ENNReal) * (X * ((a : ENNReal) * (b : ENNReal)))
      ≤ (C₀ : ENNReal) * (8 * (((shrink (windowConst R Cw))⁻¹ * Λ : ℝ≥0) : ENNReal) ^ 3
          * (a : ENNReal) * (b : ENNReal)) := by
    refine hcard.trans ((Finset.sum_le_sum_of_subset hFG).trans ?_)
    rw [← volume_collarConflictContainer hR hCw hab hb1 Λ (K i) (Y i)]
    exact hKTQ
  -- cancel `a * b`, then divide by `X`
  have hu0 : ((a : ENNReal) * (b : ENNReal)) ≠ 0 := by
    simp [ENNReal.coe_eq_zero, ha.ne', hb0.ne']
  have hutop : ((a : ENNReal) * (b : ENNReal)) ≠ ⊤ := by
    simp [ENNReal.mul_ne_top]
  have hcancel : (F.card : ENNReal) * X
      ≤ (C₀ : ENNReal) * (8 * (((shrink (windowConst R Cw))⁻¹ * Λ : ℝ≥0) : ENNReal) ^ 3) := by
    refine (ENNReal.mul_le_mul_iff_left hu0 hutop).mp ?_
    calc (F.card : ENNReal) * X * ((a : ENNReal) * (b : ENNReal))
        = (F.card : ENNReal) * (X * ((a : ENNReal) * (b : ENNReal))) := by ring
      _ ≤ (C₀ : ENNReal) * (8 * (((shrink (windowConst R Cw))⁻¹ * Λ : ℝ≥0) : ENNReal) ^ 3
            * (a : ENNReal) * (b : ENNReal)) := hchain
      _ = (C₀ : ENNReal) * (8 * (((shrink (windowConst R Cw))⁻¹ * Λ : ℝ≥0) : ENNReal) ^ 3)
            * ((a : ENNReal) * (b : ENNReal)) := by ring
  have hCwtop : ((Cw : ENNReal) ^ 3) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hX0 : X ≠ 0 := by
    refine mul_ne_zero ?_ hc0
    simp [ENNReal.inv_eq_zero, hCwtop]
  have hXtop : X ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top
    simp [ENNReal.inv_eq_top, pow_ne_zero 3 hCw0]
  have hXinv : X⁻¹ = (Cw : ENNReal) ^ 3 * (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ := by
    rw [hXdef, ENNReal.mul_inv (Or.inl (by simpa [ENNReal.inv_eq_zero] using hCwtop))
      (Or.inl (by simp [ENNReal.inv_eq_top, pow_ne_zero 3 hCw0])), inv_inv]
  calc (F.card : ENNReal) = (F.card : ENNReal) * (X * X⁻¹) := by
        rw [ENNReal.mul_inv_cancel hX0 hXtop, mul_one]
    _ = ((F.card : ENNReal) * X) * X⁻¹ := by ring
    _ ≤ ((C₀ : ENNReal) * (8 * (((shrink (windowConst R Cw))⁻¹ * Λ : ℝ≥0) : ENNReal) ^ 3)) * X⁻¹ :=
        by gcongr
    _ = (C₀ : ENNReal) * (collarConflictConst R Cw Λ : ENNReal) := by
        rw [hXinv, collarConflictConst]
        push_cast [ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne']
        ring

open Classical in
/-- **The essentially-distinct subfamily of the plank-presented Part-(B) outer family.**

The clause `Kakeya.factoringAndMultPropGlobal` exports, produced for the homothety-presented family
`Kakeya.collarPlank`, at a loss that is `⌈C₀ · (absolute)⌉₊ + 1` — sub-polynomial wherever the
datum's Katz--Tao constant is. -/
theorem exists_pairwise_ED_collarPlank_subfamily {R Cw a b : ℝ≥0}
    (hR : 1 ≤ R) (hCw : 1 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1) (ha : 0 < a) {C₀ : ℝ≥0}
    (s : Finset ι) (K : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hdim : ∀ j ∈ s, IsPlankOfDimensions Cw a b (K j))
    (hpres : ∀ j ∈ s, IsCollarPresentable R Cw a b (K j) (Y j))
    (hKT : ConvexSpaceBody.IsKatzTao s K (C₀ : ENNReal)) :
    ∃ s' ⊆ s,
      (s' : Set ι).Pairwise (fun x y => _root_.IsEssentiallyDistinct
        ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((collarPlank hR hCw hab hb1 (K y) (Y y)).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      s.card ≤ (⌈((C₀ * collarConflictConst R Cw 11 : ℝ≥0) : ℝ)⌉₊ + 1) * s'.card ∧
      (∑ j ∈ s, volume (collarPlank hR hCw hab hb1 (K j) (Y j)).shade)
        ≤ ((⌈((C₀ * collarConflictConst R Cw 11 : ℝ≥0) : ℝ)⌉₊ : ENNReal) + 1)
            * ∑ j ∈ s', volume (collarPlank hR hCw hab hb1 (K j) (Y j)).shade := by
  classical
  refine exists_pairwise_plank_ED_subfamily_of_dilation_count (le_refl (11 : ℝ≥0)) s
    (fun j => collarPlank hR hCw hab hb1 (K j) (Y j)) ?_
  intro i _
  have hE := card_filter_collarPlank_subset_dilation_le hR hCw hab hb1 ha
    (Λ := 11) (C₀ := C₀) s K Y hdim hpres hKT i
  have hNN : (((s.filter fun j =>
      ((collarPlank hR hCw hab hb1 (K j) (Y j)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((((collarPlank hR hCw hab hb1 (K i) (Y i)).toPrism3D.toPrismNDim).dilation
            11).carrier : Set (EuclideanSpace ℝ (Fin 3)))).card : ℝ≥0) : ℝ)
      ≤ ((C₀ * collarConflictConst R Cw 11 : ℝ≥0) : ℝ) := by
    have := hE
    rw [show ((s.filter fun j =>
        ((collarPlank hR hCw hab hb1 (K j) (Y j)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((((collarPlank hR hCw hab hb1 (K i) (Y i)).toPrism3D.toPrismNDim).dilation
              11).carrier : Set (EuclideanSpace ℝ (Fin 3)))).card : ENNReal)
        = (((s.filter fun j =>
        ((collarPlank hR hCw hab hb1 (K j) (Y j)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((((collarPlank hR hCw hab hb1 (K i) (Y i)).toPrism3D.toPrismNDim).dilation
              11).carrier : Set (EuclideanSpace ℝ (Fin 3)))).card : ℝ≥0) : ENNReal) from by
      push_cast; ring, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at this
    exact_mod_cast this
  exact_mod_cast hNN.trans (Nat.le_ceil _)

/-! ### The consumer-side check: a sub-polynomial extraction loss is free -/

/-- **Absorbing a sub-polynomial extraction loss into the split budget.**

If the leaf's produced exponent `η` is at most `ε / 12`, the consumer's absorption of the absolute
split constant `C` into `δ ^ (-(ε/6))` still works with the extra factor `δ ^ (-η)` — on the same
threshold argument (`Kakeya.exists_threshold_le_rpow_neg`) it already runs.  This is what makes the
`C₀`-proportional conflict degree of `Kakeya.exists_pairwise_ED_collarPlank_subfamily` usable: the
`d + 1` of the extraction is exactly such a factor. -/
theorem subpoly_split_absorb (C : ℝ≥0) (hC : 1 ≤ C) {ε η : ℝ} (hη : 0 < η)
    (hηε : η ≤ ε / 12) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → δ ≤ 1 →
      (C : ENNReal) * (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-(ε / 6)) := by
  obtain ⟨δ₀, hδ₀, hfun⟩ :=
    exists_threshold_le_rpow_neg C hC (show (0 : ℝ) < ε / 12 by linarith)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ0 hδδ₀ hδ1
  have hδ0' : (δ : ENNReal) ≠ 0 := by simpa using hδ0.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1' : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have h1 : (C : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 12)) := by
    have hNN := hfun δ hδ0 hδδ₀
    have h := (ENNReal.coe_le_coe (r := C) (q := δ ^ (-(ε / 12)))).mpr hNN
    rwa [ENNReal.coe_rpow_of_ne_zero hδ0.ne'] at h
  have h2 : (δ : ENNReal) ^ (-η) ≤ (δ : ENNReal) ^ (-(ε / 12)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδ1' (by linarith)
  calc (C : ENNReal) * (δ : ENNReal) ^ (-η)
      ≤ (δ : ENNReal) ^ (-(ε / 12)) * (δ : ENNReal) ^ (-(ε / 12)) := mul_le_mul' h1 h2
    _ = (δ : ENNReal) ^ (-(ε / 6)) := by
        rw [← ENNReal.rpow_add _ _ hδ0' hδtop]
        ring_nf

end Kakeya

end

end
