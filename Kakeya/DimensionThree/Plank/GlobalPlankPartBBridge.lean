/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Prop66BFactorsClause
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation

/-!
# From the GWZ 6.6(B) datum to the tree's Part-(B) factorisation

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B)) quantifies over
`Kakeya.GlobalPlankFactorization`, whose clause (ii) of `def:Factors` — the field
`ConvexSpaceBody.Factorization.maxDensity_le_mul` — is read against the **convex hull** of the
block.  The tree's proved Part-(B) pipeline
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`) consumes
`Kakeya.Section6PartBFactorisation`, whose `coarse_fibre_frostman` is clause (ii) read against
the **representative plank**, which is GWZ's own reading.

This file builds the second from the first.  Three things have to be produced, and each was
recorded as open:

* **the representative plank as data, with a *single* pair of half-widths.**  The datum pins the
  thin thickness of a cell hull only from above, so the declared `a` is not the right half-width:
  the Frostman loss against an `a × b × 1` plank carries the unbounded factor `a / τ₂(hull)`
  (`Kakeya.GlobalPlankFactorization.exists_isFrostmanIn_le_plank_of_thin_comparable`).  The repair
  is to *re-declare the half-widths downward*, to
  `Kakeya.GlobalPlankFactorization.uniformThin` `= ⨆_t τ₂(hull_t)` and
  `Kakeya.GlobalPlankFactorization.uniformMid` `= ⨆_t τ₁(hull_t)`.  Both are single numbers valid
  for every cell, both are dominated by `K * a'` resp. `K * b` through
  `Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`, and the resulting Frostman
  loss is the scale-free constant `Kakeya.GlobalPlankFactorization.coarseFibreFrostmanConst`.

* **`repr_window`.**  The field's own docstring says the containment
  `repr x ⊆ closedBall 0 plankWindowRadius` "genuinely has to be part of the datum".  That is true
  for the plank handed over by `le_plank`, whose centre is free; it is **false** for a plank built
  from the body's own outer prism *and re-centred*.  `Kakeya.framedCenter` deletes the long-axis
  component of the outer-prism centre, and `Kakeya.framedPlank_subset_closedBall` then gives the
  containment at radius exactly `4 = Kakeya.plankWindowRadius`.

* **`coarse_fibre_frostman`.**  Produced from the hull reading by
  `Kakeya.GlobalPlankFactorization.isFrostmanIn_plank_of_isPlankOfDimensions`, whose volume input
  is exactly what the `wide` field of the 6.6(B) datum supplies: `wide` is the quantitative
  statement that the declared `b` is not over-declared, i.e. that `|repr| ≲ Cw * |hull|`.

The price is recorded in the statement of
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`: the produced factorisation has
half-widths `(A, B)` with `A ≤ K * a'` and `b ≤ K * B`, so `A / B ≤ K² * (a / b)` and a conclusion
proved at `(A, B)` weakens back to the declared `(a, b)` at the cost of `K²`, which is
sub-polynomial under the 6.6(B) budget `Cw, C₀ ≤ δ ^ (-η)`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody

open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-! ### The framed plank of a convex body -/

theorem abs_repr_rawPrism_le {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (j : Fin 3) :
    |(rawPrism W).basis.repr (x - (rawPrism W).center) j| ≤ (thicknessNN W (j : ℕ) : ℝ) := by
  have hself := outerPrism.self_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) W.isCompact' W.nonempty' hx
  have h := ((rawPrism W).mem_carrier_iff x).mp hself j
  simpa [rawPrism, outerPrism.thicknesses_eq, thicknessNN] using h


/-- The frame-recentred centre: the outer-prism centre with its component along the *long* axis
(rank `0`) deleted. -/
def framedCenter (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : EuclideanSpace ℝ (Fin 3) :=
  (rawPrism W).center - ((rawPrism W).basis.repr (rawPrism W).center 0) • (rawPrism W).basis 0

theorem repr_framedCenter_zero (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    (rawPrism W).basis.repr (framedCenter W) 0 = 0 := by
  simp [framedCenter, OrthonormalBasis.repr_self]

theorem repr_framedCenter_ne (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {j : Fin 3}
    (hj : j ≠ 0) :
    (rawPrism W).basis.repr (framedCenter W) j = (rawPrism W).basis.repr (rawPrism W).center j := by
  simp [framedCenter, OrthonormalBasis.repr_self, hj]

theorem repr_sub_framedCenter_zero (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    (rawPrism W).basis.repr (x - framedCenter W) 0 = (rawPrism W).basis.repr x 0 := by
  rw [map_sub]
  simp [repr_framedCenter_zero]

theorem repr_sub_framedCenter_ne (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) {j : Fin 3} (hj : j ≠ 0) :
    (rawPrism W).basis.repr (x - framedCenter W) j
      = (rawPrism W).basis.repr (x - (rawPrism W).center) j := by
  rw [map_sub, map_sub]
  simp [repr_framedCenter_ne W hj]


/-- **The framed plank of a convex body**: the exact `A × B × 1` plank on the frame of the body's
outer prism, centred on the outer-prism centre with the long-axis component deleted so that the
plank stays anchored to the ambient origin in its long direction. -/
def framedPlank (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (A B : ℝ≥0)
    (hAB : A ≤ B) (hB1 : B ≤ 1) : Plank A B hAB hB1 where
  toPrismNDim := PrismNDim.mk' (framedCenter W)
    ((rawPrism W).basis.reindex Fin.revPerm) ![A, B, 1]
  thicknesses_eq := by
    simpa using PrismNDim.thicknesses_mk' (framedCenter W)
      ((rawPrism W).basis.reindex Fin.revPerm) ![A, B, 1]

theorem abs_repr_le_norm (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : |b.repr x i| ≤ ‖x‖ := by
  rw [OrthonormalBasis.repr_apply_apply]
  calc |(inner ℝ (b i) x : ℝ)| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]

/-- **A body inside the unit ball lies in its framed plank**, as soon as the two transverse
half-widths dominate the body's own two smaller thicknesses. -/
theorem le_framedPlank {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {A B : ℝ≥0}
    (hAB : A ≤ B) (hB1 : B ≤ 1)
    (h2 : thicknessNN W 2 ≤ A) (h1 : thicknessNN W 1 ≤ B)
    (hball : (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1) :
    W ≤ (framedPlank W A B hAB hB1).toConvexSpaceBody := by
  intro x hx
  change x ∈ (framedPlank W A B hAB hB1).carrier
  rw [(framedPlank W A B hAB hB1).mem_carrier_iff]
  intro i
  have hraw := abs_repr_rawPrism_le hx
  have hxnorm : ‖x‖ ≤ 1 := by
    have := hball hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this
  change |((rawPrism W).basis.reindex Fin.revPerm).repr (x - framedCenter W) i|
    ≤ ((![A, B, 1] : Fin 3 → ℝ≥0) i : ℝ)
  rw [OrthonormalBasis.repr_reindex]
  fin_cases i
  · show |(rawPrism W).basis.repr (x - framedCenter W) 2| ≤ ((A : ℝ≥0) : ℝ)
    rw [repr_sub_framedCenter_ne W x (by decide)]
    refine (hraw 2).trans ?_
    simpa using (NNReal.coe_le_coe.mpr h2)
  · show |(rawPrism W).basis.repr (x - framedCenter W) 1| ≤ ((B : ℝ≥0) : ℝ)
    rw [repr_sub_framedCenter_ne W x (by decide)]
    refine (hraw 1).trans ?_
    simpa using (NNReal.coe_le_coe.mpr h1)
  · show |(rawPrism W).basis.repr (x - framedCenter W) 0| ≤ (((1 : ℝ≥0)) : ℝ)
    rw [repr_sub_framedCenter_zero W x]
    refine (abs_repr_le_norm _ _ _).trans ?_
    simpa using hxnorm


theorem abs_repr_framedPlank_le {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {A B : ℝ≥0}
    {hAB : A ≤ B} {hB1 : B ≤ 1} {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ ((framedPlank W A B hAB hB1).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    |(rawPrism W).basis.repr (y - framedCenter W) 2| ≤ (A : ℝ) ∧
      |(rawPrism W).basis.repr (y - framedCenter W) 1| ≤ (B : ℝ) ∧
      |(rawPrism W).basis.repr (y - framedCenter W) 0| ≤ (1 : ℝ) := by
  have h := ((framedPlank W A B hAB hB1).mem_carrier_iff y).mp hy
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change |((rawPrism W).basis.reindex Fin.revPerm).repr (y - framedCenter W) 0|
    ≤ ((![A, B, 1] : Fin 3 → ℝ≥0) 0 : ℝ) at h0
  change |((rawPrism W).basis.reindex Fin.revPerm).repr (y - framedCenter W) 1|
    ≤ ((![A, B, 1] : Fin 3 → ℝ≥0) 1 : ℝ) at h1
  change |((rawPrism W).basis.reindex Fin.revPerm).repr (y - framedCenter W) 2|
    ≤ ((![A, B, 1] : Fin 3 → ℝ≥0) 2 : ℝ) at h2
  rw [OrthonormalBasis.repr_reindex] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · simpa using h0
  · simpa using h1
  · simpa using h2


theorem repr_sub_apply (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (x y : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    b.repr (x - y) i = b.repr x i - b.repr y i := by
  rw [map_sub]; rfl

/-- The pure arithmetic behind `Kakeya.framedPlank_subset_closedBall`. -/
private theorem window_arith {y0 y1 y2 u1 u2 A B : ℝ}
    (hy0 : y0 ≤ 1) (hy1 : y1 ≤ 2 * B + u1) (hy2 : y2 ≤ 2 * A + u2)
    (k0 : 0 ≤ y0) (k1 : 0 ≤ y1) (k2 : 0 ≤ y2)
    (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hA1 : A ≤ 1) (hB1 : B ≤ 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hw : u1 ^ 2 + u2 ^ 2 ≤ 1) :
    y0 ^ 2 + y1 ^ 2 + y2 ^ 2 ≤ 16 := by
  have hsum : u1 + u2 ≤ 3 / 2 := by nlinarith [sq_nonneg (u1 - u2)]
  have s0 : y0 ^ 2 ≤ 1 := by nlinarith
  have s1 : y1 ^ 2 ≤ (2 * B + u1) ^ 2 := by nlinarith
  have s2 : y2 ^ 2 ≤ (2 * A + u2) ^ 2 := by nlinarith
  have e1 : (2 * B + u1) ^ 2 ≤ 4 + 4 * u1 + u1 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hB1) hu1]
  have e2 : (2 * A + u2) ^ 2 ≤ 4 + 4 * u2 + u2 ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hA1) hu2]
  linarith

/-- **The framed plank of a body inside the unit ball lies in the Section-6 working window.**

This is the clause `Kakeya.Section6PartBFactorisation.repr_window` asks for, and whose field
docstring calls it underivable.  It *is* derivable once the representative plank is re-centred:
`Kakeya.framedCenter` deletes the long-axis component of the outer-prism centre, which anchors the
plank's long direction to the ambient origin and buys exactly the slack that the naive bound
`‖centre‖ + √(A² + B² + 1) ≤ 1 + 2√3 ≈ 4.46 > 4` misses. -/
theorem framedPlank_subset_closedBall {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {A B : ℝ≥0}
    {hAB : A ≤ B} {hB1 : B ≤ 1}
    (h2 : thicknessNN W 2 ≤ A) (h1 : thicknessNN W 1 ≤ B)
    (hball : (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall 0 1) :
    ((framedPlank W A B hAB hB1).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
  classical
  obtain ⟨w, hw⟩ := W.nonempty'
  have hwnorm : ‖w‖ ≤ 1 := by
    have := hball hw
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this
  have hraw := abs_repr_rawPrism_le hw
  have hA1 : (A : ℝ) ≤ 1 := by exact_mod_cast hAB.trans hB1
  have hB1' : (B : ℝ) ≤ 1 := by exact_mod_cast hB1
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := A.coe_nonneg
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := B.coe_nonneg
  have hτ1 : ((thicknessNN W 1 : ℝ≥0) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h1
  have hτ2 : ((thicknessNN W 2 : ℝ≥0) : ℝ) ≤ (A : ℝ) := by exact_mod_cast h2
  intro y hy
  obtain ⟨e2, e1, e0⟩ := abs_repr_framedPlank_le hy
  set b := (rawPrism W).basis with hb
  set u1 : ℝ := |b.repr w 1| with hu1def
  set u2 : ℝ := |b.repr w 2| with hu2def
  have hu1nn : 0 ≤ u1 := abs_nonneg _
  have hu2nn : 0 ≤ u2 := abs_nonneg _
  -- (1) the two transverse coordinates of the chosen point of `W`
  have hwsum : u1 ^ 2 + u2 ^ 2 ≤ 1 := by
    have hnorm : ‖b.repr w‖ = ‖w‖ := b.repr.norm_map w
    have hexp : ‖b.repr w‖ = √(∑ i : Fin 3, ‖b.repr w i‖ ^ 2) := EuclideanSpace.norm_eq _
    have hnn : (0 : ℝ) ≤ ∑ i : Fin 3, ‖b.repr w i‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : (∑ i : Fin 3, ‖b.repr w i‖ ^ 2) = ‖w‖ ^ 2 := by
      have hEq : √(∑ i : Fin 3, ‖b.repr w i‖ ^ 2) = ‖w‖ := by rw [← hexp, hnorm]
      nlinarith [Real.sq_sqrt hnn, hEq]
    rw [Fin.sum_univ_three] at hsq
    simp only [Real.norm_eq_abs] at hsq
    nlinarith [sq_nonneg |b.repr w 0|, norm_nonneg w]
  -- (2) the centre coordinates
  have hc : ∀ (j : Fin 3) (n : ℕ), j ≠ 0 → (j : ℕ) = n →
      |b.repr (framedCenter W) j| ≤ |b.repr w j| + ((thicknessNN W n : ℝ≥0) : ℝ) := by
    intro j n hj hn
    subst hn
    rw [repr_framedCenter_ne W hj, ← hb]
    have hτ := hraw j
    rw [repr_sub_apply] at hτ
    rw [abs_le] at hτ ⊢
    refine ⟨?_, ?_⟩ <;>
      linarith [hτ.1, hτ.2, le_abs_self (b.repr w j), neg_abs_le (b.repr w j)]
  have hc1 := hc 1 1 (by decide) rfl
  have hc2 := hc 2 2 (by decide) rfl
  -- (3) the coordinates of a point of the plank
  have hy0 : |b.repr y 0| ≤ 1 := by
    have : b.repr y 0 = b.repr (y - framedCenter W) 0 := (repr_sub_framedCenter_zero W y).symm
    rw [this]; exact e0
  have hy1 : |b.repr y 1| ≤ 2 * (B : ℝ) + u1 := by
    have hsplit : b.repr y 1 = b.repr (y - framedCenter W) 1 + b.repr (framedCenter W) 1 := by
      rw [repr_sub_apply]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have := hc1
    rw [← hu1def] at this
    linarith [e1, this, hτ1]
  have hy2 : |b.repr y 2| ≤ 2 * (A : ℝ) + u2 := by
    have hsplit : b.repr y 2 = b.repr (y - framedCenter W) 2 + b.repr (framedCenter W) 2 := by
      rw [repr_sub_apply]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have := hc2
    rw [← hu2def] at this
    linarith [e2, this, hτ2]
  -- (4) assemble
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖y‖ = √(∑ i : Fin 3, ‖b.repr y i‖ ^ 2) := by
    rw [← b.repr.norm_map y, EuclideanSpace.norm_eq]
  have hsum16 : (∑ i : Fin 3, ‖b.repr y i‖ ^ 2) ≤ 16 := by
    rw [Fin.sum_univ_three]
    simp only [Real.norm_eq_abs]
    exact window_arith hy0 hy1 hy2 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      hu1nn hu2nn hA1 hB1' hA0 hB0 hwsum
  have h4 : √(∑ i : Fin 3, ‖b.repr y i‖ ^ 2) ≤ 4 := by
    have : √(∑ i : Fin 3, ‖b.repr y i‖ ^ 2) ≤ √16 := Real.sqrt_le_sqrt hsum16
    calc √(∑ i : Fin 3, ‖b.repr y i‖ ^ 2) ≤ √16 := this
      _ = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  rw [hnorm]
  simpa [plankWindowRadius] using h4



/-! ### The uniform half-widths of the 6.6(B) datum -/

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

/-- **The common thin half-width of a 6.6(B) datum**: the largest rank-`2` thickness of a cell
hull.  This is the re-declared `a` of the repair: it is `≤ a` (`uniformThin_le`) and `≥ ρ`
(`le_uniformThin`), and it is what makes the plank reading of `def:Factors` clause (ii) hold with a
scale-free constant. -/
def uniformThin : ℝ≥0 := Fz.parts.sup (fun t => thicknessNN (cellBody t Rt) 2)

/-- **The common middle half-width of a 6.6(B) datum**: the largest rank-`1` thickness of a cell
hull. -/
def uniformMid : ℝ≥0 := Fz.parts.sup (fun t => thicknessNN (cellBody t Rt) 1)

theorem thicknessNN_two_le_uniformThin {part : Finset κ} (hpart : part ∈ Fz.parts) :
    thicknessNN (cellBody part Rt) 2 ≤ Fz.uniformThin :=
  Finset.le_sup (f := fun t => thicknessNN (cellBody t Rt) 2) hpart

theorem thicknessNN_one_le_uniformMid {part : Finset κ} (hpart : part ∈ Fz.parts) :
    thicknessNN (cellBody part Rt) 1 ≤ Fz.uniformMid :=
  Finset.le_sup (f := fun t => thicknessNN (cellBody t Rt) 1) hpart

theorem uniformThin_le_uniformMid : Fz.uniformThin ≤ Fz.uniformMid := by
  refine Finset.sup_le fun t ht => ?_
  exact le_trans (thicknessNN_antitone (cellBody t Rt) (by norm_num))
    (Fz.thicknessNN_one_le_uniformMid ht)


include Fz in
/-- **A cell hull of a 6.6(B) datum whose coarse tubes lie in the unit ball lies in the unit
ball.**  The cell hull is a convex hull of coarse tubes and the ball is convex. -/
theorem cellBody_subset_closedBall
    (hballs : ∀ k ∈ r, (Rt k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {part : Finset κ} (hpart : part ∈ Fz.parts) :
    ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1 := by
  have hne : part.Nonempty := Fz.nonempty_of_mem_parts hpart
  have hsub : part ⊆ r := Fz.le hpart
  rw [Finset.Nonempty.convexHull_biUnion_carrier hne]
  refine Convexity.convexHull_min ?_ (convex_closedBall _ _).isConvexSet
  refine Set.iUnion₂_subset fun k hk => ?_
  exact hballs k (hsub hk)

include Fz in
/-- Every cell hull of such a datum has circumradius at most `1`. -/
theorem thicknessNN_zero_cellBody_le_one
    (hballs : ∀ k ∈ r, (Rt k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {part : Finset κ} (hpart : part ∈ Fz.parts) :
    thicknessNN (cellBody part Rt) 0 ≤ 1 :=
  thicknessNN_zero_le_of_subset_closedBall (Fz.cellBody_subset_closedBall hballs hpart)

theorem uniformMid_le_one
    (hballs : ∀ k ∈ r, (Rt k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Fz.uniformMid ≤ 1 := by
  refine Finset.sup_le fun t ht => ?_
  exact le_trans (thicknessNN_antitone (cellBody t Rt) (by norm_num))
    (Fz.thicknessNN_zero_cellBody_le_one hballs ht)

include Fz in
/-- **The re-declared thin half-width never exceeds the declared one.**  Hence a conclusion proved
at `Fz.uniformThin` implies the conclusion at `a`, since `(A / B) ^ β` is monotone in `A`. -/
theorem uniformThin_le : Fz.uniformThin ≤ a := by
  refine Finset.sup_le fun t ht => ?_
  refine thicknessNN_le_of_ethickness_le ?_
  exact Fz.ethickness_two_le ht

include Fz in
/-- **The re-declared thin half-width is at least the coarse scale.**  Every cell hull contains a
`ρ`-tube. -/
theorem le_uniformThin (hne : Fz.parts.Nonempty) : ρ ≤ Fz.uniformThin := by
  obtain ⟨t, ht⟩ := hne
  refine le_trans ?_ (Fz.thicknessNN_two_le_uniformThin ht)
  exact le_thicknessNN_of_le_ethickness (Fz.le_ethickness_two ht)

include Fz in
/-- **The declared middle half-width is dominated by the re-declared one, up to the datum's own
reading constant.**  This is where `wide` is spent: it is the only lower bound on the middle
thickness of a cell hull, and it is what keeps the eccentricity `(a / b) ^ β` honest. -/
theorem le_mul_uniformMid (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hne : Fz.parts.Nonempty) :
    b ≤ plankReadingConst Cw C₀ * Fz.uniformMid := by
  obtain ⟨a', -, -, hfam⟩ := Fz.exists_isPlankFamilyOfDimensions hCw hb1' hne
  obtain ⟨t, ht⟩ := hne
  have hlow : ((plankReadingConst Cw C₀ : ℝ≥0) : ENNReal)⁻¹ * (b : ENNReal)
      ≤ Metric.ethickness ℝ (cellBody t Rt).carrier 1 := (hfam t ht).2.1.1
  have hC0 : ((plankReadingConst Cw C₀ : ℝ≥0) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (one_le_plankReadingConst Cw C₀)).ne'
  have hstep : (b : ENNReal)
      ≤ ((plankReadingConst Cw C₀ : ℝ≥0) : ENNReal)
        * ((thicknessNN (cellBody t Rt) 1 : ℝ≥0) : ENNReal) := by
    rw [coe_thicknessNN]
    calc (b : ENNReal)
        = ((plankReadingConst Cw C₀ : ℝ≥0) : ENNReal)
            * (((plankReadingConst Cw C₀ : ℝ≥0) : ENNReal)⁻¹ * (b : ENNReal)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 ENNReal.coe_ne_top, one_mul]
      _ ≤ ((plankReadingConst Cw C₀ : ℝ≥0) : ENNReal)
            * Metric.ethickness ℝ (cellBody t Rt).carrier 1 := by gcongr
  have hnn : b ≤ plankReadingConst Cw C₀ * thicknessNN (cellBody t Rt) 1 := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
    exact hstep
  exact hnn.trans (by gcongr; exact Fz.thicknessNN_one_le_uniformMid ht)


/-! ### The cell map of the underlying `Finpartition` -/

open Classical in
/-- The cell of a coarse index: the part of the factorisation's `Finpartition` containing it (and
`∅` off the coarse family, so that the map is total, as the Part-(B) interface demands). -/
def cellOf (k : κ) : Finset κ := if h : ∃ t ∈ Fz.parts, k ∈ t then h.choose else ∅

theorem cellOf_spec {k : κ} (hk : k ∈ r) : Fz.cellOf k ∈ Fz.parts ∧ k ∈ Fz.cellOf k := by
  classical
  have h : ∃ t ∈ Fz.parts, k ∈ t := Fz.exists_mem hk
  rw [cellOf, dif_pos h]
  exact ⟨h.choose_spec.1, h.choose_spec.2⟩

theorem cellOf_eq {k : κ} (hk : k ∈ r) {t : Finset κ} (ht : t ∈ Fz.parts) (hkt : k ∈ t) :
    Fz.cellOf k = t :=
  Fz.eq_of_mem_parts (Fz.cellOf_spec hk).1 ht (Fz.cellOf_spec hk).2 hkt

/-- **The coarse fibre of a cell is the part itself.**  This is what lets the plank reading of
`def:Factors` clause (ii), proved for the parts of the `Finpartition`, be handed verbatim to the
`coarse_fibre_frostman` field of `Kakeya.Section6PartBFactorisation`, whose fibre is a filter. -/
theorem filter_cellOf_eq {t : Finset κ} (ht : t ∈ Fz.parts)
    [inst : DecidablePred (fun k => Fz.cellOf k = t)] :
    Finset.filter (fun k => Fz.cellOf k = t) r = t := by
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hk, hkt⟩
    rw [← hkt]
    exact (Fz.cellOf_spec hk).2
  · intro hkt
    have hk : k ∈ r := Fz.le ht hkt
    exact ⟨hk, Fz.cellOf_eq hk ht hkt⟩


include Fz in
/-- **The re-declaration does not lose the eccentricity.**

`A * b ≤ K * (a * B)` with `A = Fz.uniformThin`, `B = Fz.uniformMid` and
`K = Kakeya.plankReadingConst Cw C₀`: the conclusion of GWZ 6.6(B) proved at the re-declared pair
`(A, B)` weakens back to the declared pair `(a, b)` at the cost of `K ^ β`, which the budget
`Cw, C₀ ≤ δ ^ (-η)` absorbs into `δ ^ (-ε)`.

This is the clause that closes the hole exhibited by the `ρ = δ`, hulls `δ × 1 × 1`, declared
`a = 1 / 2`, `b = 1` configuration: there `A = τ₂(hull) ≍ δ ≪ a`, and it is `A`, not `a`, that the
inner normalisation may use. -/
theorem uniformThin_mul_le (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hne : Fz.parts.Nonempty) :
    Fz.uniformThin * b ≤ plankReadingConst Cw C₀ * (a * Fz.uniformMid) := by
  calc Fz.uniformThin * b ≤ a * (plankReadingConst Cw C₀ * Fz.uniformMid) :=
        mul_le_mul' Fz.uniformThin_le (Fz.le_mul_uniformMid hCw hb1' hne)
    _ = plankReadingConst Cw C₀ * (a * Fz.uniformMid) := by ring

include Fz in
/-- **The inner-scale threshold, at the re-declared thin half-width.**

The Part-(B) pipeline's inner application of GWZ Lemma 6.1 needs `δ ≤ s₀ * A` where `A` is the
thin half-width the normalisation actually uses.  After the re-declaration that is
`Fz.uniformThin`, **not** the declared `a`; and since every cell hull contains a `ρ`-tube
(`Kakeya.GlobalPlankFactorization.le_uniformThin`), the threshold is implied by the *coarse*-scale
condition `δ ≤ s₀ * ρ`.

Consequences, both recorded rather than assumed:

* the genuinely open regime of GWZ 6.6(B) is `δ > s₀ * ρ` **together with**
  `Fz.uniformThin ≍ δ` — i.e. `ρ ≍ δ` *and* every cell hull `δ`-thin — not the whole of
  `δ > s₀ * a`.  At the declared `a` the condition can fail while the argument still runs, which is
  exactly source 2's configuration (`ρ = δ`, hulls `δ × 1 × 1`, declared `a = 1 / 2`);
* Section 9, the sole consumer, runs 6.6(B) at `ρ = δ ^ (1 - ε₂)`, so `δ / ρ = δ ^ ε₂ → 0` and the
  hypothesis below is satisfied for every `s₀ > 0` once `δ` is small; the open regime never arises
  there. -/
theorem le_mul_uniformThin_of_le_mul_rho {s₀ δ : ℝ≥0} (hne : Fz.parts.Nonempty)
    (h : δ ≤ s₀ * ρ) : δ ≤ s₀ * Fz.uniformThin :=
  h.trans (by gcongr; exact Fz.le_uniformThin hne)

end GlobalPlankFactorization

/-! ### The bridge -/

section Bridge

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

namespace GlobalPlankFactorization

/-- The Frostman constant of the produced Part-(B) factorisation: the plank-reading constant of
`Kakeya.GlobalPlankFactorization.coarseFibreFrostmanConst`, clipped to be at least `1`.  It is a
fixed polynomial in `Cw` and `C₀` and sees none of the scales `δ, ρ, a, b`. -/
def partBFrostmanConst (Cw C₀ : ℝ≥0) : ℝ≥0 := max 1 (coarseFibreFrostmanConst Cw C₀)

theorem one_le_partBFrostmanConst (Cw C₀ : ℝ≥0) : 1 ≤ partBFrostmanConst Cw C₀ := le_max_left _ _

include Fz in
theorem uniformThin_le_mul (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hne : Fz.parts.Nonempty)
    {a' : ℝ≥0}
    (hfam : IsPlankFamilyOfDimensions (plankReadingConst Cw C₀) a' b Fz.parts
      (fun part => cellBody part Rt)) :
    Fz.uniformThin ≤ plankReadingConst Cw C₀ * a' := by
  refine Finset.sup_le fun t ht => ?_
  refine thicknessNN_le_of_ethickness_le ?_
  rw [ENNReal.coe_mul]
  exact (hfam t ht).2.2.2

include Fz in
theorem uniformMid_le_mul {a' : ℝ≥0}
    (hfam : IsPlankFamilyOfDimensions (plankReadingConst Cw C₀) a' b Fz.parts
      (fun part => cellBody part Rt)) :
    Fz.uniformMid ≤ plankReadingConst Cw C₀ * b := by
  refine Finset.sup_le fun t ht => ?_
  refine thicknessNN_le_of_ethickness_le ?_
  rw [ENNReal.coe_mul]
  exact (hfam t ht).2.1.2

end GlobalPlankFactorization

end Bridge

/-! The constructor itself needs `κ : Type`: its cell type is `Finset κ`, and
`Kakeya.Section6PartBFactorisation.Cell` lives in `Type`.  The lemmas above are universe-polymorphic
and are consumed at an arbitrary universe by
`Kakeya/DimensionThree/Plank/Section6PartBDataBridgeUniv.lean`. -/

section BridgeType

variable {κ : Type} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

namespace GlobalPlankFactorization

/-- **The GWZ 6.6(B) datum yields the tree's Part-(B) factorisation datum, at the re-declared
half-widths.**

Every field is discharged:

* `repr` is the framed plank of the cell hull at the *uniform* half-widths
  `(Fz.uniformThin, Fz.uniformMid)` — the re-declaration that source 2's configuration forces;
* `repr_window` is `Kakeya.framedPlank_subset_closedBall`, so the containment the field's docstring
  calls underivable is derived here;
* `coarse_fibre_frostman` is `def:Factors` clause (ii) in GWZ's own plank reading, obtained from the
  tree's hull reading through the volume comparison that `wide` supplies, with the scale-free
  constant `Kakeya.GlobalPlankFactorization.partBFrostmanConst`;
* `isKatzTao` is the datum's own Katz--Tao clause, unchanged.

The bookkeeping needed to weaken back to the *declared* `(a, b)` is
`Kakeya.GlobalPlankFactorization.uniformThin_le` (`A ≤ a`) and
`Kakeya.GlobalPlankFactorization.le_mul_uniformMid` (`b ≤ K * B`), so
`A / B ≤ K * (a / b)` with `K = Kakeya.plankReadingConst Cw C₀ ≤ max 3 (max (2 Cw) C₀)`,
sub-polynomial under the 6.6(B) budget `Cw, C₀ ≤ δ ^ (-η)`. -/
def toSection6PartBFactorisation (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b) (hρ : 0 < ρ)
    (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Section6PartBFactorisation Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one hballs) r Rt (partBFrostmanConst Cw C₀) C₀ where
  Cell := Finset κ
  cells := Fz.parts
  body := fun t => cellBody t Rt
  cellOf := Fz.cellOf
  cellOf_mem := fun k hk => (Fz.cellOf_spec hk).1
  le_body := fun k hk =>
    Finset.le_convexHull_biUnion (fun j => (Rt j).toConvexSpaceBody) (Fz.cellOf_spec hk).2
  repr := fun t => framedPlank (cellBody t Rt) Fz.uniformThin Fz.uniformMid
    Fz.uniformThin_le_uniformMid (Fz.uniformMid_le_one hballs)
  body_le_repr := fun t ht =>
    le_framedPlank _ _ (Fz.thicknessNN_two_le_uniformThin ht)
      (Fz.thicknessNN_one_le_uniformMid ht) (Fz.cellBody_subset_closedBall hballs ht)
  repr_window := fun t ht =>
    framedPlank_subset_closedBall (Fz.thicknessNN_two_le_uniformThin ht)
      (Fz.thicknessNN_one_le_uniformMid ht) (Fz.cellBody_subset_closedBall hballs ht)
  one_le_CF := one_le_partBFrostmanConst Cw C₀
  coarse_fibre_frostman := by
    classical
    intro x hx
    obtain ⟨a', hρa', ha'a, hfam⟩ := Fz.exists_isPlankFamilyOfDimensions hCw hb1' hne
    have ha'0 : 0 < a' := lt_of_lt_of_le hρ hρa'
    have hK1 : (1 : ℝ≥0) ≤ plankReadingConst Cw C₀ := one_le_plankReadingConst Cw C₀
    have hthin := Fz.uniformThin_le_mul hCw hb1' hne hfam
    have hmid := Fz.uniformMid_le_mul hfam
    have hcmp : Fz.uniformThin * Fz.uniformMid
        ≤ plankReadingConst Cw C₀ ^ 2 * (a' * b) := by
      calc Fz.uniformThin * Fz.uniformMid
          ≤ (plankReadingConst Cw C₀ * a') * (plankReadingConst Cw C₀ * b) :=
            mul_le_mul' hthin hmid
        _ = plankReadingConst Cw C₀ ^ 2 * (a' * b) := by ring
    have hFr := Fz.isFrostmanIn_plank_of_isPlankOfDimensions hx hK1 ha'0 hb0 (hfam x hx)
      (framedPlank (cellBody x Rt) Fz.uniformThin Fz.uniformMid
        Fz.uniformThin_le_uniformMid (Fz.uniformMid_le_one hballs))
      (le_framedPlank _ _ (Fz.thicknessNN_two_le_uniformThin hx)
        (Fz.thicknessNN_one_le_uniformMid hx) (Fz.cellBody_subset_closedBall hballs hx))
      hcmp
    have hcoe : (C₀ : ENNReal)
        * ((plankFrostmanLoss (plankReadingConst Cw C₀) * plankReadingConst Cw C₀ ^ 2 : ℝ≥0)
            : ENNReal)
        ≤ ((partBFrostmanConst Cw C₀ : ℝ≥0) : ENNReal) := by
      rw [← ENNReal.coe_mul]
      exact_mod_cast le_max_right (1 : ℝ≥0) (coarseFibreFrostmanConst Cw C₀)
    have hmono := hFr.mono hcoe
    convert hmono using 2
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hk, hkt⟩
      rw [← hkt]
      exact (Fz.cellOf_spec hk).2
    · intro hkt
      exact ⟨Fz.le hx hkt, Fz.cellOf_eq (Fz.le hx hkt) hx hkt⟩
  isKatzTao := Fz.isKatzTao

end GlobalPlankFactorization

end BridgeType

end Kakeya

end

end
