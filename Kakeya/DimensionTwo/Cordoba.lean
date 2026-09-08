/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.Shading
public import Kakeya.Thickness.Volume
public import Kakeya.Thickness.Diam
public import Kakeya.Thickness.Lemmas
public import Kakeya.Mathlib.MeasureTheory.CauchySchwarz
public import Kakeya.Mathlib.Analysis.InnerProductSpace
public import Kakeya.DimensionN.Prism
public import Kakeya.DimensionTwo.PlanarAngle
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The planar Cordoba `L²` estimate (GWZ Lemma 5.9, planar core)

This file formalises the two-dimensional heart of the blueprint section
"The planar Cordoba estimate" (`section5_cordoba.tex`): the key geometric fact that
overlapping prisms lie in a common fattening (`subset_resize_of_le_volume_inter`) and
the planar Cordoba `L²` estimate built on it
(`ConvexSpaceBody.IsFrostmanIn.le_volume_biUnion`).

The blueprint uses the informal asymptotic notation `≳` (bounded below up to an
absolute constant) and `∼` (comparable up to absolute constants).  We render
`A ≳ B` as `∃ c : ℝ≥0, 0 < c ∧ (c : ℝ≥0∞) * B ≤ A`, the standard faithful
encoding of "bounded below by an absolute constant times".  The geometric facts
about overlapping prisms are stated on the project's prism types (`PrismNDim`).
The Cordoba estimate itself is phrased on a family of shaded convex bodies
(`ShadedBody`), with the common-dimensions hypothesis rendered as pairwise
comparability of affine thicknesses up to a factor `2`.  The Frostman hypothesis
and the union `U(V)` reuse `ConvexSpaceBody.IsFrostmanIn` and
`⋃ i ∈ s, (V i).shade` respectively.
-/

@[expose] public section

open MeasureTheory Metric Module
open scoped NNReal ENNReal EuclideanSpace

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

instance : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_two

instance : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 2)

/-! ### The key geometric fact (blueprint `lem:overlapInSlab`)

The Cauchy–Schwarz union lower bound (blueprint `lem:unionLowerBoundCS`) is already
available in the repository as `MeasureTheory.sq_sum_volume_le`
(`Kakeya/Mathlib/MeasureTheory/CauchySchwarz.lean`), so it is reused directly.  The
non-parallelism of the two short axes is measured by the signed area
`o.areaForm` (Mathlib's `Orientation.areaForm`); the inner-product transversality
bound `Orientation.norm_mul_abs_areaForm_le` lives in
`Kakeya/Mathlib/Analysis/InnerProductSpace.lean`. -/

/-- **Rank-`0` thickness of the intersection** (blueprint `lem:thickness0InterDet`).

For two planar prisms `Q`, `Q'` whose thicknesses are comparable up to a factor `2`
(`Q'.thicknesses ≤ 2 • Q.thicknesses`), the rank-`0` affine thickness of `Q ∩ Q'` is controlled by
the short half-width `Q.thicknesses 1` (index `1`, the smaller axis in the decreasing-thickness
`outerPrism` convention) divided by their `planarAngle`.  Stated multiplicatively (so the parallel
case `planarAngle = 0` is harmless):
`τ₀(Q ∩ Q') · planarAngle Q Q' ≲ Q.thicknesses 1`.

This is the geometric content of `Orientation.norm_mul_abs_areaForm_le`: any two points of `Q ∩ Q'`
differ by a vector `w` with `|⟪w, Q.basis 1⟫| ≤ 2 (Q.thicknesses 1)` and
`|⟪w, Q'.basis 1⟫| ≤ 2 (Q'.thicknesses 1) ≤ 4 (Q.thicknesses 1)`, so the area bound gives the
constant `2 (Q.thicknesses 1) + 2 (Q'.thicknesses 1) ≤ 6 (Q.thicknesses 1)`.  The `planarAngle`
phrasing is orientation-free; internally we pick the orientation induced by `Q.basis`. -/
theorem thickness_zero_inter_mul_planarAngle_le
    (Q Q' : PrismNDim 2 E E)
    (hcomp : Q'.thicknesses ≤ 2 • Q.thicknesses) :
    Metric.thickness ℝ (Q.carrier ∩ Q'.carrier) 0 * Q.planarAngle Q'
      ≤ 6 * (Q.thicknesses 1 : ℝ) := by
  set o : Orientation ℝ E (Fin 2) := Q.basis.toBasis.orientation with ho
  rw [PrismNDim.planarAngle_eq_abs_areaForm o Q Q' 1]
  have hc1 : (Q'.thicknesses 1 : ℝ) ≤ 2 * (Q.thicknesses 1 : ℝ) := by
    have h := hcomp 1
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact_mod_cast h
  let s : ℝ := abs <| o.areaForm (Q.basis 1) (Q'.basis 1)
  have hs_nonneg : 0 ≤ s := abs_nonneg _
  set inter := Q.carrier ∩ Q'.carrier
  refine (mul_le_mul_of_nonneg_right (thickness_zero_le_diam ?_) hs_nonneg).trans ?_
  · exact (Q.isCompact'.inter Q'.isCompact').isBounded
  -- Pointwise bound: for any x,y ∈ inter, dist x y * s ≤ 6 * (Q.thicknesses 1)
  suffices ∀ x ∈ inter, ∀ y ∈ inter, dist x y * s ≤ 6 * (Q.thicknesses 1 : ℝ) by
    by_cases hs : s = 0
    · simp [hs]
    · replace hs : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs)
      apply mul_diam_le_of_forall_mul_dist_le hs
      · positivity
      exact this
  intro x hx y hy
  rw [dist_comm, dist_eq_norm_vsub]
  rcases hx with ⟨hxQ, hxQ'⟩
  rcases hy with ⟨hyQ, hyQ'⟩
  have hwQ : |inner ℝ (y -ᵥ x) (Q.basis 1)| ≤ 2 * (Q.thicknesses 1 : ℝ) :=
    PrismNDim.abs_inner_vsub_basis_le Q hxQ hyQ 1
  have hwQ' : |inner ℝ (y -ᵥ x) (Q'.basis 1)| ≤ 2 * (Q'.thicknesses 1 : ℝ) :=
    PrismNDim.abs_inner_vsub_basis_le Q' hxQ' hyQ' 1
  have hnorm : ‖Q.basis 1‖ = 1 := Q.basis.norm_eq_one 1
  have hnorm' : ‖Q'.basis 1‖ = 1 := Q'.basis.norm_eq_one 1
  have h_mul := o.norm_mul_abs_areaForm_le hnorm hnorm' hwQ hwQ'
  calc ‖y -ᵥ x‖ * s
      ≤ 2 * (Q.thicknesses 1 : ℝ) + 2 * (Q'.thicknesses 1 : ℝ) := h_mul
    _ ≤ 6 * (Q.thicknesses 1 : ℝ) := by linarith

variable
  [MeasurableSpace E] [BorelSpace E]


/-- **Non-parallel prisms meet in small area** (blueprint `lem:overlapVolumeDet`).

Two planar prisms `Q`, `Q'` of comparable thicknesses (`Q'.thicknesses ≤ 2 • Q.thicknesses`) cross
in a parallelogram of area `≲ (Q.thicknesses 1)² / planarAngle Q Q'`, where `Q.thicknesses 1` is the
short half-width (index `1`, the smaller axis in the decreasing-thickness `outerPrism` convention).
Stated multiplicatively to avoid `ℝ≥0∞` division (so the parallel case `planarAngle = 0` is
harmless): `planarAngle Q Q' · |Q ∩ Q'| ≤ 24 (Q.thicknesses 1)²`.  The more transverse the prisms
(the larger the angle), the smaller their intersection.

Proof outline: bound `|Q ∩ Q'|` by the product of its rank-`0` and rank-`1` ethicknesses
(`volume_le_prod_ethickness`, giving the factor `4`); the rank-`1` thickness is `≤ Q.thicknesses 1`
(`Q ∩ Q' ⊆ Q`, `thickness_carrier_le`), and the rank-`0` thickness times `planarAngle` is
`≤ 6 (Q.thicknesses 1)` (`thickness_zero_inter_mul_planarAngle_le`), whence the constant
`4 · 6 = 24`. -/
theorem volume_inter_le_of_planarAngle
    (Q Q' : PrismNDim 2 E E)
    (hcomp : Q'.thicknesses ≤ 2 • Q.thicknesses) :
    ENNReal.ofReal (Q.planarAngle Q') * volume (Q.carrier ∩ Q'.carrier)
      ≤ (24 * Q.thicknesses 1 ^ 2 : ℝ≥0) := by
  set t := Q.carrier ∩ Q'.carrier with ht
  set a : ℝ := Q.planarAngle Q' with ha
  have hbdd : Bornology.IsBounded t := (Q.isCompact'.inter Q'.isCompact').isBounded
  have ha_nonneg : 0 ≤ a := abs_nonneg _
  -- Volume bounded by `4` times the product of the rank-`0` and rank-`1` ethicknesses.
  have hvol : volume t
      ≤ 4 * (ENNReal.ofReal (thickness ℝ t 0) * ENNReal.ofReal (thickness ℝ t 1)) := by
    have hfr : Module.finrank ℝ E = 2 := Fact.out
    calc volume t
        ≤ 2 ^ Module.finrank ℝ E
            * ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ t i :=
          volume_le_prod_ethickness t
      _ = 4 * (ENNReal.ofReal (thickness ℝ t 0) * ENNReal.ofReal (thickness ℝ t 1)) := by
          rw [hfr]
          simp only [Finset.prod_range_succ, ethickness_thickness' (𝕜 := ℝ) hbdd]
          norm_num
  -- The rank-`1` thickness of the intersection is at most the short half-width.
  have hth1 : thickness ℝ t 1 ≤ (Q.thicknesses 1 : ℝ) := by
    have hmono := Metric.thickness_monotone (𝕜 := ℝ) Q.isCompact'.isBounded
      (Set.inter_subset_left : t ⊆ Q.carrier)
    exact (hmono 1).trans (by simpa using Q.thickness_carrier_le (1 : Fin 2))
  -- The rank-`0` thickness times the planar angle (the lemma proved above).
  have hth0 : a * thickness ℝ t 0 ≤ 6 * (Q.thicknesses 1 : ℝ) := by
    rw [mul_comm]; exact thickness_zero_inter_mul_planarAngle_le Q Q' hcomp
  calc ENNReal.ofReal a * volume t
      ≤ ENNReal.ofReal a
          * (4 * (ENNReal.ofReal (thickness ℝ t 0) * ENNReal.ofReal (thickness ℝ t 1))) := by
        gcongr
    _ = 4 * (ENNReal.ofReal (a * thickness ℝ t 0) * ENNReal.ofReal (thickness ℝ t 1)) := by
        rw [ENNReal.ofReal_mul ha_nonneg]; ring
    _ ≤ 4 * (ENNReal.ofReal (6 * (Q.thicknesses 1 : ℝ))
          * ENNReal.ofReal (Q.thicknesses 1 : ℝ)) := by
        gcongr
    _ = (24 * Q.thicknesses 1 ^ 2 : ℝ≥0) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
        simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
        push_cast
        ring

/-- **Overlapping prisms are nearly parallel** (transversality half of blueprint
`lem:overlapInSlab`).

For two planar prisms `Q`, `Q'` of comparable thicknesses (`Q'.thicknesses ≤ 2 • Q.thicknesses`),
with `Q` of decreasing half-widths (`Q.thicknesses 1 ≤ Q.thicknesses 0`, the `outerPrism`
convention), whose carriers overlap in at least a `θ`-proportion of `|Q|`, the two prisms are nearly
parallel: their `planarAngle` is small,
`planarAngle Q Q' ≲ (Q.thicknesses 1) / (θ · Q.thicknesses 0)`.  This follows from
`volume_inter_le_of_planarAngle` together with the overlap hypothesis and `|Q| = 4 q₁ q₂` (here
`q₁ = Q.thicknesses 1` is the short and `q₂ = Q.thicknesses 0` the long half-width). -/
theorem planarAngle_le_of_le_volume_inter
    (Q Q' : PrismNDim 2 E E)
    (hmono : Q.thicknesses 1 ≤ Q.thicknesses 0) (hq : 0 < Q.thicknesses 1)
    (hcomp : Q'.thicknesses ≤ 2 • Q.thicknesses)
    {θ : ℝ} (hθ₀ : 0 < θ)
    (hover : ENNReal.ofReal θ * volume Q.carrier ≤ volume (Q.carrier ∩ Q'.carrier)) :
    Q.planarAngle Q'
      ≤ 6 * ((Q.thicknesses 1 : ℝ) / (θ * (Q.thicknesses 0 : ℝ))) := by
  have hp : 0 ≤ Q.planarAngle Q' := abs_nonneg _
  have hq1 : (0 : ℝ) < (Q.thicknesses 1 : ℝ) := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (Q.thicknesses 0 : ℝ) := by exact_mod_cast hq.trans_le hmono
  -- The exact prism volume `|Q| = 4 q₂ q₁`.
  have hVQ : volume Q.carrier
      = ENNReal.ofReal (4 * ((Q.thicknesses 0 : ℝ) * (Q.thicknesses 1 : ℝ))) := by
    rw [Q.volume_carrier, show Module.finrank ℝ E = 2 from Fact.out, Fin.prod_univ_two,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4), ENNReal.ofReal_mul hq2.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    norm_num
  -- Chain the area bound with the overlap hypothesis in `ℝ≥0∞`.
  have hkey : ENNReal.ofReal (Q.planarAngle Q') * (ENNReal.ofReal θ * volume Q.carrier)
      ≤ (24 * Q.thicknesses 1 ^ 2 : ℝ≥0) :=
    calc ENNReal.ofReal (Q.planarAngle Q') * (ENNReal.ofReal θ * volume Q.carrier)
        ≤ ENNReal.ofReal (Q.planarAngle Q') * volume (Q.carrier ∩ Q'.carrier) := by gcongr
      _ ≤ (24 * Q.thicknesses 1 ^ 2 : ℝ≥0) := volume_inter_le_of_planarAngle Q Q' hcomp
  -- Transfer to `ℝ`.
  have hRHS : ((24 * Q.thicknesses 1 ^ 2 : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (24 * (Q.thicknesses 1 : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal]; congr 1
  rw [hVQ, ← ENNReal.ofReal_mul hθ₀.le, ← ENNReal.ofReal_mul hp, hRHS,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hkey
  -- Divide the real inequality `p · θ · 4 q₂ q₁ ≤ 24 q₁²` by `4 q₁`.
  rw [← mul_div_assoc, le_div_iff₀ (by positivity : (0 : ℝ) < θ * (Q.thicknesses 0 : ℝ))]
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 4 * (Q.thicknesses 1 : ℝ))
  linear_combination hkey

private lemma fin2_sum_eq {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) (i : Fin 2) :
    ∑ j, f j = f i + f i.rev := by  -- (extracted by Fuse golfer)
  fin_cases i
  · exact Fin.sum_univ_two f
  · rw [Fin.sum_univ_two]; exact add_comm _ _

omit [Fact (finrank ℝ E = 2)] [MeasurableSpace E] [BorelSpace E] in
/-- For overlapping planar prisms sharing a point `p`, the `i`-th `Q`-coordinate of any `x ∈ Q'` is
bounded by `Q.thicknesses i + 2 Q'.thicknesses i + 2 Q'.thicknesses i.rev · planarAngle`; the cross
term carries the planar angle on the *other* (`i.rev`) axis.  Generic in `i`, this is the shared
core of both axis cases of `subset_resize_of_inter_nonempty`. -/
private lemma abs_repr_vsub_center_le {Q Q' : PrismNDim 2 E E} {p x : E}
    (hpQ : p ∈ Q.carrier) (hpQ' : p ∈ Q'.carrier) (hx : x ∈ Q'.carrier) (i : Fin 2) :
    |Q.basis.repr (x -ᵥ Q.center) i|
      ≤ (Q.thicknesses i : ℝ) + 2 * Q'.thicknesses i
        + 2 * Q'.thicknesses i.rev * Q.planarAngle Q' := by  -- (extracted by Fuse golfer)
  have e : Q.basis.repr (x -ᵥ Q.center) i
      = Q.basis.repr (x -ᵥ p) i + Q.basis.repr (p -ᵥ Q.center) i := by
    rw [← vsub_add_vsub_cancel x p Q.center, map_add, PiLp.add_apply]
  have hpc : |Q.basis.repr (p -ᵥ Q.center) i| ≤ (Q.thicknesses i : ℝ) :=
    (Q.mem_carrier_iff p).1 hpQ i
  have hri : |inner ℝ (Q'.basis i) (x -ᵥ p)| ≤ 2 * (Q'.thicknesses i : ℝ) := by
    rw [real_inner_comm]; exact PrismNDim.abs_inner_vsub_basis_le Q' hpQ' hx i
  have hrirev : |inner ℝ (Q'.basis i.rev) (x -ᵥ p)| ≤ 2 * (Q'.thicknesses i.rev : ℝ) := by
    rw [real_inner_comm]; exact PrismNDim.abs_inner_vsub_basis_le Q' hpQ' hx i.rev
  have hb : |inner ℝ (Q.basis i) (Q'.basis i)| ≤ 1 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [Q.basis.norm_eq_one, Q'.basis.norm_eq_one]; norm_num
  have hd : |inner ℝ (Q.basis i) (Q'.basis i.rev)| ≤ Q.planarAngle Q' :=
    le_of_eq (Q.planarAngle_eq_abs_inner Q' i).symm
  have hxp : |Q.basis.repr (x -ᵥ p) i|
      ≤ 2 * (Q'.thicknesses i : ℝ) + 2 * (Q'.thicknesses i.rev : ℝ) * Q.planarAngle Q' := by
    rw [Q.basis.repr_apply_apply, ← Q'.basis.sum_repr (x -ᵥ p), inner_sum, fin2_sum_eq _ i,
      real_inner_smul_right, real_inner_smul_right, Q'.basis.repr_apply_apply,
      Q'.basis.repr_apply_apply]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |inner ℝ (Q'.basis i) (x -ᵥ p)| * |inner ℝ (Q.basis i) (Q'.basis i)|
        ≤ 2 * (Q'.thicknesses i : ℝ) :=
      (mul_le_mul hri hb (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    have h2 : |inner ℝ (Q'.basis i.rev) (x -ᵥ p)| * |inner ℝ (Q.basis i) (Q'.basis i.rev)|
        ≤ 2 * (Q'.thicknesses i.rev : ℝ) * Q.planarAngle Q' :=
      mul_le_mul hrirev hd (abs_nonneg _) (by positivity)
    linarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  linarith

omit [Fact (finrank ℝ E = 2)] [MeasurableSpace E] [BorelSpace E] in
/-- **Overlapping prism sits in a resize of `Q`** (blueprint `lem:overlapContainment`).

If two planar prisms `Q`, `Q'` have a common point, then `Q'` is contained in the resize of `Q`
(same centre and axes) whose `i`-th half-width is
`Q.thicknesses i + 2 (Q'.thicknesses i) + 2 (Q'.thicknesses i.rev) · planarAngle`.  Any overlapping
`Q'`, whatever its orientation, thus lies in a box about `Q`'s centre aligned with `Q`'s axes; the
fattening along axis `i` grows with the planar angle.  Proof: for `x ∈ Q'` expand `x -ᵥ Q.center`
through a common point and the orthonormal frame of `Q'`; the cross inner products are `≤ 1`
(parallel axes) or equal to `planarAngle` (`planarAngle_eq_abs_inner`). -/
theorem subset_resize_of_inter_nonempty
    {Q Q' : PrismNDim 2 E E}
    (hne : (Q.carrier ∩ Q'.carrier).Nonempty) :
    Q'.carrier ⊆ (Q.resize
      ![Q.thicknesses 0 + 2 * Q'.thicknesses 0 + 2 * Q'.thicknesses 1 * (Q.planarAngle Q').toNNReal,
        Q.thicknesses 1 + 2 * Q'.thicknesses 1
          + 2 * Q'.thicknesses 0 * (Q.planarAngle Q').toNNReal]).carrier := by
  obtain ⟨p, hpQ, hpQ'⟩ := hne
  have hsnn : ((Q.planarAngle Q').toNNReal : ℝ) = Q.planarAngle Q' :=
    Real.coe_toNNReal _ (abs_nonneg _)
  intro x hx
  rw [PrismNDim.mem_resize_carrier]
  intro i
  fin_cases i
  · -- axis `0` (long): the cross term carries the planar angle on `Q'.thicknesses 1`
    refine (abs_repr_vsub_center_le hpQ hpQ' hx 0).trans (le_of_eq ?_)
    rw [show (0 : Fin 2).rev = 1 from rfl]
    push_cast [hsnn]; ring
  · -- axis `1` (short): the cross term carries the planar angle on `Q'.thicknesses 0`
    refine (abs_repr_vsub_center_le hpQ hpQ' hx 1).trans (le_of_eq ?_)
    rw [show (1 : Fin 2).rev = 0 from rfl]
    push_cast [hsnn]; ring

/-- **Overlapping prisms lie in a common fattening** (blueprint `lem:overlapInSlab`).

For `Q` of decreasing half-widths (`Q.thicknesses 1 ≤ Q.thicknesses 0`, short index `1`) and a
threshold `θ`, there is a *single* resize `R_θ(Q)` of `Q` — same centre and axes, half-widths
`10 q₂` (long) and `5 q₁ + 24 θ⁻¹ q₁` (short), depending only on `Q` and `θ` — that contains every
comparable `Q'` (`Q'.thicknesses ≤ 2 • Q.thicknesses`) whose carrier overlaps `Q` in at least a
`θ`-proportion of `|Q|`.  Its short half-width is `∼ θ⁻¹ q₁` and its long one `∼ q₂`, so
`|R_θ(Q)| ∼ θ⁻¹ |Q|`.  Obtained from `subset_resize_of_inter_nonempty`: along the short axis the
cross term carries the long thickness, so it needs the planar-angle bound
(`planarAngle_le_of_le_volume_inter`); along the long axis the cross term carries only the short
thickness, so the trivial bound `planarAngle ≤ 1` (`planarAngle_le_one`) already gives `10 q₂`,
avoiding the `θ⁻¹` blow-up when `θ` is small. -/
theorem subset_resize_of_le_volume_inter
    {Q Q' : PrismNDim 2 E E}
    (hmono : Q.thicknesses 1 ≤ Q.thicknesses 0) (hq : 0 < Q.thicknesses 1)
    (hcomp : Q'.thicknesses ≤ 2 • Q.thicknesses)
    {θ : ℝ≥0} (hθ₀ : 0 < θ)
    (hover : (θ : ℝ≥0∞) * volume Q.carrier ≤ volume (Q.carrier ∩ Q'.carrier)) :
    Q'.carrier ⊆ (Q.resize ![10 * Q.thicknesses 0,
      5 * Q.thicknesses 1 + 24 * θ⁻¹ * Q.thicknesses 1]).carrier := by
  have hq2 : (0 : ℝ) < (Q.thicknesses 0 : ℝ) := by exact_mod_cast hq.trans_le hmono
  have hθr : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ₀
  have hmr : (Q.thicknesses 1 : ℝ) ≤ (Q.thicknesses 0 : ℝ) := by exact_mod_cast hmono
  -- comparability of thicknesses, transported to `ℝ`
  have hc : ∀ i, (Q'.thicknesses i : ℝ) ≤ 2 * (Q.thicknesses i : ℝ) := by
    intro i
    have h := hcomp i
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact_mod_cast h
  -- the planar angle, as a real number, and its two bounds
  have hsr : ((Q.planarAngle Q').toNNReal : ℝ) = Q.planarAngle Q' :=
    Real.coe_toNNReal _ (Q.planarAngle_nonneg Q')
  have hsθ : Q.planarAngle Q'
      ≤ 6 * ((Q.thicknesses 1 : ℝ) / ((θ : ℝ) * (Q.thicknesses 0 : ℝ))) :=
    planarAngle_le_of_le_volume_inter Q Q' hmono hq hcomp hθr
      (by rwa [ENNReal.ofReal_coe_nnreal])
  -- the prism has positive volume, so the overlap forces a common point
  have hVne : volume Q.carrier ≠ 0 := by
    rw [Q.volume_carrier, show Module.finrank ℝ E = 2 from Fact.out, Fin.prod_univ_two]
    exact mul_ne_zero (by norm_num) (mul_ne_zero
      (ENNReal.coe_ne_zero.2 (hq.trans_le hmono).ne') (ENNReal.coe_ne_zero.2 hq.ne'))
  have hne : (Q.carrier ∩ Q'.carrier).Nonempty := by
    refine nonempty_of_measure_ne_zero (μ := volume) (fun h0 => ?_)
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hover
    exact hover.elim (fun h => hθ₀.ne' h) (fun h => hVne h)
  -- pass through the bare containment, then enlarge the half-widths
  refine (subset_resize_of_inter_nonempty hne).trans (Q.resize_carrier_mono ?_)
  rw [Pi.le_def, Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · -- long axis: `q₂ + 2 q'₂ + 2 q'₁ · s ≤ 10 q₂`, using only `s ≤ 1`
    simp only [Matrix.cons_val_zero]
    rw [← NNReal.coe_le_coe]
    push_cast [hsr]
    have hprod : (Q'.thicknesses 1 : ℝ) * Q.planarAngle Q' ≤ 2 * (Q.thicknesses 1 : ℝ) * 1 :=
      mul_le_mul (hc 1) (Q.planarAngle_le_one Q') (Q.planarAngle_nonneg Q')
        (mul_nonneg zero_le_two (Q.thicknesses 1).coe_nonneg)
    linarith [hc 0, hmr, hq2]
  · -- short axis: `q₁ + 2 q'₁ + 2 q'₂ · s ≤ 5 q₁ + 24 θ⁻¹ q₁`, using the planar-angle bound
    simp only [Matrix.cons_val_one]
    rw [← NNReal.coe_le_coe]
    push_cast [hsr]
    have hprod : (Q'.thicknesses 0 : ℝ) * Q.planarAngle Q'
        ≤ 12 * (θ : ℝ)⁻¹ * (Q.thicknesses 1 : ℝ) :=
      (mul_le_mul (hc 0) hsθ (Q.planarAngle_nonneg Q')
        (mul_nonneg zero_le_two (Q.thicknesses 0).coe_nonneg)).trans_eq (by field_simp; ring)
    linarith [hc 1]

/-! ### The planar Cordoba estimate (blueprint `lem:cordoba2D`) -/

namespace ConvexSpaceBody.IsFrostmanIn

/-! ### Overlap volume in the Frostman family (blueprint `lem:slabVolume`,
`lem:singleQOverlapBound`) -/

/-- **Frostman slab volume bound** (blueprint `lem:slabVolume`).

Keep the hypotheses of `le_volume_biUnion`: `V` is a family of convex bodies of
mutually comparable dimensions, each contained in `K`, and `C`-Frostman in `K`.
Fix `i ∈ V` and a threshold `θ ∈ (0, 1]`.  Then the *total volume* of the bodies `V j` whose
carrier overlaps `V i` in at least a `θ`-proportion of `|V i|` is bounded, with the density of the
family in `K` kept explicit on the right, by
`≤ (volume_comparison.C 2)² · C · (50 + 240 θ⁻¹) · |V i| · densityIn V K`.

This is the direct consequence of the Frostman condition, with no cardinality count.  The family is
of convex bodies, so the prism geometry is applied through outer prisms: with
`Pᵢ = outerPrism (V i)`
and `Pⱼ = outerPrism (V j)`, every `V j` with large overlap satisfies `V j ⊆ Pⱼ ⊆ R_θ(Pᵢ)`
(`subset_resize_of_le_volume_inter`), hence lies in the convex test body `K ⊓ R_θ(Pᵢ)`.  The
Frostman property says exactly that the density the family deposits in any test body `K'` is
`≤ C · densityIn V K`.  The convex-body-to-prism passage costs a factor `volume_comparison.C 2`
twice -- once on `|Pᵢ| ≲ volume_comparison.C 2 · |V i|`, and once when rescaling the overlap
threshold `θ ↦ θ / volume_comparison.C 2` so that the prism overlap dominates `θ |V i|`; the latter
lands inside the `θ⁻¹` term, which is why the dimensional factor is squared.  Bounding a sum of
volumes (rather than a number of slabs) is what Frostman provides natively, which is what the
total-overlap estimate actually needs. -/
theorem sum_volume_le_of_volume_inter_ge
    {ι : Type*} (s : Finset ι)
    (V : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E)
    {C : ℝ≥0∞} {i : ι} (hi : i ∈ s) (hpos : 0 < volume (V i).carrier)
    {θ : ℝ} (hθ₀ : 0 < θ)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFro : IsFrostmanIn s V K C) :
    ∑ j ∈ {j ∈ s |
        ENNReal.ofReal θ * volume (V i).carrier ≤ volume ((V i).carrier ∩ (V j).carrier)},
        volume (V j).carrier
      ≤ ((Metric.volume_comparison.C 2 : ℝ≥0∞) ^ 2) * C * ENNReal.ofReal (50 + 240 * θ⁻¹)
          * volume (V i).carrier * Kakeya.densityIn s V K := by
  classical
  have hfr : finrank ℝ E = 2 := Fact.out
  set κ : ℝ≥0 := Metric.volume_comparison.C 2 with hκdef
  have hκpos : 0 < κ := Metric.volume_comparison.C_pos 2
  have hκ1 : (1 : ℝ≥0) ≤ κ := by rw [hκdef, Metric.volume_comparison.C_two]; norm_num
  -- The filter predicate defining the counted family.
  set P : ι → Prop := fun j =>
    ENNReal.ofReal θ * volume (V i).carrier ≤ volume ((V i).carrier ∩ (V j).carrier) with hPdef
  -- Outer prism of `V i`, at dimension `2`.
  set Pi : PrismNDim 2 E E := outerPrism hfr (V i).isCompact (V i).nonempty with hPidef
  have hViPi : (V i).carrier ⊆ Pi.carrier :=
    outerPrism.self_subset hfr (V i).isCompact (V i).nonempty
  have hPithick (k : Fin 2) : (Pi.thicknesses k : ℝ) = thickness ℝ (V i).carrier (k : ℕ) := by
    rw [outerPrism.thicknesses_eq hfr (V i).isCompact (V i).nonempty k]; exact NNReal.coe_mk _ _
  -- Convex-body → prism volume comparison (`volume_outerPrism_le_volume_self`).
  have hPivol : volume Pi.carrier ≤ (κ : ℝ≥0∞) * volume (V i).carrier :=
    Metric.volume_outerPrism_le_volume_self hfr (V i).convex (V i).isCompact (V i).nonempty
  -- Positivity (from `hpos`) and decreasing order (from `thickness_antitone`) of the half-widths.
  have hq1 : 0 < Pi.thicknesses 1 := by
    have hmem : 1 ∈ Finset.range (Module.finrank ℝ E) := by rw [hfr]; simp
    have hbdd : Bornology.IsBounded (V i).carrier := (V i).isCompact.isBounded
    have hne : thickness ℝ (V i).carrier 1 ≠ 0 := fun hz =>
      ethickness_ne_zero_of_volume_pos hpos hmem <| by
        rw [ethickness_thickness' hbdd, hz, ENNReal.ofReal_zero]
    have hval : (Pi.thicknesses 1 : ℝ) = thickness ℝ (V i).carrier 1 := hPithick 1
    have : (0 : ℝ) < Pi.thicknesses 1 := by
      rw [hval]; exact (thickness_nonneg _ _).lt_of_ne' hne
    exact_mod_cast this
  have hmono : Pi.thicknesses 1 ≤ Pi.thicknesses 0 := by
    rw [← NNReal.coe_le_coe, hPithick 1, hPithick 0]
    exact Metric.thickness_antitone (𝕜 := ℝ) (V i).isCompact.isBounded (Nat.zero_le 1)
  -- Rescaled overlap threshold `θ' = θ / κ`, chosen so `θ' |Pi| ≤ θ |V i|`.
  set θ' : ℝ≥0 := θ.toNNReal / κ with hθ'def
  have hθ'pos : 0 < θ' := by
    rw [hθ'def]; exact div_pos (Real.toNNReal_pos.mpr hθ₀) hκpos
  -- The common fattening `R = resize Pi`, half-widths from `subset_resize_of_le_volume_inter`.
  set w : Fin 2 → ℝ≥0 :=
    ![10 * Pi.thicknesses 0, 5 * Pi.thicknesses 1 + 24 * θ'⁻¹ * Pi.thicknesses 1] with hwdef
  set R : PrismNDim 2 E E := Pi.resize w with hRdef
  -- Every counted `V j` lies in `R`: `V j ⊆ Pj ⊆ R` via `subset_resize_of_le_volume_inter`.
  have hcontain : ∀ j ∈ s, P j → (V j).carrier ⊆ R.carrier := by
    intro j hj hPj
    set Pj : PrismNDim 2 E E := outerPrism hfr (V j).isCompact (V j).nonempty with hPjdef
    have hVjPj : (V j).carrier ⊆ Pj.carrier :=
      outerPrism.self_subset hfr (V j).isCompact (V j).nonempty
    have hPjthick (k : Fin 2) : (Pj.thicknesses k : ℝ) = thickness ℝ (V j).carrier k := by
      rw [outerPrism.thicknesses_eq hfr (V j).isCompact (V j).nonempty k]
      exact NNReal.coe_mk _ _
    have hcomp : Pj.thicknesses ≤ 2 • Pi.thicknesses := fun k => by
      have h := hunif j hj i hi (k : ℕ)
      rw [_root_.Pi.smul_apply, nsmul_eq_mul] at h
      rw [_root_.Pi.smul_apply, nsmul_eq_mul, ← NNReal.coe_le_coe]
      push_cast at h ⊢
      rw [hPjthick k, hPithick k]
      linarith
    have hover : (θ' : ℝ≥0∞) * volume Pi.carrier ≤ volume (Pi.carrier ∩ Pj.carrier) := by
      have hθκ : (θ' : ℝ≥0∞) * (κ : ℝ≥0∞) = ENNReal.ofReal θ := by
        rw [hθ'def, ← ENNReal.coe_mul, div_mul_cancel₀ _ hκpos.ne',
          ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal θ hθ₀.le]
      have hkey : (θ' : ℝ≥0∞) * volume Pi.carrier ≤ ENNReal.ofReal θ * volume (V i).carrier := by
        rw [← hθκ, mul_assoc]; exact mul_le_mul_right hPivol _
      exact (hkey.trans hPj).trans (measure_mono (Set.inter_subset_inter hViPi hVjPj))
    exact hVjPj.trans (subset_resize_of_le_volume_inter hmono hq1 hcomp hθ'pos hover)
  -- Test body `K' = K ⊓ R` (nonempty since `V i ⊆ K ∩ R`).
  have hKRne : (K.carrier ∩ R.carrier).Nonempty := by
    have hwidths : Pi.thicknesses ≤ w := by
      rw [_root_.Pi.le_def, Fin.forall_fin_two]
      simp only [hwdef, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨le_mul_of_one_le_left zero_le (by norm_num),
        (le_mul_of_one_le_left zero_le (by norm_num)).trans le_self_add⟩
    have hxR : (V i).carrier ⊆ R.carrier := hViPi.trans (Pi.resize_carrier_mono hwidths)
    obtain ⟨x, hx⟩ := (V i).nonempty
    exact ⟨x, hsub i hi hx, hxR hx⟩
  set K' : ConvexSpaceBody E := ConvexSpaceBody.inter K R.toConvexSpaceBody hKRne with hK'def
  have hK'leK : K' ≤ K := fun x hx => hx.1
  -- Volume of the fattening: `|R| = (50 + 240 θ'⁻¹)|Pi| ≤ κ²(50 + 240 θ⁻¹)|V i|`.
  have hRvol : volume R.carrier
      ≤ ((κ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (50 + 240 * θ⁻¹) * volume (V i).carrier := by
    have key : volume R.carrier = ((4 * (w 0 * w 1) : ℝ≥0) : ℝ≥0∞) := by
      rw [hRdef, PrismNDim.volume_carrier, PrismNDim.resize_thicknesses, hfr, Fin.prod_univ_two]
      push_cast; ring
    have keyPi : volume Pi.carrier
        = ((4 * (Pi.thicknesses 0 * Pi.thicknesses 1) : ℝ≥0) : ℝ≥0∞) := by
      rw [Pi.volume_carrier, hfr, Fin.prod_univ_two]
      push_cast; ring
    have hR_eq : volume R.carrier
        = ((50 + 240 * θ'⁻¹ : ℝ≥0) : ℝ≥0∞) * volume Pi.carrier := by
      rw [key, keyPi, ← ENNReal.coe_mul]
      congr 1
      rw [hwdef]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    -- `(50 + 240 θ'⁻¹) κ ≤ κ² (50 + 240 θ⁻¹)`, an `ℝ≥0` computation via `θ'⁻¹ = κ θ⁻¹`.
    have hLcoe : ENNReal.ofReal (50 + 240 * θ⁻¹)
        = ((50 + 240 * θ.toNNReal⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      push_cast [Real.coe_toNNReal θ hθ₀.le]
      ring
    have hnn : (50 + 240 * θ'⁻¹ : ℝ≥0) * κ ≤ κ ^ 2 * (50 + 240 * θ.toNNReal⁻¹) := by
      rw [hθ'def, inv_div, div_eq_mul_inv,
        show (50 + 240 * (κ * θ.toNNReal⁻¹) : ℝ≥0) * κ
          = κ * 50 + κ ^ 2 * (240 * θ.toNNReal⁻¹) from by ring, mul_add]
      refine add_le_add (mul_le_mul' ?_ le_rfl) le_rfl
      rw [pow_two]
      exact le_mul_of_one_le_left zero_le hκ1
    have hfac : ((50 + 240 * θ'⁻¹ : ℝ≥0) : ℝ≥0∞) * (κ : ℝ≥0∞)
        ≤ ((κ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (50 + 240 * θ⁻¹) := by
      rw [hLcoe, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr hnn
    calc volume R.carrier
        = ((50 + 240 * θ'⁻¹ : ℝ≥0) : ℝ≥0∞) * volume Pi.carrier := hR_eq
      _ ≤ ((50 + 240 * θ'⁻¹ : ℝ≥0) : ℝ≥0∞) * ((κ : ℝ≥0∞) * volume (V i).carrier) :=
          mul_le_mul_right hPivol _
      _ = (((50 + 240 * θ'⁻¹ : ℝ≥0) : ℝ≥0∞) * (κ : ℝ≥0∞)) * volume (V i).carrier :=
          (mul_assoc _ _ _).symm
      _ ≤ ((κ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (50 + 240 * θ⁻¹) * volume (V i).carrier :=
          mul_le_mul' hfac le_rfl
  -- Frostman + density chain.
  have hstep1 : ∑ j ∈ {j ∈ s | P j}, volume (V j).carrier
      ≤ ∑ j ∈ {j ∈ s | V j ≤ K'}, volume (V j).carrier := by
    refine Finset.sum_le_sum_of_subset fun x hx => ?_
    obtain ⟨hxs, hPx⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxs, ?_⟩
    dsimp [K', ConvexSpaceBody.inter]
    exact Set.subset_inter (hsub x hxs) (hcontain x hxs hPx)
  calc ∑ j ∈ {j ∈ s | P j}, volume (V j).carrier
      ≤ Kakeya.densityIn s V K' * volume K'.carrier :=
        hstep1.trans_eq (Kakeya.sum_volume_eq_densityIn_mul_volume s V K')
    _ ≤ (C * Kakeya.densityIn s V K) * volume R.carrier :=
        (mul_le_mul_left (hFro K' hK'leK) _).trans
          (mul_le_mul_right (measure_mono fun x hx => hx.2) _)
    _ ≤ (C * Kakeya.densityIn s V K)
          * (((κ : ℝ≥0∞) ^ 2) * ENNReal.ofReal (50 + 240 * θ⁻¹) * volume (V i).carrier) :=
        mul_le_mul_right hRvol _
    _ = ((κ : ℝ≥0∞) ^ 2) * C * ENNReal.ofReal (50 + 240 * θ⁻¹)
          * volume (V i).carrier * Kakeya.densityIn s V K := by ring

/-- **Small-overlap contribution** (blueprint `lem:smallOverlap`).

The terms of the total-overlap sum coming from bodies `V j` whose overlap with `V i` is below a
threshold `t` contribute at most `#s · t`: each such term is `< t`, and there are at most `#s` of
them.  No Frostman property, geometry, or comparability is used; this is the part of
`sum_volume_inter_le` that is handled by counting rather than by the slab volume bound.  In the
total-overlap proof the threshold is taken to be `t = η · |V i|`, and the absolute decomposition
`ENNReal.sum_eq_sum_filter_lt_add_sum_range_dyadic` separates this small part from the dyadic
shells `|V i ∩ V j| ∈ [2ⁿ t, 2ⁿ⁺¹ t)`. -/
theorem sum_volume_inter_lt_le {ι : Type*} (s : Finset ι) (V : ι → ConvexSpaceBody E)
    (i : ι) (t : ℝ≥0∞) :
    ∑ j ∈ {j ∈ s | volume ((V i).carrier ∩ (V j).carrier) < t},
        volume ((V i).carrier ∩ (V j).carrier)
      ≤ (s.card : ℝ≥0∞) * t := by
  classical
  calc ∑ j ∈ {j ∈ s | volume ((V i).carrier ∩ (V j).carrier) < t},
          volume ((V i).carrier ∩ (V j).carrier)
      ≤ {j ∈ s | volume ((V i).carrier ∩ (V j).carrier) < t}.card • t :=
        Finset.sum_le_card_nsmul _ _ _ fun j hj => (Finset.mem_filter.mp hj).2.le
    _ = ({j ∈ s | volume ((V i).carrier ∩ (V j).carrier) < t}.card : ℝ≥0∞) * t := by
        rw [nsmul_eq_mul]
    _ ≤ (s.card : ℝ≥0∞) * t := by gcongr; exact Finset.filter_subset _ _

/-- Absolute constant in the total-overlap bound `sum_volume_inter_le`.  It is
`580 · κ⁴` with `κ = volume_comparison.C 2` the convex-body-to-prism volume ratio: each of the
`N + 1` dyadic contributions (small part and `N` shells) costs `κ` twice through the slab volume
bound and twice more through comparable carrier volumes, and `580 = 2 · 290` collects the shell
constant. -/
@[nolint defsWithUnderscore]
noncomputable def sum_volume_inter_le.C : NNReal := 580 * Metric.volume_comparison.C 2 ^ 4

lemma sum_volume_inter_le.C_pos : 0 < C := by
  unfold C
  exact mul_pos (by norm_num) (pow_pos (Metric.volume_comparison.C_pos 2) 4)

/-- **One dyadic shell of the total-overlap sum**, extracted from the proof of
`sum_volume_inter_le`.

Under the hypotheses of `sum_volume_inter_le`, the bodies `V j` whose overlap with `V i` lies in the
window `[θ |V i|, 2 θ |V i|)` contribute at most `C · #s · |V i|² / |K|`, **independently of the
scale `θ`**: each such overlap is `< 2 θ |V i| ≤ 2 θ κ |V j|`, the Frostman slab volume bound
(`sum_volume_le_of_volume_inter_ge`) bounds `∑ |V j|` over the window by
`κ² C (50 + 240 θ⁻¹) |V i| · densityIn`, the factor `θ` cancels the `θ⁻¹` (on a nonempty window
`θ ≤ 1`, so `θ (50 + 240 θ⁻¹) ≤ 290`), and comparable volumes give
`densityIn ≤ κ · #s · |V i| / |K|`. -/
private lemma sum_volume_inter_shell_le
    {ι : Type*} (s : Finset ι)
    (V : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E)
    {C : ℝ≥0∞} {i : ι} (hi : i ∈ s) (hvipos : 0 < volume (V i).carrier)
    {θ : ℝ} (hθpos : 0 < θ)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFro : IsFrostmanIn s V K C) :
    ∑ j ∈ {j ∈ s | ENNReal.ofReal θ * volume (V i).carrier
          ≤ volume ((V i).carrier ∩ (V j).carrier) ∧
        volume ((V i).carrier ∩ (V j).carrier) < 2 * (ENNReal.ofReal θ * volume (V i).carrier)},
        volume ((V i).carrier ∩ (V j).carrier)
      ≤ (sum_volume_inter_le.C : ℝ≥0∞) * C * s.card
          * volume (V i).carrier ^ 2 / volume K.carrier := by
  have hfr : finrank ℝ E = 2 := Fact.out
  set vi : ℝ≥0∞ := volume (V i).carrier
  set vK : ℝ≥0∞ := volume K.carrier with hvK
  set κ : ℝ≥0∞ := (Metric.volume_comparison.C 2 : ℝ≥0∞) with hκ
  set d : ℝ≥0∞ := Kakeya.densityIn s V K with hd
  set F := {j ∈ s | ENNReal.ofReal θ * vi ≤ volume ((V i).carrier ∩ (V j).carrier) ∧
    volume ((V i).carrier ∩ (V j).carrier) < 2 * (ENNReal.ofReal θ * vi)}
  have hvi_top : vi ≠ ⊤ := (V i).isCompact.measure_lt_top.ne
  have hvK_top : vK ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hvK0 : vK ≠ 0 := (hvipos.trans_le (measure_mono (hsub i hi))).ne'
  have hC580 : (sum_volume_inter_le.C : ℝ≥0∞) = 580 * κ ^ 4 := by
    rw [hκ]; simp only [sum_volume_inter_le.C]; push_cast; ring
  -- Comparable carrier volumes in both directions.
  have hcompj : ∀ j ∈ s, vi ≤ κ * volume (V j).carrier := fun j hj => by
    have h := Metric.thickness.volume_comparison hunif i hi j hj
    rwa [hfr, ← hκ] at h
  have hcompj' : ∀ j ∈ s, volume (V j).carrier ≤ κ * vi := fun j hj => by
    have h := Metric.thickness.volume_comparison hunif j hj i hi
    rwa [hfr, ← hκ] at h
  -- Frostman slab volume bound at threshold `θ`, and the density bound.
  have hslab : ∑ j ∈ {j ∈ s | ENNReal.ofReal θ * vi ≤ volume ((V i).carrier ∩ (V j).carrier)},
      volume (V j).carrier ≤ κ ^ 2 * C * ENNReal.ofReal (50 + 240 * θ⁻¹) * vi * d := by
    have h := sum_volume_le_of_volume_inter_ge s V K hi hvipos hθpos hunif hsub hFro
    rwa [← hκ] at h
  have hdbound : d ≤ κ * (s.card : ℝ≥0∞) * vi * vK⁻¹ := by
    rw [hd, Kakeya.densityIn_of_all_le hsub, div_eq_mul_inv, ← hvK]
    refine mul_le_mul_left ?_ vK⁻¹
    calc (∑ k ∈ s, volume (V k).carrier) ≤ ∑ _k ∈ s, κ * vi := Finset.sum_le_sum hcompj'
      _ = (s.card : ℝ≥0∞) * (κ * vi) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = κ * (s.card : ℝ≥0∞) * vi := by ring
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · rw [hFe, Finset.sum_empty]; exact zero_le
  · -- On a nonempty window the scale satisfies `θ ≤ 1`.
    have hθ1 : θ ≤ 1 := by
      obtain ⟨j₀, hj₀⟩ := hFne
      obtain ⟨-, hlo, -⟩ := Finset.mem_filter.mp hj₀
      refine ENNReal.ofReal_le_one.mp ((ENNReal.mul_le_mul_iff_left hvipos.ne' hvi_top).mp ?_)
      rw [one_mul]
      exact hlo.trans (measure_mono Set.inter_subset_left)
    -- The `θ` of the window cancels the `θ⁻¹` of the slab bound: `θ (50 + 240 θ⁻¹) = 50 θ + 240`.
    have hprod : ENNReal.ofReal θ * ENNReal.ofReal (50 + 240 * θ⁻¹) ≤ 290 := by
      rw [← ENNReal.ofReal_mul hθpos.le,
        show (290 : ℝ≥0∞) = ENNReal.ofReal 290 from by rw [ENNReal.ofReal_ofNat]]
      refine ENNReal.ofReal_le_ofReal ?_
      calc θ * (50 + 240 * θ⁻¹) = 50 * θ + 240 * (θ * θ⁻¹) := by ring
        _ = 50 * θ + 240 := by rw [mul_inv_cancel₀ hθpos.ne', mul_one]
        _ ≤ 290 := by linarith
    calc ∑ j ∈ F, volume ((V i).carrier ∩ (V j).carrier)
        ≤ 2 * ENNReal.ofReal θ * κ * ∑ j ∈ F, volume (V j).carrier := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j hjF => ?_
          obtain ⟨hjs, -, hhi⟩ := Finset.mem_filter.mp hjF
          calc volume ((V i).carrier ∩ (V j).carrier) ≤ 2 * (ENNReal.ofReal θ * vi) := hhi.le
            _ ≤ 2 * (ENNReal.ofReal θ * (κ * volume (V j).carrier)) :=
                mul_le_mul_right (mul_le_mul_right (hcompj j hjs) _) 2
            _ = 2 * ENNReal.ofReal θ * κ * volume (V j).carrier := by ring
      _ ≤ 2 * ENNReal.ofReal θ * κ *
            (κ ^ 2 * C * ENNReal.ofReal (50 + 240 * θ⁻¹) * vi * d) :=
          mul_le_mul_right (le_trans (Finset.sum_le_sum_of_subset
            (fun j hjF => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjF).1,
              (Finset.mem_filter.mp hjF).2.1⟩)) hslab) _
      _ = κ ^ 3 * C * vi * d * (ENNReal.ofReal θ * ENNReal.ofReal (50 + 240 * θ⁻¹)) * 2 := by
          ring
      _ ≤ κ ^ 3 * C * vi * (κ * (s.card : ℝ≥0∞) * vi * vK⁻¹) * 290 * 2 :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hdbound) hprod) le_rfl
      _ = (sum_volume_inter_le.C : ℝ≥0∞) * C * (s.card : ℝ≥0∞) * vi ^ 2 / vK := by
          rw [hC580, div_eq_mul_inv]; ring

/-- **Total overlap of a fixed prism** (blueprint `lem:singleQOverlapBound`).

Keep the hypotheses of `le_volume_biUnion`.  Then for every `i ∈ V`,
`∑ j, |V i ∩ V j| ≤ C · (N + 1) · #V · |V i|² / |K|`,
where `N` is any dyadic scale count dominating the eccentricity `|K| / |V i|`, i.e.
`|K| ≤ 2 ^ N |V i|` (so `N = ⌈log₂(|K| / |V i|)⌉` works).  The factor `N + 1` is the **explicit
logarithmic loss**: it is the number of dyadic scales the overlap ranges over, and replaces the
blueprint's `⪅`.

Proof route (entirely through volumes, no cardinality): decompose the overlap sum dyadically
(`ENNReal.sum_eq_sum_filter_lt_add_sum_range_dyadic`) with cutoff `t = |V i|² / |K|` and `N`
shells.  The small part `∑_{|V i ∩ V j| < t} |V i ∩ V j| ≤ #V · t = #V · |V i|² / |K|`
(`sum_volume_inter_lt_le`).  Each shell is handled by `sum_volume_inter_shell_le`: on the shell
`|V i ∩ V j| ∼ θ |V i|`, comparable volumes give
`|V i ∩ V j| ≤ 2θ |V i| ⪅ θ |V j|`, so the shell contributes `⪅ θ · ∑_shell |V j|`; the Frostman
slab volume bound (`sum_volume_le_of_volume_inter_ge`) bounds `∑_shell |V j| ⪅ C θ⁻¹ (|V i| / |K|)
∑ₖ|V k|`, the `θ` cancels, and comparable volumes turn `∑ₖ|V k|` into `#V · |V i|` — each shell
contributing `⪅ C · #V · |V i|² / |K|`, independent of the scale.  Summing the small part and the
`N` shells gives the `(N + 1)` factor. -/
theorem sum_volume_inter_le
    {ι : Type*} (s : Finset ι)
    (V : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E)
    {C : ℝ≥0∞} {i : ι} (hi : i ∈ s) {N : ℕ}
    (hN : volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hFro : IsFrostmanIn s V K C) :
    ∑ j ∈ s, volume ((V i).carrier ∩ (V j).carrier)
      ≤ (sum_volume_inter_le.C : ℝ≥0∞) * ((N : ℝ≥0∞) + 1) * C * s.card
          * volume (V i).carrier ^ 2 / volume K.carrier := by
  -- Abbreviations for the overlap function, the two volumes, and the dimensional constant `κ`.
  set a : ι → ℝ≥0∞ := fun j => volume ((V i).carrier ∩ (V j).carrier)
  set vi : ℝ≥0∞ := volume (V i).carrier
  set vK : ℝ≥0∞ := volume K.carrier
  set κ : ℝ≥0∞ := (Metric.volume_comparison.C 2 : ℝ≥0∞) with hκ
  -- Finiteness and elementary bounds.
  have hvi_top : vi ≠ ⊤ := (V i).isCompact.measure_lt_top.ne
  have hvK_top : vK ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have haj_le : ∀ j, a j ≤ vi := fun j => measure_mono Set.inter_subset_left
  -- `κ ≥ 1` (the volume ratio is at least `1`), and the tracked constant in `κ`-form.
  have hκ1 : (1 : ℝ≥0∞) ≤ κ := by rw [hκ, Metric.volume_comparison.C_two]; norm_num
  have hC580 : (sum_volume_inter_le.C : ℝ≥0∞) = 580 * κ ^ 4 := by
    rw [hκ]; simp only [sum_volume_inter_le.C]; push_cast; ring
  clear_value κ
  -- Degenerate case: `V i` null makes every overlap null and the LHS zero.
  rcases eq_or_ne vi 0 with hvi0 | hvi0
  · exact (Finset.sum_eq_zero fun j _ => le_antisymm (hvi0 ▸ haj_le j) zero_le).trans_le zero_le
  · -- Main case: `0 < vi ≤ vK`.
    have hvipos : 0 < vi := pos_iff_ne_zero.mpr hvi0
    have hvK0 : vK ≠ 0 := (hvipos.trans_le (measure_mono (hsub i hi))).ne'
    -- The Frostman constant is `≥ 1` (test the condition on `K' = K`).
    have hC1 : 1 ≤ C := hFro.one_le <| by
      rw [Kakeya.densityIn_pos_iff]; exact ⟨i, hi, hvipos, hsub i hi⟩
    -- Dyadic cutoff `t = 2 |V i|² / |K|`.  The factor `2` guarantees the strict bound below.
    set t : ℝ≥0∞ := 2 * vi ^ 2 / vK with ht
    -- Every overlap is `< 2^N t`: `a j ≤ vi < 2 vi ≤ 2^N t`, the last step from `hN`.
    have hle : 2 * vi ≤ 2 ^ N * t := by
      refine (ENNReal.mul_le_mul_iff_left hvK0 hvK_top).mp ?_
      rw [show (2 : ℝ≥0∞) ^ N * t * vK = 2 ^ N * (2 * vi ^ 2) from by
        rw [mul_assoc, ht, ENNReal.div_mul_cancel hvK0 hvK_top]]
      calc 2 * vi * vK ≤ 2 * vi * (2 ^ N * vi) := mul_le_mul_right hN _
        _ = 2 ^ N * (2 * vi ^ 2) := by ring
    have hstrict : ∀ j ∈ s, a j < 2 ^ N * t := by
      intro j _
      refine (haj_le j).trans_lt (lt_of_lt_of_le ?_ hle)
      rw [two_mul]; exact ENNReal.lt_add_right hvi_top hvipos.ne'
    -- Abstract dyadic decomposition into the small part and `N` shells.
    have hdecomp := ENNReal.sum_eq_sum_filter_lt_add_sum_range_dyadic a t N s hstrict
    -- The common per-contribution bound `B`, expressed through the tracked constant.
    set B : ℝ≥0∞ :=
      (sum_volume_inter_le.C : ℝ≥0∞) * C * (s.card : ℝ≥0∞) * vi ^ 2 / vK with hB
    -- Small part: `∑_{a < t} a ≤ #s · t = 2 #s |V i|²/|K| ≤ B` (`sum_volume_inter_lt_le`).
    have hsmall : ∑ j ∈ {j ∈ s | a j < t}, a j ≤ B := by
      have h_two_le : (2 : ℝ≥0∞) ≤ (sum_volume_inter_le.C : ℝ≥0∞) * C := by
        rw [hC580]
        calc (2 : ℝ≥0∞) ≤ 580 * 1 ^ 4 * 1 := by norm_num
          _ ≤ 580 * κ ^ 4 * C :=
              mul_le_mul' (mul_le_mul' le_rfl (ENNReal.pow_le_pow_left hκ1)) hC1
      calc ∑ j ∈ {j ∈ s | a j < t}, a j ≤ (s.card : ℝ≥0∞) * t :=
            sum_volume_inter_lt_le s V i t
        _ = 2 * ((s.card : ℝ≥0∞) * vi ^ 2 / vK) := by
            rw [ht]; simp only [div_eq_mul_inv]; ring
        _ ≤ (sum_volume_inter_le.C : ℝ≥0∞) * C * ((s.card : ℝ≥0∞) * vi ^ 2 / vK) :=
            mul_le_mul' h_two_le le_rfl
        _ = B := by rw [hB]; simp only [div_eq_mul_inv]; ring
    -- Each dyadic shell contributes `≤ B`, independent of the scale `n`: the shell
    -- `[2ⁿ t, 2ⁿ⁺¹ t)` is exactly the window `[θ |V i|, 2 θ |V i|)` at the scale
    -- `θ = 2ⁿ⁺¹ |V i| / |K|`, so `sum_volume_inter_shell_le` applies.
    have hshell : ∀ n ∈ Finset.range N,
        ∑ j ∈ {j ∈ s | 2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t}, a j ≤ B := by
      intro n _
      obtain ⟨θ, hθpos, hθvi⟩ : ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal θ * vi = 2 ^ n * t := by
        have hτne : (2 : ℝ≥0∞) ^ (n + 1) * vi / vK ≠ ⊤ :=
          ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hvi_top) hvK0
        refine ⟨((2 : ℝ≥0∞) ^ (n + 1) * vi / vK).toReal, ENNReal.toReal_pos
          (ENNReal.div_pos (mul_ne_zero (by simp) hvipos.ne') hvK_top).ne' hτne, ?_⟩
        rw [ENNReal.ofReal_toReal hτne, ht]
        simp only [div_eq_mul_inv, pow_succ]; ring
      have h2θ : (2 : ℝ≥0∞) * (ENNReal.ofReal θ * vi) = 2 ^ (n + 1) * t := by
        rw [hθvi, ← mul_assoc, ← pow_succ']
      refine le_trans (Finset.sum_le_sum_of_subset fun j hj => ?_)
        (sum_volume_inter_shell_le s V K hi hvipos hθpos hunif hsub hFro)
      obtain ⟨hjs, hlo, hhi⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hjs, hθvi.trans_le hlo, hhi.trans_eq h2θ.symm⟩
    -- Assemble: `∑ a = small + ∑_{n<N} shell_n ≤ B + N · B = (N+1) · B`, then reorder to the goal.
    have hsum_shells :
        ∑ n ∈ Finset.range N,
            ∑ j ∈ {j ∈ s | 2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t}, a j
          ≤ (N : ℝ≥0∞) * B :=
      (Finset.sum_le_sum hshell).trans_eq (by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul])
    calc ∑ j ∈ s, a j = _ := hdecomp
      _ ≤ B + (N : ℝ≥0∞) * B := add_le_add hsmall hsum_shells
      _ = (sum_volume_inter_le.C : ℝ≥0∞) * ((N : ℝ≥0∞) + 1) * C * (s.card : ℝ≥0∞)
            * vi ^ 2 / vK := by rw [hB]; simp only [div_eq_mul_inv]; ring

/-- Absolute constant in the planar Cordoba estimate `le_volume_biUnion`: the
reciprocal of the product of the total-overlap constant and the comparable-volume
constant, as produced by the Cauchy--Schwarz assembly. -/
@[nolint defsWithUnderscore]
noncomputable def le_volume_biUnion_TwoDim.c : NNReal :=
  (sum_volume_inter_le.C * Metric.volume_comparison.C 2)⁻¹

lemma le_volume_biUnion_TwoDim.c_pos : 0 < c := by
  apply inv_pos_of_pos
  apply mul_pos
  · exact sum_volume_inter_le.C_pos
  · exact volume_comparison.C_pos _

/-- **Aggregate planar Cordoba `L²` estimate**.

Let `K ⊆ ℝ²` be convex and let `V` be a family of shaded convex bodies, each
contained in `K`.  It is enough that the *total* shading mass be at least `μ` times the total
carrier mass; no bodywise density lower bound is required.  If `V` is `C`-Frostman in `K`, then
`|U(V)| ≳ (N + 1)⁻¹ C⁻¹ μ² |K|`,
where `N` bounds the dyadic eccentricity of the family: `|K| ≤ 2 ^ N |V i|` for every `i`
(so `N = ⌈log₂(|K| / min |V i|)⌉`).  The factor `N + 1` is the **explicit logarithmic loss** of
the Córdoba `L²` argument, inherited from `sum_volume_inter_le`.

The common-dimensions hypothesis of the blueprint is modelled directly on the
shaded bodies: their affine thicknesses are pairwise comparable up to a factor
`2` (`hunif`), so no auxiliary family of prisms with prescribed half-widths is
needed. -/
theorem le_volume_biUnion_TwoDim_aggregate
    {ι : Type*} {s : Finset ι}
    (V : ι → ShadedBody E)
    (K : ConvexSpaceBody E)
    {C μ : ℝ≥0∞} {N : ℕ}
    (hs : s.Nonempty)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hvol : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hfull : μ * (∑ i ∈ s, volume (V i).carrier) ≤
      ∑ i ∈ s, volume (V i).shade)
    (hFro : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C) :
    (le_volume_biUnion_TwoDim.c : ℝ≥0∞) * μ ^ 2 * volume K.carrier
      ≤ ((N : ℝ≥0∞) + 1) * C * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  -- Finiteness and positivity facts.
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hcar_le : ∀ i ∈ s, volume (V i).carrier ≤ volume K.carrier :=
    fun i hi => measure_mono (hsub i hi)
  have hK0 : volume K.carrier ≠ 0 :=
    (lt_of_lt_of_le (hvol i₀ hi₀) (hcar_le i₀ hi₀)).ne'
  have hσ0 : (∑ j ∈ s, volume (V j).carrier) ≠ 0 :=
    (lt_of_lt_of_le (hvol i₀ hi₀)
      (Finset.single_le_sum (f := fun j => volume (V j).carrier)
        (fun j _ => zero_le) hi₀)).ne'
  have hσtop : (∑ j ∈ s, volume (V j).carrier) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i hi => lt_of_le_of_lt (hcar_le i hi) hKtop.lt_top).ne
  -- The two tracked absolute constants, with positivity.
  have hCcκ_ne : sum_volume_inter_le.C * Metric.volume_comparison.C 2 ≠ 0 :=
    mul_ne_zero sum_volume_inter_le.C_pos.ne' (Metric.volume_comparison.C_pos 2).ne'
  have hCcκ0 : (sum_volume_inter_le.C : ℝ≥0∞) * (Metric.volume_comparison.C 2 : ℝ≥0∞) ≠ 0 := by
    rw [← ENNReal.coe_mul]; exact ENNReal.coe_ne_zero.mpr hCcκ_ne
  have hCcκtop :
      (sum_volume_inter_le.C : ℝ≥0∞) * (Metric.volume_comparison.C 2 : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.coe_mul]; exact ENNReal.coe_ne_top
  -- Abbreviate the heavy opaque volumes and constants up front (after dropping the spent
  -- hypotheses, which keeps the abstraction cheap), so every subsequent `have` is stated
  -- and elaborated with small atoms rather than giant volume terms.
  clear hcar_le hvol hi₀ i₀
  set U := volume (⋃ i ∈ s, (V i).shade)
  set Kv := volume K.carrier
  set σ := ∑ j ∈ s, volume (V j).carrier with hσdef
  set Cc := (sum_volume_inter_le.C : ℝ≥0∞) with hCc
  set κ := (Metric.volume_comparison.C 2 : ℝ≥0∞) with hκ
  -- The explicit logarithmic factor `M = N + 1` (number of dyadic scales, small part included).
  set M := (N : ℝ≥0∞) + 1
  -- Cauchy–Schwarz on the shades (reused repo lemma).
  have hCS := MeasureTheory.sq_sum_volume_le (s := s) (Y := fun i => (V i).shade)
    (fun i _ => (V i).measurableSet_shade)
  -- Numerator lower bound `μ · σ ≤ ∑ |Y(V i)|`.
  have hnum : μ * σ ≤ ∑ i ∈ s, volume (V i).shade := by
    simpa only [hσdef] using hfull
  -- Shade overlaps are bounded by carrier overlaps.
  have hsh_le : (∑ i ∈ s, ∑ j ∈ s, volume ((V i).shade ∩ (V j).shade))
      ≤ ∑ i ∈ s, ∑ j ∈ s, volume ((V i).carrier ∩ (V j).carrier) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      measure_mono (Set.inter_subset_inter (V i).shade_subset (V j).shade_subset)
  -- `n · ∑ |V i|² ≤ κ · σ²` from comparability of carrier volumes.
  have hnT : (s.card : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier ^ 2 ≤ κ * σ ^ 2 := by
    calc
      _ = ∑ i ∈ s, (s.card : ℝ≥0∞) * volume (V i).carrier * volume (V i).carrier := by
          simp only [Finset.mul_sum, sq, mul_assoc]
      _ ≤ ∑ i ∈ s, κ * σ * volume (V i).carrier := by
          refine Finset.sum_le_sum fun i hi => mul_le_mul_left ?_ _
          have hfr : finrank ℝ E = 2 := Fact.out
          simpa only [hfr] using
            card_mul_volume_carrier_le_sum (V := fun i => (V i).toConvexSpaceBody) hunif hi
      _ = κ * σ ^ 2 := by rw [← Finset.mul_sum, ← hσdef, sq, mul_assoc]
  -- Denominator: carrier double sum bounded via the total-overlap estimate.
  have hDcar : (∑ i ∈ s, ∑ j ∈ s, volume ((V i).carrier ∩ (V j).carrier))
      ≤ Kv⁻¹ * (Cc * M) * C * (κ * σ ^ 2) := by
    calc
      _  ≤ ∑ i ∈ s, Cc * M * C * (s.card : ℝ≥0∞) * volume (V i).carrier ^ 2 / Kv :=
          Finset.sum_le_sum fun i hi => sum_volume_inter_le s
            (fun i => (V i).toConvexSpaceBody) K hi (hN i hi) hunif hsub hFro
      _ = Kv⁻¹ * (Cc * M) * C * ((s.card : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier ^ 2) := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ ≤ Kv⁻¹ * (Cc * M) * C * (κ * σ ^ 2) := mul_le_mul_right hnT _
  -- Assemble, then cancel `σ²`, then `|K|`, then the constant.
  have hμ2 : μ ^ 2 ≤ U * Kv⁻¹ * (Cc * M) * C * κ := by
    refine (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hσ0) (ENNReal.pow_ne_top hσtop)).mp ?_
    calc μ ^ 2 * σ ^ 2 = (μ * σ) ^ 2 := (mul_pow _ _ 2).symm
      _ ≤ (∑ i ∈ s, volume (V i).shade) ^ 2 := pow_le_pow_left' hnum 2
      _ ≤ U * (∑ i ∈ s, ∑ j ∈ s, volume ((V i).shade ∩ (V j).shade)) := hCS
      _ ≤ U * (Kv⁻¹ * (Cc * M) * C * (κ * σ ^ 2)) :=
          mul_le_mul_right (hsh_le.trans hDcar) _
      _ = (U * Kv⁻¹ * (Cc * M) * C * κ) * σ ^ 2 := by ring
  have hleC : (le_volume_biUnion_TwoDim.c : ℝ≥0∞) = (Cc * κ)⁻¹ := by
    simp only [le_volume_biUnion_TwoDim.c, hCc, hκ, ENNReal.coe_inv hCcκ_ne, ENNReal.coe_mul]
  -- `c · μ² |K| ≤ M · C · |U|` (the `M = N + 1` factor rides through).
  calc (le_volume_biUnion_TwoDim.c : ℝ≥0∞) * μ ^ 2 * Kv
      = (Cc * κ)⁻¹ * (μ ^ 2 * Kv) := by rw [hleC, mul_assoc]
    _ ≤ (Cc * κ)⁻¹ * ((U * Kv⁻¹ * (Cc * M) * C * κ) * Kv) :=
        mul_le_mul_right (mul_le_mul_left hμ2 _) _
    _ = ((Cc * κ)⁻¹ * (Cc * κ)) * (M * C * U) * (Kv⁻¹ * Kv) := by ring
    _ = M * C * U := by
        rw [ENNReal.inv_mul_cancel hCcκ0 hCcκtop, ENNReal.inv_mul_cancel hK0 hKtop, one_mul,
          mul_one]

/-- **Planar Cordoba `L²` estimate** (blueprint `lem:cordoba2D`).

This is the bodywise-density interface used previously.  It is a direct consequence of
`le_volume_biUnion_TwoDim_aggregate`, obtained by summing the bodywise lower bounds. -/
theorem le_volume_biUnion_TwoDim
    {ι : Type*} {s : Finset ι}
    (V : ι → ShadedBody E)
    (K : ConvexSpaceBody E)
    {C μ : ℝ≥0∞} {N : ℕ}
    (hs : s.Nonempty)
    (hN : ∀ i ∈ s, volume K.carrier ≤ 2 ^ N * volume (V i).carrier)
    (hunif : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)
    (hsub : ∀ i ∈ s, (V i).carrier ⊆ K.carrier)
    (hvol : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hfull : ∀ i ∈ s, μ * volume (V i).carrier ≤ volume (V i).shade)
    (hFro : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) K C) :
    (le_volume_biUnion_TwoDim.c : ℝ≥0∞) * μ ^ 2 * volume K.carrier
      ≤ ((N : ℝ≥0∞) + 1) * C * volume (⋃ i ∈ s, (V i).shade) := by
  apply le_volume_biUnion_TwoDim_aggregate V K hs hN hunif hsub hvol
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum hfull
  · exact hFro

end ConvexSpaceBody.IsFrostmanIn
