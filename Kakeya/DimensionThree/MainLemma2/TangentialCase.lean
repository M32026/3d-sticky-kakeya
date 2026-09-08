/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.AffineMap
public import Kakeya.PartialEstimates
public import Kakeya.Uniform
public import Kakeya.Factorization
public import Kakeya.DimensionThree.Plank.AngleDef
public import Kakeya.DimensionThree.MainLemma2.VeryNotSticky
public import Kakeya.Mathlib.MeasureTheory.Lintegral
public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.DimensionThree.MainLemma2.NonSlabSplit
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre
public import Kakeya.DimensionThree.MainLemma2.TypicalAngle
public import Kakeya.DimensionThree.MainLemma2.SplitInputsLoose

/-!
In this file, we prove the tangential case of the non-slab case
of the thin case of Main Lemma 2.

The three auxiliary statements are the ones the blueprint proof of `lem:ml2tangential`
consumes: the reduction to a single dense slab (`lem:ml2tangentialSlabDecomp`), the
multiplicity estimate inside that slab (`lem:ml2tangentialSlabMult`), and the combination of
the non-slab splitting with the Katz–Tao bound at the ball `B` (`lem:ml2tangentialSplit`).
Every *exponent* loss of the blueprint is made explicit against the single budget
`Kakeya.VeryNotSticky.parameterSeparationConstant`, each of the three lemmas spending a
quarter of it, so that the tangential budget `params.tangential` alone closes the argument
with no further smallness assumption on `δ`.

*Constants are not exponents.* By the constant/exponent distinction of the blueprint
(the paragraph opening the tangential subsubsection), the budget governs exponent losses
only: since `δ` is allowed up to `1`, a factor `δ^{-s}` with `s > 0` is `≥ 1` but does not
dominate a given constant. Multiplicative constants are therefore either carried by name in
the statements — `tangentialSlabDecompConstant tc.C` in the density clause, `Cμ` in the
multiplicity clause, `CΔ` in the rescaled slab — or discharged by an explicit fixed-scale
threshold of the shape `C ≤ δ^{-s}`.

*Two currencies, two refinement factors.* The pair `(𝕎''_B, Y_{𝕎''_B})` accompanying the
typical angle is only a `c`-refinement of `(𝕎'_B, Y_{𝕎'_B})` with `δ^{2η} ≤ c`, and by
blueprint `lem:ml2fullnessRefine` and `lem:ml2multRefine` that costs a factor `c` in the
fullness *and* a factor `c` in the multiplicity. Both clauses of `tangentialSlabDecomp`
therefore carry it: in the density clause it compounds with the `δ^{2η}` of `(T2)` and
raises the exponent to `δ^{8η}` (blueprint `lem:ml2tangentialDensityChain`), and in the
multiplicity clause it is one further power `δ^{-2η}`, charged — together with the
`δ^{-2τ'}` of the fibre count and the `δ^{-τ'}` paying for `Cμ` — to that lemma's quarter
budget `C_sep τ'/4`, which `lem:ml2tangentialSlabDecompExponent` verifies with room to
spare. Earlier drafts of both clauses dropped the refinement factor; the `2η`/`tc.C` form of
the density clause is not derivable (blueprint gives a counterexample).
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric

universe u
/-- **Constant in Lemma `tangentialSlabDecomp`** (blueprint
`def:ml2tangentialSlabDecompConstant`, `C_{lem:ml2tangentialSlabDecomp}`).

`C_{lem:ml2tangentialSlabDecomp}(C^λ) = 100 C^λ`, where `C^λ = tc.C` is the density comparison
constant of blueprint `def:ml2thinFullnessConstant`, the one appearing in the explicit form
`densityWWBexplicit` of (T2).

The factor `100` is the reciprocal of the slab-selection threshold of blueprint
`lem:ml2tangentialDenseSlabs`: only the slabs with
`λ(𝕎''_S, Y_{𝕎''_S}) ≥ (1/100) λ(𝕎''_B, Y_{𝕎''_B})` are kept, so the density guaranteed at the
selected slab is that of `𝕎''_B` divided by `100`. That factor is absolute: it depends neither
on the ambient dimension, nor on `δ`, nor on the ball `B`, nor on the slab `S`, nor on any
parameter of blueprint `hyp:ml2params`. Hence the constant is a function of `tc.C` alone and,
like it, is sub-polynomial in `δ⁻¹` rather than independent of `δ` — which is what makes the
fixed-scale threshold `hCdens` of `Kakeya.VeryNotSticky.tangentialSlabMult` available. -/
def tangentialSlabDecompConstant (C : NNReal) : NNReal := 100 * C

/-- **Constant in blueprint `lem:ml2slabAxisSeparation`** — retained, since
`Kakeya.VeryNotSticky.slabConeCountConstant` and
`Kakeya.VeryNotSticky.slabDecompFibreConstant` are both built from it (blueprint
`c_{lem:ml2slabAxisSeparation}(C₀)`).

A constant in `(0, 1]`, depending only on the thickness comparison constant `C₀` of (C3)/(C4)
and on the comparison constants of (S2), below which the normals of two distinct slabs of a
slab family are not allowed to approach one another, measured in units of `a/b`. It is small,
hence named `c` and not `C`. The word "axis" in the name is retained from before the
correction to `Kakeya.VeryNotSticky.axisAngle`; the direction compared is the normal
`Kakeya.NonSlab.bodyNormal`. The displayed value is provisional: it is fixed by clause (S4) of
`Kakeya.VeryNotSticky.IsSlabFamily`, and only its range `(0, 1]` and its dependence on `C₀`
alone are used downstream, through
`Kakeya.VeryNotSticky.slabDecompFibreConstant`.

`noncomputable` is forced, not decorative: `NNReal.instInv` is itself noncomputable (it goes
through `Real.instInv`, which is choice-based), so the inversion cannot be compiled. -/
noncomputable def slabAxisSeparationConstant (C₀ : NNReal) : NNReal := (2 ^ 10 * C₀ ^ 4)⁻¹

/-- The separation constant is positive, half of what blueprint `lem:ml2slabAxisSeparation`
requires of it. Positivity is what keeps clause (S4) of
`Kakeya.VeryNotSticky.IsSlabFamily` from being vacuous. -/
lemma slabAxisSeparationConstant_pos {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    0 < slabAxisSeparationConstant C₀ := by
  have hpos : (0 : NNReal) < 2 ^ 10 * C₀ ^ 4 := by
    have hC₀0 : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
    positivity
  simpa [slabAxisSeparationConstant, pos_iff_ne_zero] using hpos.ne'

/-- The separation constant is at most one, the other half of what blueprint
`lem:ml2slabAxisSeparation` requires of it: it records that the separation is a genuine
loss. -/
lemma slabAxisSeparationConstant_le_one {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    slabAxisSeparationConstant C₀ ≤ 1 := by
  rw [slabAxisSeparationConstant, inv_le_one₀]
  · exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hC₀)
  · positivity

/-- **The cone-count constant of the lattice slab cells** — the `δ`-free constant of
clause (S4″) of `Kakeya.VeryNotSticky.IsSlabFamily`.

The refined proof builds the slab cells as a *bounded-overlap cover*, not a tiling: "use a
fixed net of normals and a lattice only in the normal coordinate; the two tangential
directions are not tiled" (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.5057-5059),
and "at a shaded point, the typical-angle property confines all relevant normals to one
`O(θ)`-cap; separation of the normal net and of the one-dimensional lattice therefore leaves
only `O(1)` possible slab labels" (l.1684-1688). The two factors of that `O(1)` are the
`⌈C/c⌉ + 1` lattice translates per net normal and the number of net cells *in the cap*, and
the second factor is why clause (S4″) is **cone-restricted**: over all directions at once the
count is `≍ (b/a)²/κ²`, since the net of normals of l.1677-1678 ranges over every direction. The value carried here is the aperture-over-separation square
`C_{lem:coneDirectionCount} (3 / c_{lem:ml2slabAxisSeparation}(C₀))²`, i.e. the cell count of a
cone of aperture `3 (a/b)` at resolution `c(C₀) (a/b)`; clause (S4″) states the count per unit
of `α/(a/b)`, so the typicality factor `Ctyp` and the tangential `δ^{-τ'}` are *not* in it —
they enter the fibre bound through the aperture `α`, and
`Kakeya.VeryNotSticky.slabDecompFibreConstant` is this constant times `16 Ctyp²`. It carries
no power of `δ` (§J: the source's `O(1)` rendered at an explicit absolute constant,
never `1`). -/
noncomputable def slabConeCountConstant (C₀ : NNReal) : NNReal :=
  NonSlab.coneDirectionCountConstant * (3 / slabAxisSeparationConstant C₀) ^ 2

/-- The cone-count constant is at least `1`: a single slab through the point and inside the
cone must fit under it, and the degenerate singleton family is exactly that case. -/
lemma one_le_slabConeCountConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    1 ≤ slabConeCountConstant C₀ := by
  have hc : slabAxisSeparationConstant C₀ ≤ 1 := slabAxisSeparationConstant_le_one hC₀
  have hcpos : 0 < slabAxisSeparationConstant C₀ := slabAxisSeparationConstant_pos hC₀
  have h1 : (1 : NNReal) ≤ 3 / slabAxisSeparationConstant C₀ := by
    have : (1 : ℝ) ≤ 3 / (slabAxisSeparationConstant C₀ : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hcpos)]
      have : ((slabAxisSeparationConstant C₀ : NNReal) : ℝ) ≤ 1 := by exact_mod_cast hc
      linarith
    exact_mod_cast this
  calc (1 : NNReal) = 1 * 1 ^ 2 := by norm_num
    _ ≤ NonSlab.coneDirectionCountConstant * (3 / slabAxisSeparationConstant C₀) ^ 2 := by
        gcongr
        exact NonSlab.one_le_coneDirectionCountConstant
    _ = slabConeCountConstant C₀ := rfl

/-- **The `δ`-free comparison constant of the aligned anisotropic transport.**

Moved here from `Kakeya.DimensionThree.MainLemma2.TangentialSlabAlign` (where it was
introduced and where every theorem about it still lives) because clauses (A2)/(A2′) of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` are now stated at it, and that structure is
declared in this file. The value is unchanged, byte for byte. -/
def alignedRescaleConstant (C₀ κ : NNReal) : NNReal := 2304 * (3 + κ) * C₀ ^ 4

/-- `1 ≤ alignedRescaleConstant C₀ κ` whenever `1 ≤ C₀` and `1 ≤ κ`. -/
lemma one_le_alignedRescaleConstant {C₀ κ : NNReal} (hC₀ : 1 ≤ C₀) (hκ : 1 ≤ κ) :
    1 ≤ alignedRescaleConstant C₀ κ := by
  have h4 : (1 : NNReal) ≤ C₀ ^ 4 := one_le_pow₀ hC₀
  calc (1 : NNReal) = 1 * 1 * 1 := by norm_num
    _ ≤ 2304 * (3 + κ) * C₀ ^ 4 := by
        gcongr
        · norm_num
        · exact hκ.trans le_add_self
    _ = alignedRescaleConstant C₀ κ := rfl

/-- The comparison constant of `Kakeya.VeryNotSticky.BallData` is below the aligned one, so a
`HasThicknesses` at `bd.C₀` weakens to one at `alignedRescaleConstant bd.C₀ κ`. -/
lemma le_alignedRescaleConstant {C₀ κ : NNReal} (hC₀ : 1 ≤ C₀) (hκ : 1 ≤ κ) :
    C₀ ≤ alignedRescaleConstant C₀ κ := by
  have hC₀0 : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have h4 : C₀ ≤ C₀ ^ 4 := by
    calc C₀ = C₀ ^ 1 := (pow_one C₀).symm
      _ ≤ C₀ ^ 4 := pow_le_pow_right₀ hC₀ (by norm_num)
  have hbig : (1 : NNReal) ≤ 2304 * (3 + κ) := by
    calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 2304 * (3 + κ) := by
          gcongr
          · norm_num
          · exact hκ.trans le_add_self
  calc C₀ ≤ C₀ ^ 4 := h4
    _ = 1 * C₀ ^ 4 := (one_mul _).symm
    _ ≤ 2304 * (3 + κ) * C₀ ^ 4 := by gcongr
    _ = alignedRescaleConstant C₀ κ := rfl

/-- **The comparison constant of the aligned anisotropic transport at a LATTICE cell.**

`Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀` is the constant of the transport attached
to a slab that *is* the normalising ellipsoid about its own `bodyNormal`, at aspect `a/b` and
tangential radius `r₁`. A cell of the refined lattice construction
(`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1677-1688) is none of those three: it is
about a **net** normal `ν`, its tangential radius is `4 r₁` (l.1680, "tangential widths large
enough to contain `B₁`"; `Kakeya.VeryNotSticky.hasThicknesses_of_four_R`), and its aspect is
therefore `(a/b)/4`. Each departure costs the transport a factor, and all three are `δ`-free:

* the net normal costs `2 ratio` in the alignment
  (`Kakeya.VeryNotSticky.lineAngle_defining_normal_le_of_axisAngle_le`), so the alignment
  available against `ν` is `2 (a/b) + 2 ratio = (5/2)(a/b) = 10 ratio` — the `10`;
* the transport is the one that normalises the **doubled** cell, so the cell itself lands in
  `B̄(0, 1/2)` and its bodies' `τ₂`-neighbourhoods still land in `B̄(0,1)` — clause (A1′) for
  *every* `Wd`, at radius `1`, with no clause added anywhere.
  Its radius is `8 r₁`, which moves the profile slot to `(8 r₁, 8 b, 4 a)`, and the body meets
  that only at `8 bd.C₀` — the `8 * C₀`;
* clause (A2′) reads the same alignment slot for the *thickened* body, whose extra tilt is
  `≲ C₀² (a/b)` (obligation R7) — the `4 * C₀ ^ 2`.

It carries **no power of `δ`**: this is the source's `O(1)` rendered at an explicit absolute
constant, never `1` and never `δ^{-τ'}`, which is what keeps
`Kakeya.VeryNotSticky.ktRho2EnclosureConstant` `δ`-free and the fullness clause at `L ≤ 5/3`.
The value is a **producer measurement confined to this one line**: if
the C3-b assembly or R7 needs more, this body is re-cut and no statement text moves. -/
noncomputable def latticeRescaleConstant (C₀ : NNReal) : NNReal :=
  alignedRescaleConstant (8 * C₀) (10 + 4 * C₀ ^ 2)

/-- `1 ≤ latticeRescaleConstant C₀` whenever `1 ≤ C₀`. -/
theorem one_le_latticeRescaleConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    1 ≤ latticeRescaleConstant C₀ := by
  refine one_le_alignedRescaleConstant ?_ ?_
  · calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 8 * C₀ := by gcongr; norm_num
  · calc (1 : NNReal) ≤ 10 := by norm_num
      _ ≤ 10 + 4 * C₀ ^ 2 := le_add_self.trans_eq (add_comm _ _) |>.trans le_rfl

/-- The comparison constant of `Kakeya.VeryNotSticky.BallData` is below the lattice one. -/
theorem le_latticeRescaleConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    C₀ ≤ latticeRescaleConstant C₀ := by
  have h1 : (1 : NNReal) ≤ 8 * C₀ := by
    calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 8 * C₀ := by gcongr; norm_num
  have h2 : (1 : NNReal) ≤ 10 + 4 * C₀ ^ 2 := by
    calc (1 : NNReal) ≤ 10 := by norm_num
      _ ≤ 10 + 4 * C₀ ^ 2 := le_self_add
  calc C₀ ≤ 8 * C₀ := by
        calc C₀ = 1 * C₀ := (one_mul _).symm
          _ ≤ 8 * C₀ := by gcongr; norm_num
    _ ≤ latticeRescaleConstant C₀ := le_alignedRescaleConstant h1 h2

/-- **The move to the lattice pin is a pure weakening of every producer obligation**: the
existing degenerate route produces at `bd.C₀`, weakens to `latticeRescaleConstant bd.C₀` by
`le_alignedRescaleConstant` + `hasThicknesses_mono_const`, and weakens to the new pin by
exactly the same two steps. -/
theorem alignedRescaleConstant_two_le_lattice {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    alignedRescaleConstant C₀ 2 ≤ latticeRescaleConstant C₀ := by
  have hC₀0 : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  rw [latticeRescaleConstant, alignedRescaleConstant, alignedRescaleConstant]
  have hbase : C₀ ^ 4 ≤ (8 * C₀) ^ 4 := by
    gcongr
    calc C₀ = 1 * C₀ := (one_mul _).symm
      _ ≤ 8 * C₀ := by gcongr; norm_num
  have hκ : (3 : NNReal) + 2 ≤ 3 + (10 + 4 * C₀ ^ 2) := by
    gcongr
    calc (2 : NNReal) ≤ 10 := by norm_num
      _ ≤ 10 + 4 * C₀ ^ 2 := le_self_add
  gcongr

/-- The constant the lattice route's own (A2) producer delivers is below the pin. -/
theorem route_B1_le_lattice {C₀ : NNReal} (_hC₀ : 1 ≤ C₀) :
    alignedRescaleConstant (8 * C₀) 6 ≤ latticeRescaleConstant C₀ := by
  rw [latticeRescaleConstant, alignedRescaleConstant, alignedRescaleConstant]
  have hκ : (3 : NNReal) + 6 ≤ 3 + (10 + 4 * C₀ ^ 2) := by
    gcongr
    exact le_trans (by norm_num) (le_self_add : (10 : NNReal) ≤ 10 + 4 * C₀ ^ 2)
  gcongr

/-- **`HasThicknesses` weakens with the comparison constant.**

Moved here from `Kakeya.DimensionThree.MainLemma2.TangentialSlabAlign`; it is the step that
lets a producer at `bd.C₀` meet clauses (A2)/(A2′) at
`Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀`. -/
theorem hasThicknesses_mono_const {m : ℕ} {X : Set (EuclideanSpace ℝ (Fin 3))} {C C' : NNReal}
    {t : Fin m → ℝ} (hC : 0 < C) (hCC' : C ≤ C') (ht : ∀ k, 0 ≤ t k)
    (h : Kakeya.HasThicknesses X C t) : Kakeya.HasThicknesses X C' t := by
  have hC' : (0:ℝ) < (C' : ℝ) := lt_of_lt_of_le (by exact_mod_cast hC) (by exact_mod_cast hCC')
  have hC0 : (0:ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hle : ((C : ℝ)) ≤ (C' : ℝ) := by exact_mod_cast hCC'
  intro k
  refine ⟨le_trans ?_ (h k).1, le_trans (h k).2 ?_⟩
  · exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ hC' hC0).2 hle) (ht k)
  · exact mul_le_mul_of_nonneg_right hle (ht k)

/-- **Slab family for `(B, θ)`** (blueprint `hyp:ml2tangentialSlabFamily`).

`𝕊` is a finite set of slabs `S ⊆ B` decomposing the family `𝕎''_B` (here `Wb'`, an arbitrary
`Finset` of body indices — its one instantiation is `ta.sel`, the index set on which the
`c`-refinement `(𝕎''_B, Y_{𝕎''_B})` of `Kakeya.VeryNotSticky.TypicalAngleData` is recorded)
according to the normal direction, at angular resolution `θ`:

* (S2) each slab has affine thicknesses `∼ (r₁, r₁, (a/b) r₁)`, with the constant `bd.C₀` of
  Configuration `hyp:ml2setup`, and **meets** the ball `B`;
* (S3) writing `𝕎''_S = {W ∈ 𝕎''_B : W ⊆ S and ∠(n(W), n(S)) ≤ 2θ}` with `n(·)` the normal of
  blueprint `def:ml2bodyNormal` (`Kakeya.NonSlab.bodyNormal`, the rank-`2` axis of
  `outerPrism`), the subfamilies `𝕎''_S` partition `𝕎''_B`. This is rendered as: every
  `W ∈ 𝕎''_B` lies in `𝕎''_S` for exactly one `S ∈ 𝕊`, which is precisely
  `𝕎''_B = ⨆_{S ∈ 𝕊} 𝕎''_S`. The angle is read at `2θ` and not at `θ`: GWZ (28), `gwz.txt` l.774-776, define `P_S` through `∠(T_P, T_S) ≤ θ` and add that
  the plane `T_P` "is defined up to accuracy `θ`", so the clause is a `θ`-accuracy statement
  carrying an absolute constant. At constant `1` the Lean clause excluded normals at angle in
  `(1, π/2]` that the source admits; at `2θ` it is void when `θ = 1` (`a = b`), since
  `axisAngle` ranges over `[0, π/2]` and `2 > π/2` — exactly as GWZ's clause is void there;
* (S3′) each body's normal is within `2 (a/b)` of its own slab's normal — the slab's own
  angular width, which is what the anisotropic transport of
  `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` needs and what the refined assignment
  ("the first slab whose normal is closest to its short John axis and whose normal interval
  contains it", `260115_kakeyadetailedproofv3_revised_detailed.tex` l.1681-1682) gives once
  the net of normals is taken at mesh `κ (a/b)`;
* (S4″) **bounded overlap, cone-restricted**: the slabs whose `C₀ a`-thickening contains a
  given point and whose normal lies within `α` of a given direction number at most
  `slabConeCountConstant(C₀) · (α/(a/b) + 1)²`.

**Why (S1) is gone and (S4) is (S4″).** The refined proof's slab cells are *overlapping
lattice slabs* of full tangential extent: "use a fixed net of normals and a lattice only in
the normal coordinate; the two tangential directions are not tiled" (l.5057-5059), each cell
of normal width `Cθ` on a lattice of spacing `cθ`, with "two fixed tangential widths large
enough to contain `B₁`" (l.1680). Consecutive translates therefore overlap in width
`(C − c) θ` and are *parallel*, so the old (S1) (pairwise `IsEssentiallyDistinct`) and the old
(S4) (normals of overlapping slabs `c(C₀) (a/b)`-separated) are both **false** for the family
the source builds. What the source proves instead, and all that its counting uses, is the
`O(1)` label bound at a point: "at a shaded point, the typical-angle property confines all
relevant normals to one `O(θ)`-cap; separation of the normal net and of the one-dimensional
lattice therefore leaves only `O(1)` possible slab labels" (l.1684-1688). That is (S4″), at
the explicit absolute constant `Kakeya.VeryNotSticky.slabConeCountConstant`, restricted to the
cone the consumer reads it in. Its single
consumer, `Kakeya.VeryNotSticky.tangentialSlabFibreCount`, keeps its statement byte for byte:
under the tangential guard `θ < δ^{-τ'} (a/b)` the factor `(θ/(a/b))²` is below `δ^{-2τ'}`,
which is exactly the shape the count had before. (S1) had **zero** consumers in the tree and
is simply deleted.

Both (S3) and (S3′) are stated through `Kakeya.VeryNotSticky.axisAngle`, which since the
correction recorded in its own docstring reads `Kakeya.NonSlab.bodyNormal` and not
`Kakeya.NonSlab.bodyAxis`. The name `axisAngle`, and the names `slabAxisSeparation` and
`slabAxisSeparationConstant`, are retained from before that correction; the direction they
compare is the normal.

The existence of such a family is a maximality argument that the blueprint does *not* prove,
so `𝕊` is carried as data by `Kakeya.VeryNotSticky.tangentialSlabDecomp` rather than produced
by it; the blueprint statement of `lem:ml2tangentialSlabDecomp` likewise begins "let `𝕊` be a
slab family for `(B, θ)`".

**Why `Set` together with a `Set.Finite` field and not `Finset`.** Every use of `𝕊` in (S3)
and (S4″) treats it as finite, so `Finset` would be the canonical Mathlib type and would remove
the `finite` field — but `ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))` carries no
`DecidableEq` instance, and none is derivable: a `ConvexSpaceBody` is a set together with
proofs, so equality of two of them is equality of subsets of `ℝ³`, which is not decidable.
Introducing one by `Classical.dec` would make `𝕊` a `Finset` in a noncomputable and
instance-fragile way, and the `Finset` membership `S ∈ 𝕊` occurring in
`Kakeya.VeryNotSticky.IsDenseSlab.mem` would then depend on that choice of instance. The
`Set` + `Set.Finite` pair is the stable form.

**Why the separation is a clause and not a lemma.** Blueprint `lem:ml2slabAxisSeparation`
presents (S4) as a *consequence* of (S1) and (S2), by the picture "two slabs of thicknesses
`∼ (r₁, r₁, (a/b) r₁)` inside a ball of radius `∼ r₁` whose directions make an angle `≪ a/b`
overlap in more than half of either one, contradicting essential disjointness". That
derivation is false, and not only in the relaxed Lean setting: a ball of radius `r₁` holds
`∼ b/a` disjoint *parallel translates* of one `r₁ × r₁ × (a/b) r₁` box, and translates have
equal normals — and equal axes — so (S1)–(S3) hold — take `Wb' = ∅` to make (S3) vacuous —
while the angle is `0`. Adding a common-point hypothesis does not repair it either: two
coplanar boxes of side `r₁/C₀` inside a ball of radius `r₁` may meet in a single boundary
point with equal normals, since at the comparison constants of (S2) the profile only forces
`τ₀(S), τ₁(S) ∈ [r₁/C₀, C₀ r₁]`.

The counterexamples above are stated for the normal, which is the direction (S4) now compares.
The statement was equally false for the long axis, and for one further reason: two boxes
sharing a long axis and rotated about it by an angle `∼ 1` are essentially disjoint with equal
*axes*, while their *normals* are separated by that rotation. That is one respect in which
the normal is the better-behaved direction here, and part of why it is the one (S4) compares.

What is true is that the family `𝕊` produced by the maximality argument of the blueprint — the
one that bins the bodies of `𝕎''_B` by direction at resolution `θ ≥ a/b` — has separated
normals by construction. Since the re-cut of (S4) to (S4″) the
projection is `Kakeya.VeryNotSticky.slabConeCount`, so that
`Kakeya.VeryNotSticky.tangentialSlabFibreCount` still names its input.

**A deliberate divergence: "slab" is relaxed to a thickness profile.** Blueprint
`hyp:ml2tangentialSlabFamily` asks for a finite family of *slabs* in the sense of
`def:slab`, whose Lean forms are `Kakeya.Slab` of `Kakeya/DimensionThree/Slab/Basic.lean` and
`Kakeya.Prism3D` of `Kakeya/DimensionThree/Prism.lean`. Those types pin the shape of `S`
exactly — a `Prism3D` *is* an axis-aligned box of prescribed half-widths — whereas every use the
tangential argument makes of a slab (its three thicknesses, its normal
`Kakeya.NonSlab.bodyNormal`, its containment in `B`) is a comparison up to the constant
`bd.C₀` of (C3)/(C4). So (S2) is stated as
`HasThicknesses S.carrier bd.C₀ ![r₁, r₁, (a/b) r₁]`, the same thickness-profile idiom the
rest of this development uses, and `S` is an arbitrary `ConvexSpaceBody`.

The relaxation is strict: a `HasThicknesses` body need not be a slab, so (S1)–(S3) are
*weaker* than the blueprint's. With the separation moved into (S4) this no longer makes any
statement of this file refutable — a weaker hypothesis only weakens the lemmas that consume it
— but it does leave a satisfiability obligation on whoever eventually constructs `𝕊`: the
family must consist of bodies for which (S3) and (S4) both hold, the two clauses jointly
constraining the one direction `n(S)` that both read.

Since the correction to `Kakeya.VeryNotSticky.axisAngle` that obligation is *lighter* than it
was. For a profile `∼ (r₁, r₁, (a/b) r₁)` the two long thicknesses are comparable, so the
rank-`0` direction that `Kakeya.NonSlab.bodyAxis` reads off `outerPrism` is not pinned by the
geometry of `S` at all — the outer prism selects one frame out of a circle of admissible ones
— and the old reading of (S3)/(S4) constrained a direction the hypotheses did not determine.
The short thickness, by contrast, is separated from the two long ones as soon as
`C₀² (a/b) < 1`, so the rank-`2` direction `n(S)` that `Kakeya.NonSlab.bodyNormal` reads off
*is* constrained by the geometry of `S`, to the extent of that gap. What remains owed is only
that the directions so constrained satisfy (S3) and (S4). Restoring
`Kakeya.Slab`/`Kakeya.Prism3D` in (S2), or carrying the normal of each slab as data alongside
`𝕊`, would discharge it at the cost of a refactor of every consumer in this file. -/
structure IsSlabFamily (cfg : VeryNotSticky.{u}) {bd : BallData cfg} (B : bd.bι)
    (Wb' : Finset bd.ω) (θ : NNReal)
    (𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))))
    (slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop where
  /-- the family is finite -/
  finite : 𝕊.Finite
  /-- (S2), first half: each slab has affine thicknesses `∼ (r₁, r₁, (a/b) r₁)` -/
  S2_thicknesses : ∀ S ∈ 𝕊, HasThicknesses S.carrier bd.C₀
    ![(cfg.r₁ : ℝ), (cfg.r₁ : ℝ), ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)]
  /-- (S2), second half, **re-cut against the refined source**: each slab *meets* the ball
  `B`, rather than lying inside it.

  The refined construction gives the slab cells "two fixed tangential widths large enough to
  contain `B₁`" (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1680), so a cell is not
  contained in `B̄(ctr B, r₁)` — nor in any fixed multiple of it. What is true, and what the
  assignment gives, is that a retained cell carries at least one plank of the ball, hence
  meets the ball. This is the weakest positional clause the source supports, and it is what
  the family needs to be *about* `B` at all.

  The clause it replaces was `S.carrier ⊆ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)`, and that
  containment is **compiler-refuted for any family with translates**: for a normalising
  ellipsoid `Kakeya.VeryNotSticky.center_eq_of_generalSlab_subset_closedBall` shows the
  containment at radius `r₁` forces the slab's centre to be `bd.ctr B`, so the family is
  concentric and admits none of the "`∼ b/a` parallel translates per direction" the source's
  lattice produces. Weakening it to `2 r₁` buys translates but keeps
  a containment the source does not have; the intersection form drops it altogether. Clause
  (A1) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` — the only consumer of the old
  containment — is correspondingly re-read on the *bodies*, which are inside the ball by
  `Kakeya.VeryNotSticky.BallData.bodies_subset_ball`. -/
  S2_ball_meets : ∀ S ∈ 𝕊,
    (S.carrier ∩ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)).Nonempty
  /-- (S3) each body of `𝕎''_B` is *assigned* to a slab of `𝕊` containing it, with the
  normal angle at `2θ` — GWZ's "up to accuracy `θ`" with an absolute constant. The fibres `𝕎''_S = slabOf⁻¹(S)` then partition `𝕎''_B` by construction,
  which is GWZ's `𝕎''_B = ⊔_S 𝕎''_S` (l.2350) read as an assignment: the filter sets of (28)
  need not be literally disjoint for a maximal essentially distinct family, so the earlier
  `∃!` was a strictly stronger demand than the source makes. -/
  S3 : ∀ j ∈ Wb', slabOf j ∈ 𝕊 ∧
    (bd.Wb j).carrier ⊆ (slabOf j).carrier ∧ axisAngle (bd.Wb j) (slabOf j) ≤ 2 * (θ : ℝ)
  /-- (S3′) each body of `𝕎''_B` has its normal within `2 (a/b)` of the normal of **its own
  slab** — the slab's own angular width, not the typical angle `θ`.

  This is what makes GWZ's "converts `𝕎''_S` to a set `𝕋̃` of `ρ₂`-tubes" (`gwz.txt`
  l.2374-2375) true: the anisotropic transport stretches the slab normal by `b/(a r₁)` and the
  plane by `1/r₁`, so a tilt of `s` costs a factor `1 + s b/a` in the rank-`1` thickness of the
  image (`Kakeya.VeryNotSticky.thickness_one_aniRescale_image_le_of_aligned`), which is
  `δ`-free exactly when `s ≲ a/b`. At `θ ≤ δ^{-τ'} (a/b)` — the tangential guard — clause (S3)
  is weaker by exactly `δ^{-τ'}` (`Kakeya.VeryNotSticky.tilt_gap_is_delta_pow_tau'`). At
  `a = b` the two clauses coincide (`Kakeya.VeryNotSticky.typicalAngle_eq_one_of_a_eq_b`), so
  the degenerate route pays nothing.

  It is **produced, not assumed**, by the refined assignment: the normal net has mesh
  `κ (a/b)` and a plank is assigned to "the first slab whose normal is closest to its short
  John axis and whose normal interval contains it"
  (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1681-1682). The sub-class count that
  the finer mesh costs is `(δ^{-τ'}/κ)²`, which is the existing
  `Kakeya.VeryNotSticky.slabDecompFibreConstant` with `κ^{-2}` absorbed — a `δ`-free constant,
  since `Kakeya.VeryNotSticky.IsSlabDecompMultConstant` is a predicate on `Cμ`. -/
  S3_ratio : ∀ j ∈ Wb',
    axisAngle (bd.Wb j) (slabOf j) ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ)
  /-- (S4″) **the bounded-overlap count of the source, cone-restricted** (refined
  l.1677-1689: a `cθ`-net of normals, a lattice of spacing `cθ` in the normal coordinate only,
  width `Cθ`, so a point lies in `⌈C/c⌉+1` slabs per net normal): the slabs whose
  `C₀ a`-thickening contains `x` and whose normal lies within `α` of `v` number at most a
  `δ`-free constant times the number of net cells in the `α`-cone at resolution `a/b`.
  Consumed by `Kakeya.VeryNotSticky.tangentialSlabFibreCount` at `α = 3 Ctyp θ`; replaces
  (S4′), which is false for parallel lattice translates.

  **Why the count is cone-restricted and not over the whole family**. The refined normal net is "a fixed `cθ`-net of
  unoriented normal directions" over *all* directions
  (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1677-1678), so at mesh `κ (a/b)` a
  point lies in `≍ (b/a)²/κ²` slabs — one `O(1)` lattice layer per direction — and `b/a` is up
  to `δ^{-(1-exscal)}`, not `δ^{-O(τ')}`. An unrestricted count at a `δ`-free constant times
  `(θ/(a/b))²` is therefore **false for the family the source builds**. What is true, and all
  the source's counting uses, is the count *inside the cone* the typical-angle property
  confines the relevant normals to: "at a shaded point, the typical-angle property confines
  all relevant normals to one `O(θ)`-cap; separation of the normal net and of the
  one-dimensional lattice therefore leaves only `O(1)` possible slab labels" (l.1684-1688).
  The sole consumer, `Kakeya.VeryNotSticky.tangentialSlabFibreCount`, reads it at exactly that
  cone — `α = 3 Ctyp θ` about the normal of a body shading `x`, which is what
  `Kakeya.VeryNotSticky.TypicalAngleData.hangle` supplies — so the restriction costs the
  consumer nothing and is what makes the clause satisfiable by the lattice family.

  **The radius of the thickening.** It is `C₀ a`, the same one (S4′) carried, and for the same
  reason: a shaded point of a body of `𝕎''_S` lies in `N_{τ₂(W)}(W)` by
  `Kakeya.ThinCase.ThinBall.W_le_cthickening`, and `τ₂(W) ≤ C₀ a` by (C4)
  `Kakeya.VeryNotSticky.BallData.bodies_thickness`, so this is exactly the radius the single
  consumer's call site can manufacture.

  **The shape of the bound.** `(α/(a/b) + 1)²` and not `(α/(a/b))²`: the count of net cells in
  a cone of aperture `α` at resolution `a/b` is `≍ (α/(a/b) + 1)²`, and the `+1` is what keeps
  the clause true at apertures below the mesh — in particular at `α = 0`, where one slab may
  still contain `x`. `Set.ncard` because the counted object is a `Set` of slabs, matching the
  conclusion of `Kakeya.VeryNotSticky.tangentialSlabFibreCount`. -/
  S4'' : ∀ (x v : EuclideanSpace ℝ (Fin 3)) (α : ℝ), 0 ≤ α →
    (({S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
        NonSlab.lineAngle (bodyNormal S) v ≤ α}.ncard : ℕ) : ℝ) ≤
      (slabConeCountConstant bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2

/-- **Projection of the defining fields.** Clause (S3) of a slab family reads the normal angle
at `2θ` — GWZ (28) "up to accuracy `θ`" with an absolute constant — and not at `θ`. The statement
is the licensed text of the clause spelled out and the proof is its projection, so this
declaration fails to elaborate if the clause changes in either direction. -/
theorem IsSlabFamily.S3_two_theta {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι}
    {Wb' : Finset bd.ω} {θ : NNReal} {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) :
    ∀ j ∈ Wb', slabOf j ∈ 𝕊 ∧
      (bd.Wb j).carrier ⊆ (slabOf j).carrier ∧ axisAngle (bd.Wb j) (slabOf j) ≤ 2 * (θ : ℝ) :=
  hS.S3

/-- **Tripwire for the re-cut (S3′)/R1.** The alignment clause reads the *slab's own angular
width* `2 (a/b)`, not the typical angle. The statement is the licensed text spelled out and the
proof is its projection, so this declaration fails to elaborate if the clause moves. -/
theorem IsSlabFamily.S3_ratio_two_ab {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι}
    {Wb' : Finset bd.ω} {θ : NNReal} {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) :
    ∀ j ∈ Wb', axisAngle (bd.Wb j) (slabOf j) ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ) :=
  hS.S3_ratio

/-- **Tripwire for the re-cut (S2)-ball/R11.** The positional clause of a slab family is
*intersection with* the ball, not containment in it. -/
theorem IsSlabFamily.S2_ball_meets_r₁ {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι}
    {Wb' : Finset bd.ω} {θ : NNReal} {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) :
    ∀ S ∈ 𝕊, (S.carrier ∩ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)).Nonempty :=
  hS.S2_ball_meets

/-- **Tripwire for the re-cut (S4″).** The overlap clause of a slab family is a
*cone-restricted point count* of thickenings at an explicit `δ`-free constant — not a pairwise
normal separation, and not the unrestricted point count which fails for the source's family. -/
theorem IsSlabFamily.S4''_cone_count {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι}
    {Wb' : Finset bd.ω} {θ : NNReal} {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) :
    ∀ (x v : EuclideanSpace ℝ (Fin 3)) (α : ℝ), 0 ≤ α →
      (({S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) v ≤ α}.ncard : ℕ) : ℝ) ≤
        (slabConeCountConstant bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 :=
  hS.S4''

/-- **A dense slab of the family `𝕊`, with its subfamily `𝕎''_S`** (blueprint
`tangentialSdens`, the output of `lem:ml2tangentialSlabDecomp`).

`S` is one of the slabs of the family `𝕊` for `(B, ta.θ)`, and `Wd` indexes the subfamily
`𝕎''_S = {W ∈ 𝕎''_B : W ⊆ S and ∠(n(W), n(S)) ≤ 2θ}` of blueprint `tangentialWWS`, with `n(·)`
the normal of blueprint `def:ml2bodyNormal` (`Kakeya.NonSlab.bodyNormal`). The eight
clauses are exactly what `Kakeya.VeryNotSticky.tangentialSlabDecomp` returns about the pair
`(S, Wd)` and exactly what `Kakeya.VeryNotSticky.tangentialSlabMult` consumes about it; they
are bundled because the rescaling hypothesis of `Kakeya.VeryNotSticky.goalMult_of_theta_lt`
has to be quantified over *precisely* the pairs `(S, Wd)` the decomposition can produce, and
listing them one by one there had already dropped the angle clause, which made that
hypothesis unsatisfiable.

**The index set is `ta.sel`, not `𝕎'_B.**` Blueprint `hyp:ml2tangentialSlabFamily`(S3)
decomposes the `c`-refinement `𝕎''_B`, and the Lean record of that refinement,
`Kakeya.VeryNotSticky.TypicalAngleData`, carries it on `ta.sel` only: `ta.hrefine`,
`ta.htyp`, `ta.hfull` and `ta.hconst` all live there, and `ta.YW` carries no information
whatsoever off `ta.sel`. With `subset : Wd ⊆ (tc.thinBall hB).bodies'` the two conclusions of
`tangentialSlabDecomp`, both stated about `ta.YW` on `Wd`, would therefore say nothing about
the factoring bodies, and `Kakeya.VeryNotSticky.tangentialSlabMult` would be *false*: taking
all `ta.YW j` to be one and the same fully shaded body makes `λ(Wd, ta.YW) = 1` while
`μ(Wd, ta.YW) = |Wd|`, which (A3) bounds only by `≈ δ^{-3ϱ} ρ₂^{-2}`. With `Wd ⊆ ta.sel`,
`ta.hrefine` pins `(ta.YW j).toConvexSpaceBody` to the outer body
`((tc.thinBall hB).W j).toConvexSpaceBody`, which the enlargement sandwich
`Kakeya.ThinCase.ThinBall.Wb_le_W` / `Kakeya.ThinCase.ThinBall.W_le_cthickening` in turn pins
between the geometric body `bd.Wb j` and its closed `τ₂(bd.Wb j)`-neighbourhood; the
counterexample disappears. It is *not* pinned to `bd.Wb j` itself — the corrected factoring
proposition returns genuine enlargements — but the sandwich is two-sided and tight at the
scale of the body, so every geometric clause below still bears on the shaded family, with the
one-factor-of-`2` losses recorded at their use.

The angle clause is what makes the anisotropic rescaling of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` turn the bodies of `𝕎''_S` into `ρ₂`-tubes: a
body of thicknesses `∼ (r₁, b, a)` sitting in a slab of thicknesses `∼ (r₁, r₁, (a/b) r₁)`
with its *thin* direction at angle up to `π/2` from `n(S)` is *not* carried to a tube by the
map that stretches the short axis of `S` by `∼ b/a`. Without the clause, (A2) fails and the
hypothesis is vacuous. Note that this is exactly what the clause says now that it is read on
the normals: `∠(n(W), n(S)) ≤ 2θ` says the thin direction of `W` is that of `S` up to `2θ`
(the `θ`-accuracy of GWZ (28) with an absolute constant, at `θ = 1`,
i.e. `a = b`, the clause is void, as GWZ's is), which is the alignment the stretch needs. On
the old reading, `∠(v(W), v(S)) ≤ θ`, it said instead that the two *long* directions agree,
which in `ℝ³` leaves the thin direction of `W` free to rotate about `v(S)` and does not give
(A2).

The density clause `dense` is what makes the name honest, and it is why the conclusion of
`Kakeya.VeryNotSticky.tangentialSlabDecomp` is a two-fold and not a three-fold conjunction: it
is blueprint `tangentialDensityChain`,
`δ^{8η} ≤ tangentialSlabDecompConstant tc.C · λ(𝕎''_S, Y_{𝕎''_S})`, consumed at exactly one
place, blueprint `lem:ml2tangentialSlabFull`. Both corrections against the earlier
`δ^{3η} ≤ tc.C · λ` are forced: the exponent is `8η` because the chain has *two* independent
factors, `δ^{6η}` from (T2) at the `tb` index `2η` (F8) and `δ^{2η}` from `ta.hc`, and the
constant is `100 · tc.C` because the slab selection of blueprint
`lem:ml2tangentialDenseSlabs` keeps only the slabs of density at least a hundredth of
`λ(𝕎''_B, Y_{𝕎''_B})`. Being a constant and not a power of `δ` it is carried by name and
discharged where the clause is consumed, by `SlabMultKT.densityConstant`. -/
structure IsDenseSlab (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ')
    (𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))))
    (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω) : Prop where
  /-- the slab belongs to the assumed family `𝕊` -/
  mem : S ∈ 𝕊
  /-- `𝕎''_S` is a subfamily of the index set `𝕊*` on which `ta.YW` is a refinement -/
  subset : Wd ⊆ ta.sel
  /-- `𝕎''_S ≠ ∅`, part of blueprint `tangentialSdens` -/
  nonempty : Wd.Nonempty
  /-- (S2) the slab has affine thicknesses `∼ (r₁, r₁, (a/b) r₁)` -/
  thicknesses : HasThicknesses S.carrier bd.C₀
    ![(cfg.r₁ : ℝ), (cfg.r₁ : ℝ), ((cfg.a / cfg.b : NNReal) : ℝ) * (cfg.r₁ : ℝ)]
  /-- (S2) the slab **meets** the ball `B`, in lockstep with clause (S2)-ball of
  `Kakeya.VeryNotSticky.IsSlabFamily`; see there for why the containment form is not what the
  refined source's lattice slab cells satisfy. -/
  ball_meets : (S.carrier ∩ Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)).Nonempty
  /-- every body of `𝕎''_S` lies in the slab -/
  bodies_subset : ∀ j ∈ Wd, (bd.Wb j).carrier ⊆ S.carrier
  /-- every body of `𝕎''_S` has its normal within `2θ` of the normal of the slab — in
  lockstep with clause (S3) of `Kakeya.VeryNotSticky.IsSlabFamily` and with
  `Kakeya.VeryNotSticky.slabBodies` -/
  angle : ∀ j ∈ Wd, axisAngle (bd.Wb j) S ≤ 2 * ((ta.θ : NNReal) : ℝ)
  /-- every body of `𝕎''_S` has its normal within `2 (a/b)` of the normal of the slab, in
  lockstep with clause (S3′) of `Kakeya.VeryNotSticky.IsSlabFamily`. This is the alignment that
  `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_body_of_denseSlab` consumes to produce
  clause (A2) at the `δ`-free `Kakeya.VeryNotSticky.alignedRescaleConstant`. -/
  angle_ratio : ∀ j ∈ Wd, axisAngle (bd.Wb j) S ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ)
  /-- the density of the selected slab, blueprint `tangentialDensityChain`.

  The exponent is `8η`: it is `δ^{2η}` from `ta.hc` times the `δ^{6η}` of (T2),
  `Kakeya.ThinCase.ThinBall.fullness_bodies` at `δ^{3η}` in its own index `η`, read by
  `Kakeya.VeryNotSticky.ThinConfig.tb` at the index `2 · cfg.η` — the (C5) exponent in the density clause. What follows it is
  `Kakeya.VeryNotSticky.SlabMultKT.fullness_threshold`, which correspondingly reads `9η ≤ η₁` —
  a bound on the Katz–Tao exponent threshold `η₁`, chosen after `η`, not on `η`. -/
  dense : (cfg.δ : ENNReal) ^ (8 * cfg.η) ≤
    ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) *
      (ShadedBody.fullness Wd ta.YW : ENNReal)

/-- **Projection of the defining fields.** The angle clause of a dense slab reads
the normal angle at `2θ`, in lockstep with clause (S3) of `Kakeya.VeryNotSticky.IsSlabFamily`.
The proof is the projection, so this declaration fails to elaborate if the clause changes. -/
theorem IsDenseSlab.angle_two_theta {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {Wd : Finset bd.ω}
    (h : IsDenseSlab cfg ta 𝕊 S Wd) :
    ∀ j ∈ Wd, axisAngle (bd.Wb j) S ≤ 2 * ((ta.θ : NNReal) : ℝ) :=
  h.angle

/-- **Tripwire for the re-cut (S3′)/R2 (lockstep item).** The `a/b` alignment clause of a dense
slab, spelled out; the proof is its projection. -/
theorem IsDenseSlab.angle_ratio_two_ab {cfg : VeryNotSticky.{u}} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    {ta : TypicalAngleData cfg tc hB τ'}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {Wd : Finset bd.ω}
    (h : IsDenseSlab cfg ta 𝕊 S Wd) :
    ∀ j ∈ Wd, axisAngle (bd.Wb j) S ≤ 2 * ((cfg.a / cfg.b : NNReal) : ℝ) :=
  h.angle_ratio

/-- **The anisotropic slab rescaling** (blueprint `hyp:ml2anisotropicSlabRescale`, together
with the `Δ_max` transport of blueprint `lem:ml2tangentialDeltamaxTransport`).

`L` is the linear change of variables carrying the slab `S` to the unit ball: it rescales the
two axes of length `∼ r₁` to unit length and stretches the short axis, of length
`∼ (a/b) r₁`, by `∼ b/a`. The blueprint has the isotropic homothety toolkit but not the
anisotropic comparison, so its three effects are *assumed*:

* (A1) `L(S) ⊆ B₁`, whence also `L(W) ⊆ B₁` for every `W ∈ 𝕎''_S`, since `W ⊆ S`;
* (A1') `L(N_{τ₂(W)}(W)) ⊆ B₁` for every `W ∈ 𝕎''_S`, where `N_r` is the closed
  `r`-neighbourhood and `τ₂(W) = W.scale` is the shortest affine thickness of `W`;
* (A2) `L(W)` is a `ρ₂`-tube up to the thickness constant `bd.C₀`, for every `W ∈ 𝕎''_S`;
* (A2') `L(N_{τ₂(W)}(W))` is a `ρ₂`-tube up to the *doubled* constant `2 bd.C₀`;
* (A3) the transport distorts `Δ_max` by at most `CΔ`: any realisation of the image family
  `L(𝕎''_S)` as convex bodies is Katz–Tao at `CΔ δ^{-2ϱ}`.

**Why the two primed clauses.** The family that carries the shading is not `bd.Wb` but the
outer family `𝕎'_B` of the corrected factoring proposition, whose bodies
`((tc.thinBall hB).W j).toConvexSpaceBody` are genuine *enlargements* of the geometric bodies:
`Kakeya.ThinCase.ThinBall.Wb_le_W` and `Kakeya.ThinCase.ThinBall.W_le_cthickening` pin them
between `bd.Wb j` and `N_{τ₂(bd.Wb j)}(bd.Wb j)` and nothing more. An enlarged carrier need
not lie in the slab `S` at all, so (A1) says nothing about it, and thicknesses are not
monotone, so neither does (A2). The primed clauses are the same two assertions made about the
*outer* end of that sandwich, which is a set built from `bd.Wb` alone; squeezing gives both
assertions for the enlarged carriers, at the cost of the factor `2` in the thickness constant.
That factor is exactly the one `Kakeya.ThinCase.ThinBall.hasThicknesses_W` charges in the
original coordinates, and it is the same loss the slab case absorbs into
`Kakeya.VeryNotSticky.slabInputsConstant`; it is charged here to
`Kakeya.VeryNotSticky.KTRho2ScaleData`, which is stated at comparison constant `2 bd.C₀`.

Neither primed clause is a new geometric demand on `L`: a map normalising `S` to the unit ball
carries `N_{τ₂(W)}(W)` — a set of affine thicknesses `∼ (r₁, b, a)`, by
`ConvexSpaceBody.hasThicknesses_cthickening`, and contained in `N_{τ₂(W)}(S)` — to a body of
thicknesses `∼ (1, ρ₂, ρ₂)` inside a fixed multiple of `B₁`, exactly as it does `W` itself.
The geometric clauses (A1)–(A3) are kept unprimed and unchanged: they are what
`Kakeya.VeryNotSticky.slabCard` reads, and that lemma counts the *index set* `Wd` and is
therefore free to do so against the geometric bodies.

Clause (A3) is blueprint `tangentialDeltamaxTransport`, and it is what gives the parameter
`CΔ` content: without it `CΔ` would occur only in its own threshold
`tangentialDeltamaxThreshold` and could be taken to be `1`. Its bound `CΔ δ^{-2ϱ}` is the
product of the three factors of blueprint `def:ml2tangentialSlabDeltamaxConstant` — the `⪅`
constant of `factmaxmod2` at bias `ϱ`, the distortion of the transport itself, and the square
of the absolute constant of `def:tubeCountFromDeltamaxConstant` — against the biased maximal
density `Δ_max(𝕎''_S) ≤ Δ_max(𝕎_B)` that Lemma 9.2 (`lemmafactmaxbias`) supplies per ball.
GWZ (83) at `U = B` reads `Δ_max(𝕎_B) ≲ (|W|/|B|)^{-ϱ}` with `|W|/|B| ∼ ab/r₁² ≥ (δ/r₁)²`,
so the supply is `(δ/r₁)^{-2ϱ} = δ^{-2ϱ(1-exscal)}` up to a `δ`-free constant — strictly
above `δ^{-ϱ}` whenever `exscal < 1/2` (`CaseParams.scale`) and at most `δ^{-2ϱ}`. It is what
clause (C4), `Kakeya.VeryNotSticky.BallData.bodies_antiClustering`, records as
`Cbias δ^{-2ϱ}`, and it reaches `L(𝕎''_S)` unchanged, `Δ_max` being monotone in the family
and invariant under affine equivalences. An earlier version budgeted (A3) at `CΔ δ^{-ϱ}`
against a misreading `Δ_max(𝕎_B) ⪅ δ^{-ϱ}` of (83), which no `BallData` produced by Lemma 9.2
can meet (its constant is `≥ 2`); the estimate therefore uses the exponent `2ϱ` and the half-exponent threshold `SlabPackage.CΔ_le` to `CΔ ≤ δ^{-ϱ/2}`, so that
`Kakeya.VeryNotSticky.slabKatzTao` and `Kakeya.VeryNotSticky.slabCard` still close at
`δ^{-3ϱ}`. Being a constant and not a power of `δ`, `CΔ` is discharged by the fixed-scale
threshold `SlabPackage.CΔ_le` and never by the exponent budget.

(A3) is stated by quantifying over the realisations `V` of `L(𝕎''_S)` as a family of convex
bodies rather than by naming one, because `ConvexSpaceBody` carries convexity, compactness and
interior data that the image of an affine equivalence does not come with for free in Lean;
`Δ_max` depends on `V` only through the carriers, which the hypothesis pins down. -/
structure IsAnisotropicSlabRescale (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (Cmp CΔ : NNReal) : Prop where
  /-- (A1) each body of `𝕎''_S` is carried into the unit ball.

  **Re-cut from `L '' S.carrier ⊆ B̄(0,1)`** in lockstep with the (S2)-ball re-cut of
  `Kakeya.VeryNotSticky.IsSlabFamily`: the refined source's slab cells have "two fixed
  tangential widths large enough to contain `B₁`"
  (`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1680), so no normalisation carries the
  *cell* into a fixed ball at a `δ`-free cost; what the transport does carry into `B̄(0,1)` are
  the *bodies*, which lie in the ball `B` by
  `Kakeya.VeryNotSticky.BallData.bodies_subset_ball`. Every consumer of the old clause used it
  only through `Set.image_mono` composed with `IsDenseSlab.bodies_subset`, i.e. only at the
  bodies, so the re-cut loses no consumer and the ellipsoid producer
  `Kakeya.VeryNotSticky.slabRescale_A1_and_A1'` still supplies it. -/
  A1 : ∀ j ∈ Wd, L '' (bd.Wb j).carrier ⊆ Metric.closedBall 0 1
  /-- (A1') the closed `τ₂(W)`-neighbourhood of each body of `𝕎''_S` is carried into the unit
  ball; this is what bears on the *enlarged* carriers, which need not lie in `S` -/
  A1' : ∀ j ∈ Wd,
    L '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier ⊆ Metric.closedBall 0 1
  /-- (A2) each body of `𝕎''_S` is carried to a `ρ₂`-tube, at the `δ`-free comparison constant
  `Cmp`, a parameter of the structure.

  **Why the constant is a parameter.** On the degenerate route `a = b` the transport is a
  homothety and `Kakeya.VeryNotSticky.hasThicknesses_degenerateRescale_body` gives the clause at
  `bd.C₀` itself; at general `(a, b)` it is `Kakeya.VeryNotSticky.latticeRescaleConstant bd.C₀`
  that `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_body_of_denseSlab` delivers, and at
  `bd.C₀` alone the clause is **not** a consequence of the transport at any `a < b`
  (`Kakeya.VeryNotSticky.aniLin_rank_two_gap`). Pinning either value here would either break the
  degenerate tripwire or make the general route unprovable, so the value travels with the
  structure as the parameter `Cmp`, pinned by `Kakeya.VeryNotSticky.SlabPackage.rescale` (with
  `bd.C₀ ≤ Cmp`) and matched against the comparison constant of the Katz–Tao input, pinned by
  `Kakeya.VeryNotSticky.SlabMultKT.estimate`, at the single place both are read,
  `Kakeya.VeryNotSticky.tangentialSlabMult`.  (Neither is a *field*: carrying the constant as a
  field of `SlabPackage` is undischargeable, because conjunct 3 of
  `Kakeya.VeryNotSticky.SideDataObligations` hands over `Nonempty (SlabPackage cfg ta)` and the
  consumer takes `.some`, so the package's constant is opaque exactly where the two must be
  compared.)

  At the general route's value the constant is a polynomial in `bd.C₀` and carries **no power of
  `δ`**: that is the
  difference from `anisotropicRescaleConstant bd.C₀ cfg.δ τ' = 4 C₀ δ^{-τ'}`, and it is why the
  enclosure constant `Kakeya.VeryNotSticky.ktRho2EnclosureConstant` stays `δ`-free and the
  fullness clause stays at `L ≤ 5/3`. It is produced from clause (S3′)/`IsDenseSlab.angle_ratio`
  by `Kakeya.VeryNotSticky.hasThicknesses_slabRescale_body_of_denseSlab`; at `bd.C₀` alone the
  clause is not a consequence of the transport at any `a < b`
  (`Kakeya.VeryNotSticky.aniLin_rank_two_gap`). Producers that do meet the smaller constant —
  the degenerate route's `hasThicknesses_degenerateRescale_body`, say — weaken to it by
  `Kakeya.VeryNotSticky.hasThicknesses_mono_const` and
  `Kakeya.VeryNotSticky.le_alignedRescaleConstant`. -/
  A2 : ∀ j ∈ Wd, HasThicknesses (L '' (bd.Wb j).carrier) Cmp
    ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]
  /-- (A2') the closed `τ₂(W)`-neighbourhood of each body of `𝕎''_S` is carried to a `ρ₂`-tube
  at the doubled comparison constant -/
  A2' : ∀ j ∈ Wd, HasThicknesses (L '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier)
    (2 * Cmp) ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]
  /-- (A3) the transport distorts `Δ_max` by at most `CΔ` -/
  A3 : ∀ V : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ j ∈ Wd, (V j).carrier = L '' (bd.Wb j).carrier) →
    ConvexSpaceBody.IsKatzTao Wd V ((CΔ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)))

/-- **The Katz–Tao estimate for `ρ₂`-tubes, at the fixed Katz–Tao parameter `δ`** (GWZ
Lemma 3.7, blueprint `genKKT`, read through Remark `multBoundsDeltaVsRho`).

`cfg.KTRho2ScaleData bd ε η₁ κ` is the cross-section of GWZ Lemma 3.7
(`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, blueprint `genKKT`) at loss `ε`,
fullness threshold `η₁`, `Δ_max` level `κ`, tube scale `ρ₂` and Katz–Tao parameter
`τ = δ ≤ ρ₂`: any finite family of bodies comparable to `ρ₂`-tubes in the unit ball which is
Katz–Tao at `δ^{-κ}` and `δ^{η₁}`-full has multiplicity at most `δ^{-ε} |𝕋|^β`. The two
exponents are kept apart because the source keeps them apart: in Lemma 3.7 `Δ_max` enters as
the *factor* `Δ_max^{1-β}`, which the consumer folds into the loss `ε` at its own `Δ_max`
level `δ^{-κ}`, and the only threshold Lemma 3.7 attaches to the pair `(ε, β)` is the fullness
one, `η₁ = η(ε, β)`. The earlier diagonal `κ = η₁` — Definition 3.4's shape, with the `Δ_max`
level pinned to the fullness threshold — was refuted by the constant-copies family: `D` copies
of one fully shaded body satisfy every hypothesis at `D ≈ δ^{-η₁}` and violate the conclusion
as `δ → 0` once `ε < η₁ (1-β)`.

It differs from `Kakeya.VeryNotSticky.KTScaleData` in all three respects that the tangential
case needs, and neither implies the other: `KTScaleData` speaks only about subfamilies of the
fixed family `cfg.T` of `δ`-tubes, at the fixed threshold exponent `cfg.η`, whereas the
rescaled family `𝕋̃ = L(𝕎''_S)` of `Kakeya.VeryNotSticky.tangentialSlabMult` consists of
`ρ₂`-tubes indexed by a subset of `bd.ω`, and its fullness is only `δ^{8η}`. Reading the
estimate at the small parameter `τ = δ` for a family of `ρ₂`-tubes is exactly the content of
Remark `multBoundsDeltaVsRho`, and it only weakens the fullness requirement, since `τ ≤ ρ₂`
gives `τ^{η₁} ≤ ρ₂^{η₁}`.

The fullness threshold `η₁` is left as a parameter, since it is what
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` produces existentially from the pair
`(ε, β)`; the `Δ_max` level `κ` is a parameter because it is what the consumer supplies (for
`Kakeya.VeryNotSticky.tangentialSlabMult` it is the `δ^{-3ϱ}` of
`Kakeya.VeryNotSticky.slabKatzTao`); the hypothesis `9η ≤ η₁` of
`Kakeya.VeryNotSticky.SlabMultKT` is what connects `η₁` to the density chain. No clause
relates `κ` to `η₁`: `η₁(ε, β) ≤ ε/(1-β)` for every threshold `K_KT(β)` can provide, so a
clause `κ ≤ η₁` at `κ = 3ϱ`, `ε = ϱ` would be unsatisfiable for `β < 2/3`.

**Why this quantifies over `ShadedBody` and not over `ShadedTube`.** An earlier version read
`T : ω → ShadedTube cfg.rho2 (EuclideanSpace ℝ (Fin 3))`, and in that form the estimate was
*unusable* by its one consumer. `Tube ρ` carries the field
`carrier_eq : carrier = ⋃ z ∈ segment x y, closedBall z ρ`, which structurally forces the
carrier to be the `ρ`-thickening of a unit segment. What
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` supplies about the rescaled bodies is its
clause (A2), `HasThicknesses (L '' (bd.Wb j).carrier) bd.C₀ ![1, rho2, rho2]` — thicknesses
*comparable* to that profile, with constant `bd.C₀`. Comparable is not equal: a
`1 × rho2 × rho2` box has exactly that thickness profile and is not the `rho2`-thickening of
any unit segment, and no lemma turns a `HasThicknesses ![1, ρ, ρ]` convex body into a `Tube ρ`
with the *same* carrier. Since clause (A3) gives its Katz–Tao bound only for families whose
carriers *equal* `L '' (bd.Wb j).carrier`, there was no way to build a `ShadedTube` family
meeting the Katz–Tao hypothesis, and `Kakeya.VeryNotSticky.tangentialSlabMult` was blocked
outright rather than merely unproved.

The statement never used the tube-only fields — only `.carrier`, `.shade`,
`.toConvexSpaceBody`, all of which `ShadedBody` has — so the repair is to quantify over
`ShadedBody` and carry the tube profile as the explicit hypothesis `hthick`. That is also the
faithful rendering of Remark `multBoundsDeltaVsRho`, which reads the Katz–Tao estimate for a
family of bodies comparable to `ρ₂`-tubes; the enclosure implicit in "comparable" costs a
constant, which is what `bd.C₀` records. The comparison constant is `2 bd.C₀`, so `bd` is now a
parameter of the definition.

**Why `2 bd.C₀` and not `bd.C₀`.** The family the estimate is applied to is the rescaled
*shaded* family `𝕋̃ = L(𝕎''_S)`, whose carriers are the enlarged outer carriers
`((tc.thinBall hB).W j).carrier` of the corrected factoring proposition and not the geometric
bodies `bd.Wb j`. Those carriers inherit the tube profile only at the doubled constant — that
is clause (A2') of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale`, and in the original
coordinates it is `Kakeya.ThinCase.ThinBall.hasThicknesses_W`. Reading the estimate at `2 bd.C₀`
is a *strengthening* of this assumption, not of any conclusion: a Katz–Tao estimate valid for
bodies comparable to `ρ₂`-tubes with a worse constant is what the tangential chain needs, and
`Kakeya.KatzTaoEstimate.generalize` supplies it at every fixed comparison constant. The slab
case charges the same doubling, there through
`Kakeya.VeryNotSticky.slabInputsConstant`.

The family is indexed by `bd.ω` and not by a universe-quantified `ω : Type u`: the sole
instantiation is at `bd.ω` (through `Kakeya.VeryNotSticky.tangentialSlabMult`, whose family
`𝕋̃ = L(𝕎''_S)` is indexed by `Wd ⊆ bd.ω`), and `BallData.ω : Type u` already lives at the
universe of `cfg`, so the polymorphism was never exercised. -/
def KTRho2ScaleData (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (ε η₁ κ : ℝ) : Prop :=
  ∀ (t : Finset bd.ω) (T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
    (∀ j ∈ t, (T j).carrier ⊆ Metric.closedBall 0 1) →
    (∀ j ∈ t, HasThicknesses (T j).carrier (2 * bd.C₀)
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]) →
    ConvexSpaceBody.IsKatzTao t (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-κ)) →
    cfg.δ ^ η₁ ≤ ShadedBody.fullness t T →
    ShadedBody.multiplicity t T ≤
      (cfg.δ : ENNReal) ^ (-ε) * (t.card : ENNReal) ^ cfg.β

/-- **`Kakeya.VeryNotSticky.KTRho2ScaleData` with the comparison constant as a parameter.**

Moved here from `Kakeya.DimensionThree.MainLemma2.TangentialSlabAlign` (where it was introduced
and where its producers still live) because `Kakeya.VeryNotSticky.SlabMultKT.estimate` now reads
it at `Cmp := latticeRescaleConstant bd.C₀`, the constant clauses (A2)/(A2′) are stated at.
The body is unchanged, byte for byte, and `ktRho2ScaleDataAt_at_C₀` still witnesses that at
`Cmp = bd.C₀` it *is* `KTRho2ScaleData`, definitionally. -/
def KTRho2ScaleDataAt (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (Cmp : NNReal)
    (ε η₁ κ : ℝ) : Prop :=
  ∀ (t : Finset bd.ω) (T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
    (∀ j ∈ t, (T j).carrier ⊆ Metric.closedBall 0 1) →
    (∀ j ∈ t, Kakeya.HasThicknesses (T j).carrier (2 * Cmp)
      ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]) →
    ConvexSpaceBody.IsKatzTao t (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-κ)) →
    cfg.δ ^ η₁ ≤ ShadedBody.fullness t T →
    ShadedBody.multiplicity t T ≤
      (cfg.δ : ENNReal) ^ (-ε) * (t.card : ENNReal) ^ cfg.β

/-- Tripwire: `KTRho2ScaleData` spelled out, so that a later edit of the
definition body is visible. -/
theorem KTRho2ScaleData_spelled (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (ε η₁ κ : ℝ) :
    cfg.KTRho2ScaleData bd ε η₁ κ ↔
    (∀ (t : Finset bd.ω) (T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      (∀ j ∈ t, (T j).carrier ⊆ Metric.closedBall 0 1) →
      (∀ j ∈ t, HasThicknesses (T j).carrier (2 * bd.C₀)
        ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]) →
      ConvexSpaceBody.IsKatzTao t (fun j ↦ (T j).toConvexSpaceBody)
        ((cfg.δ : ENNReal) ^ (-κ)) →
      cfg.δ ^ η₁ ≤ ShadedBody.fullness t T →
      ShadedBody.multiplicity t T ≤
        (cfg.δ : ENNReal) ^ (-ε) * (t.card : ENNReal) ^ cfg.β) := Iff.rfl

/-! ### Invariance of `μ` and `λ` under the anisotropic rescaling

Blueprint `lem:ml2tangentialSlabRescale`, equation `tangentialSlabRescaleInvariance`, is
`ShadedBody.multiplicity_affineImage` and `ShadedBody.fullness_affineImage` of
`Kakeya/Homothety.lean`: two statements, one conclusion each, in the `ShadedBody` namespace
beside their isotropic special cases `ShadedBody.multiplicity_homothety` and
`ShadedBody.fullness_homothety`, and stated for a general finite-dimensional real inner
product space rather than for `EuclideanSpace ℝ (Fin 3)`. Nothing about them is specific to
the very-not-sticky case, so they do not live here.
-/

/-- **The fibre-count constant** `C^fib_{lem:ml2tangentialSlabDecomp}` of blueprint
`def:ml2tangentialSlabDecompMultConstant`(a).

The product of the constant implicit in the `⪅` of the typicality bound `anglebound`, which is
`Ctyp`, with the absolute constant of the covering argument counting the slabs met by one
fibre. The proof of `Kakeya.VeryNotSticky.tangentialSlabFibreCount` produces it as
`C_{lem:coneDirectionCount} (3 Ctyp / c_{lem:ml2slabAxisSeparation}(C₀))²`, the aperture of
the cone being `3 Ctyp δ^{-τ'} a/b` and the separation of its normals
`c_{lem:ml2slabAxisSeparation}(C₀) a/b`, so that the scale `a/b` cancels.

The factor `3 Ctyp` — rather than the `2 + Ctyp` that the triangle inequality
`∠(n(S), n(W₁)) ≤ ∠(n(S), n(W)) + ∠(n(W), n(W₁)) ≤ 2θ + Ctyp θ` literally gives — is the
blueprint's `2 Ctyp` with the slab-angle clause read at `2θ` instead of `θ` (clause (S3) of `Kakeya.VeryNotSticky.IsSlabFamily` and the filter
`Kakeya.VeryNotSticky.slabBodies` bound `∠(n(W), n(S))` by `2θ`, GWZ's `θ`-accuracy with an
absolute constant; the factor `2` is absorbed here), and it is legitimate only because
`1 ≤ Ctyp`. That is
`Kakeya.VeryNotSticky.TypicalAngleData.hCtyp1`, a field of the typical-angle bundle and not
something the shape of this constant can supply: the expression is `∝ Ctyp²`, so at small
`Ctyp` it *decreases*, and at `Ctyp = 0` it vanishes while the count is `≥ 1` as soon as one
slab shades `x`.

It carries no power of `δ`: the `δ^{-2τ'}` of the fibre count is written out in the statement
and charged to the quarter budget. Together with the factor `100/99` of
`Kakeya.VeryNotSticky.tangentialDenseSlabs_isCRefinement` this is exactly what an admissible
`Cμ` of `Kakeya.VeryNotSticky.IsSlabDecompMultConstant` dominates. -/
noncomputable def slabDecompFibreConstant (C₀ Ctyp : NNReal) : NNReal :=
  slabConeCountConstant C₀ * 16 * Ctyp ^ 2

/-- The fibre-count constant is the cone-count constant of clause (S4″) times `16 Ctyp²`. The two
factors are exactly what `Kakeya.VeryNotSticky.tangentialSlabFibreCount`'s arithmetic
produces: (S4″) is read at the cone aperture `α = 3 Ctyp δ^{-τ'} (a/b)`, so its right-hand
side is `slabConeCountConstant C₀ · (3 Ctyp δ^{-τ'} + 1)²`, and `1 ≤ Ctyp δ^{-τ'}` turns
`(3 Ctyp δ^{-τ'} + 1)²` into `16 Ctyp² δ^{-2τ'}`. -/
lemma slabDecompFibreConstant_eq (C₀ Ctyp : NNReal) :
    slabDecompFibreConstant C₀ Ctyp = slabConeCountConstant C₀ * 16 * Ctyp ^ 2 := rfl

/-- The cone-count constant is below the fibre-count constant at every admissible typicality
constant, which is what lets clause (S4″) discharge
`Kakeya.VeryNotSticky.tangentialSlabFibreCount` at its existing bound. -/
lemma slabConeCountConstant_le_slabDecompFibreConstant {C₀ Ctyp : NNReal} (h : 1 ≤ Ctyp) :
    slabConeCountConstant C₀ ≤ slabDecompFibreConstant C₀ Ctyp := by
  rw [slabDecompFibreConstant]
  calc slabConeCountConstant C₀ = slabConeCountConstant C₀ * 1 * 1 ^ 2 := by ring
    _ ≤ slabConeCountConstant C₀ * 16 * Ctyp ^ 2 := by
        gcongr
        all_goals norm_num

/-- **Constant in the multiplicity clause of `tangentialSlabDecomp`** (blueprint
`def:ml2tangentialSlabDecompMultConstant`).

`Cμ` is *admissible for the thickness constant `C₀` and the typicality constant `Ctyp`* if it
dominates the product of the two multiplicative losses of the multiplicity chain: the
fibre-count constant `C^fib_{lem:ml2tangentialSlabDecomp}` of blueprint
`def:ml2tangentialSlabDecompMultConstant`(a), which is
`Kakeya.VeryNotSticky.slabDecompFibreConstant`, and the factor `100/99` of
`def:ml2tangentialSlabDecompMultConstant`(b) coming from the passage to the dense subfamily.

Like blueprint `def:ml2goalDensity`, this is a *predicate* on a constant and not a defining
equation: `Cμ` also has to satisfy the fixed-scale threshold `Cμ ≤ δ^{-τ'}` of
`Kakeya.VeryNotSticky.SlabPackage.Cμ_le`, so it cannot be pinned to a formula. The single
clause is exactly the inequality the proof of `lem:ml2tangentialSlabDecomp` needs in order to
absorb the prefactor `(100/99) C^fib δ^{-2τ' - 2η}` of
`Kakeya.VeryNotSticky.tangentialSlabDecompMultChain` into `δ^{-C_sep τ'/4}`. There is no
separate `1 ≤ Cμ` field: at the constants the consumers use,
`slabDecompFibreConstant bd.C₀ ta.Ctyp = 9 · 2^34 bd.C₀^8 ta.Ctyp^2`, and both `1 ≤ bd.C₀` and
`1 ≤ ta.Ctyp` are available — the latter as
`Kakeya.VeryNotSticky.TypicalAngleData.hCtyp1`, a field of the typical-angle bundle — so the
fibre constant is `≥ 9 · 2^34` and `1 ≤ Cμ` follows from `typ_le`.

What matters, and all that the consumers use, is that an admissible `Cμ` is a function of
`Ctyp`, of `bd.C₀` and of absolute constants alone, and carries no power of `δ`: every power
of `δ` in the multiplicity clause — the `δ^{-2τ'}` of the fibre count and the `δ^{-2η}` of
the refinement — is written out in the statement instead. That is exactly what makes the
fixed-scale threshold `tangentialSlabMultThreshold`, `Cμ ≤ δ^{-τ'}`, available. -/
structure IsSlabDecompMultConstant (C₀ Ctyp Cμ : NNReal) : Prop where
  /-- `Cμ` dominates the fibre-count constant `C^fib` of
  `Kakeya.VeryNotSticky.slabDecompFibreConstant`, together with the factor `100/99` of the
  passage to the dense subfamily -/
  typ_le : (100 / 99 : NNReal) * slabDecompFibreConstant C₀ Ctyp ≤ Cμ

/-! ### The slab decomposition, in pieces

The decomposition `Kakeya.VeryNotSticky.tangentialSlabDecomp` is a chain of independent
moves, each stated separately here: naming the subfamily `𝕎''_S` of a slab and the subfamily
attached to a *set* of slabs, recasting the latter as a refinement, selecting the dense slabs,
separating the slab normals, counting the slabs met by one fibre, and chaining the density and
the multiplicity. The exponent check is
`Kakeya.VeryNotSticky.tangentialSlabDecompExponent`, in `MainLemma2/VeryNotSticky.lean`, and
the positivity side conditions are the `Kakeya.VeryNotSticky.thinBallPositivity_*` group, in
`MainLemma2/ThinConfig.lean`; neither mentions a slab, so neither lives here.
-/

open scoped Classical in
/-- **The subfamily of `𝕎''_B` attached to one slab** (blueprint `tangentialWWS`).

`𝕎''_S = {W ∈ 𝕎''_B : W ⊆ S and ∠(n(W), n(S)) ≤ 2θ}`, with `n(·)` the normal of blueprint
`def:ml2bodyNormal`, the angle read at `2θ` in lockstep with clause (S3) of
`Kakeya.VeryNotSticky.IsSlabFamily`. Here `Wb'` indexes `𝕎''_B`; its
one instantiation is `ta.sel`, the index
set on which the `c`-refinement of `Kakeya.VeryNotSticky.TypicalAngleData` is recorded.

The clauses are the geometric clauses `bodies_subset` and `angle` of
`Kakeya.VeryNotSticky.IsDenseSlab`, so that `IsDenseSlab cfg ta 𝕊 S (slabBodies cfg ta.sel
ta.θ S)` is exactly what `Kakeya.VeryNotSticky.tangentialSlabDecompMultChain` returns. -/
noncomputable def slabBodies (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (Wb' : Finset bd.ω) (slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Finset bd.ω :=
  {j ∈ Wb' | slabOf j = S}

open scoped Classical in
/-- **Projection of the defining fields.** Membership in `𝕎''_S` is containment
in the slab together with the normal angle at `2θ`, in lockstep with clause (S3) of
`Kakeya.VeryNotSticky.IsSlabFamily`; this declaration fails to elaborate if the filter
changes. -/
theorem mem_slabBodies_iff (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {Wb' : Finset bd.ω} {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {j : bd.ω} :
    j ∈ slabBodies cfg Wb' slabOf S ↔ j ∈ Wb' ∧ slabOf j = S := by
  rw [slabBodies, Finset.mem_filter]

open scoped Classical in
/-- **The subfamily of `𝕎''_B` attached to a set of slabs**: the blueprint's
`𝕍_{𝕊'} = ⨆_{S ∈ 𝕊'} 𝕎''_S` of `lem:ml2tangentialSlabRecast`.

It is defined as a *filter* of `Wb'` rather than as a `Finset.biUnion` over `𝕊'` on purpose:
`ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))` carries no `DecidableEq`, and none is derivable,
so `𝕊'` is a `Set` throughout (see `Kakeya.VeryNotSticky.IsSlabFamily`) and a `biUnion` over
it would first have to be given one. Under clause (S3) of
`Kakeya.VeryNotSticky.IsSlabFamily` the two agree, because each `j ∈ Wb'` lies in `𝕎''_S` for
exactly one `S ∈ 𝕊`; that is what makes the double sum over `S ∈ 𝕊'` of blueprint
`tangentialSlabRecastMass` equal to the single sum over this index set. -/
noncomputable def slabsBodies (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (Wb' : Finset bd.ω) (slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) : Finset bd.ω :=
  {j ∈ Wb' | slabOf j ∈ 𝕊'}

open scoped Classical in
/-- **The partition identity behind the slab decomposition.**

For a subfamily `𝕊' ⊆ 𝕊` of a slab family, summing a weight `f` first over the bodies of each
`𝕎''_S`, `S ∈ 𝕊'`, and then over `𝕊'` is the same as summing it once over
`𝕍_{𝕊'} = ⨆_{S ∈ 𝕊'} 𝕎''_S`. This is exactly clause (S3) of
`Kakeya.VeryNotSticky.IsSlabFamily`: the sets `slabBodies cfg Wb' slabOf S`, `S ∈ 𝕊'`, are pairwise
disjoint and their union is `slabsBodies cfg Wb' slabOf 𝕊'`.

It is stated for a general `f : bd.ω → ℝ≥0∞`, and privately, because it is not a blueprint
statement but the common step of `tangentialSlabRecast_isCRefinement_iff` (at the shaded
volumes), of `tangentialDenseSlabs_mass` (at the shaded volumes, the carrier volumes, and the
whole family `𝕊' = 𝕊`) and of `tangentialSlabFibreCountMult` (at the fibre counts). -/
private theorem sum_slabBodies_eq_sum_slabsBodies (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf)
    {𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))} (h𝕊' : 𝕊' ⊆ 𝕊)
    (f : bd.ω → ENNReal) :
    (∑ S ∈ (hS.finite.subset h𝕊').toFinset, ∑ j ∈ slabBodies cfg Wb' slabOf S, f j) =
      ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊', f j := by
  classical
  let F' : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
    (hS.finite.subset h𝕊').toFinset
  -- **The partition is now by construction**: the fibres of `slabOf`
  -- are pairwise disjoint because `slabOf` is a function, and their union over `𝕊'` is the
  -- preimage `slabOf⁻¹(𝕊') ∩ Wb'`. Clause (S3) is no longer spent here at all.
  have hdisj : (F' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))).PairwiseDisjoint
      (fun S => slabBodies cfg Wb' slabOf S) := by
    intro S _hS1 S' _hS2 hne
    change Disjoint (slabBodies cfg Wb' slabOf S) (slabBodies cfg Wb' slabOf S')
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact hne
      ((((mem_slabBodies_iff cfg).mp hj1).2).symm.trans ((mem_slabBodies_iff cfg).mp hj2).2)
  have hbi : F'.biUnion (fun S => slabBodies cfg Wb' slabOf S) = slabsBodies cfg Wb' slabOf 𝕊' := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      rcases Finset.mem_biUnion.mp hj with ⟨S, hSF, hjS⟩
      obtain ⟨hjW, hjeq⟩ := (mem_slabBodies_iff cfg).mp hjS
      refine Finset.mem_filter.mpr ⟨hjW, ?_⟩
      rw [hjeq]
      exact (Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mp hSF
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hjW, hjmem⟩
      exact Finset.mem_biUnion.mpr
        ⟨slabOf j, (Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mpr hjmem,
          (mem_slabBodies_iff cfg).mpr ⟨hjW, rfl⟩⟩
  calc
    (∑ S ∈ (hS.finite.subset h𝕊').toFinset, ∑ j ∈ slabBodies cfg Wb' slabOf S, f j)
        = ∑ j ∈ F'.biUnion (fun S => slabBodies cfg Wb' slabOf S), f j := by
          rw [Finset.sum_biUnion hdisj]
    _ = ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊', f j := by rw [hbi]

/-- **The dense slabs** (blueprint `tangentialSdens`).

`𝕊_dens` is the set of slabs of `𝕊` whose subfamily `𝕎''_S` is nonempty and carries at least a
hundredth of the ambient density `λ(𝕎''_B, Y_{𝕎''_B})`. The density condition is stated
division-free, as `λ(𝕎''_B, Y) ∑_{W ∈ 𝕎''_S}|W| ≤ 100 ∑_{W ∈ 𝕎''_S}|Y(W)|`: in the quotient
form it needs `∑_{W ∈ 𝕎''_S}|W| > 0`, which `𝕎''_S ≠ ∅` alone does not give — that comes from
`Kakeya.VeryNotSticky.volume_body_pos`.

The threshold is the explicit number `1/100` and not a `⪆ 1`: the multiplicity chain divides
by it, and `Kakeya.LEApprox` supplies its constant only existentially. The clause
`𝕎''_S ≠ ∅` is part of the definition and not an afterthought, since
`Kakeya.VeryNotSticky.tangentialSlabDecomp` asserts the existence of a slab with `𝕎''_S ≠ ∅`
and takes a maximum of `μ(𝕎''_S, Y_{𝕎''_S})` over `𝕊_dens`. -/
noncomputable def denseSlabs (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (Wb' : Finset bd.ω) (slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) :
    Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
  {S ∈ 𝕊 | (slabBodies cfg Wb' slabOf S).Nonempty ∧
    (ShadedBody.fullness Wb' YW : ENNReal) *
        ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).carrier ≤
      100 * ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).shade}

/-- **A subfamily of slabs is a refinement** (blueprint `lem:ml2tangentialSlabRecast`, first
half).

For any set of slabs `𝕊'`, the family `𝕍_{𝕊'} = ⨆_{S ∈ 𝕊'} 𝕎''_S` with the shading inherited
from `Y_{𝕎''_B}` is a refinement of `(𝕎''_B, Y_{𝕎''_B})` in the sense of
`ShadedBody.IsRefinement`.

This half of the blueprint lemma is the cheap one, and it is stated separately for that
reason: `slabsBodies` is by definition a `Finset.filter` of `Wb'` and the shading is literally
`YW`, so neither the slab-family hypothesis nor `𝕊' ⊆ 𝕊` is needed and there is no content to
hide. All the content of `lem:ml2tangentialSlabRecast` sits in
`Kakeya.VeryNotSticky.tangentialSlabRecast_isCRefinement_iff`. -/
theorem tangentialSlabRecast_isRefinement (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (Wb' : Finset bd.ω) (slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) :
    ShadedBody.IsRefinement (slabsBodies cfg Wb' slabOf 𝕊') YW Wb' YW := by
  classical
  constructor
  · intro j hj
    exact (Finset.mem_filter.mp hj).1
  · intro i hi
    exact ⟨rfl, Set.Subset.rfl⟩

/-- **When a subfamily of slabs is a `c`-refinement** (blueprint
`lem:ml2tangentialSlabRecast`, second half).

For `𝕊' ⊆ 𝕊`, the refinement `𝕍_{𝕊'} = ⨆_{S ∈ 𝕊'} 𝕎''_S` of
`Kakeya.VeryNotSticky.tangentialSlabRecast_isRefinement` is a `c`-refinement exactly when it
retains a `c`-fraction of the shaded mass, blueprint `tangentialSlabRecastMass`.

The mass condition is stated as the blueprint's *double* sum over `S ∈ 𝕊'`, which clause (S3)
of `Kakeya.VeryNotSticky.IsSlabFamily` identifies with the single sum over
`slabsBodies cfg Wb' slabOf 𝕊'`; that identification is the whole content of the `iff`, and it is
what `hS` and `h𝕊'` are for — without (S3) the double sum overcounts the bodies lying in
several `𝕎''_S`, and the two sides differ.

**The signature.** Eleven binder groups, so: `cfg` and `bd` are the ambient Configuration
`hyp:ml2setup` data, fixing `bd.ω` and `bd.Wb`; `B` is the ball, which only `hS` mentions;
`Wb'` indexes `𝕎''_B`, the family being refined, and `θ` is the angular resolution — both
occur in `slabBodies`/`slabsBodies` on each side; `𝕊` and `hS` are the slab family, and it is
`hS`'s clause (S3) that makes the double sum a single sum, hence the whole `iff`; `YW` is the
shading, inherited on both sides; `𝕊'` and `h𝕊'` are the subfamily and its inclusion, the
latter both letting (S3) apply and making the `Finset`
`(hS.finite.subset h𝕊').toFinset` of the right-hand side exist; and `c` is the refinement
factor the `iff` is about, instantiated at `99/100` by
`Kakeya.VeryNotSticky.tangentialDenseSlabs_isCRefinement`. -/
theorem tangentialSlabRecast_isCRefinement_iff (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))} (h𝕊' : 𝕊' ⊆ 𝕊) (c : NNReal) :
    ShadedBody.IsCRefinement (slabsBodies cfg Wb' slabOf 𝕊') YW Wb' YW c ↔
      (c : ENNReal) * ∑ j ∈ Wb', volume (YW j).shade ≤
        ∑ S ∈ (hS.finite.subset h𝕊').toFinset,
          ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).shade := by
  classical
  have sum_partition :=
    sum_slabBodies_eq_sum_slabsBodies cfg hS h𝕊' (fun j => volume (YW j).shade)
  constructor
  · intro h
    exact h.2.trans_eq sum_partition.symm
  · intro hmass
    refine ⟨tangentialSlabRecast_isRefinement cfg Wb' slabOf YW 𝕊', ?_⟩
    exact hmass.trans_eq sum_partition

/-- **The dense slabs carry almost all the mass** (blueprint
`lem:ml2tangentialDenseSlabs`(i)).

With `𝕊_dens` as in `Kakeya.VeryNotSticky.denseSlabs`, blueprint `tangentialSdens`, the dense
slabs carry at least `99/100` of the shaded mass of `𝕎''_B`.

This is `Kakeya.le_sum_filter_dense`, Markov on densities, at `κ = 1/100`, together with the
observation that the slabs excluded from `𝕊_dens` by the clause `𝕎''_S ≠ ∅` carry no mass at
all, so that dropping them costs nothing.

No positivity of the total mass or of the total volume is assumed: Markov needs only that the
total mass is *finite*, and that is automatic, since each `Y(W) ⊆ W` is compact. At zero mass
the statement is `0 ≤ 0`. -/
theorem tangentialDenseSlabs_mass (cfg : VeryNotSticky.{u}) {bd : BallData cfg} {B : bd.bι}
    {Wb' : Finset bd.ω} {θ : NNReal}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    (99 / 100 : ENNReal) * ∑ j ∈ Wb', volume (YW j).shade ≤
      ∑ j ∈ slabsBodies cfg Wb' slabOf (denseSlabs cfg Wb' slabOf YW 𝕊), volume (YW j).shade := by
  classical
  let m : bd.ω → ENNReal := fun j => volume (YW j).shade
  let v : bd.ω → ENNReal := fun j => volume (YW j).carrier
  let d : ENNReal := (ShadedBody.fullness Wb' YW : ENNReal)
  let mS : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) → ENNReal :=
    fun S => ∑ j ∈ slabBodies cfg Wb' slabOf S, m j
  let vS : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) → ENNReal :=
    fun S => ∑ j ∈ slabBodies cfg Wb' slabOf S, v j
  let 𝕊d : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) := denseSlabs cfg Wb' slabOf YW 𝕊
  have h𝕊d_sub : 𝕊d ⊆ 𝕊 := fun S hSd => hSd.1
  let Fd : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
    (hS.finite.subset h𝕊d_sub).toFinset
  let F : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) := hS.finite.toFinset
  -- `𝕎''_B` is recovered from the whole family
  have hslabs_eq : slabsBodies cfg Wb' slabOf 𝕊 = Wb' := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      exact (Finset.mem_filter.mp hj).1
    · intro hjW
      -- (S3′) assigns `j` to `slabOf j ∈ 𝕊`, so `j` is in the preimage outright
      exact Finset.mem_filter.mpr ⟨hjW, (hS.S3 j hjW).1⟩
  -- the partition identity: a subfamily-sum over `𝕊'` equals the body-sum over `slabsBodies`
  have sum_partition {𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))} (h𝕊' : 𝕊' ⊆ 𝕊)
      {f : bd.ω → ENNReal} :
      (∑ S ∈ (hS.finite.subset h𝕊').toFinset, ∑ j ∈ slabBodies cfg Wb' slabOf S, f j) =
        ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊', f j :=
    sum_slabBodies_eq_sum_slabsBodies cfg hS h𝕊' f
  -- total mass in ENNReal is finite
  have hM_ne_top : (∑ j ∈ Wb', volume (YW j).shade) ≠ ⊤ := by
    have hcar : (∑ j ∈ Wb', volume (YW j).carrier) ≠ ⊤ := by
      intro ht
      rcases ENNReal.sum_eq_top.1 ht with ⟨j, hj, htop⟩
      exact (YW j).isCompact'.measure_ne_top htop
    exact ne_top_of_le_ne_top hcar (Finset.sum_le_sum (fun j _ => measure_mono (YW j).shade_subset))
  have hFsame : F = (hS.finite.subset (subset_rfl : 𝕊 ⊆ 𝕊)).toFinset := by
    apply Finset.ext
    intro S
    simp [F]
  have hM_split : (∑ S ∈ F, mS S) = (∑ j ∈ Wb', m j) := by
    calc
      (∑ S ∈ F, mS S) = (∑ S ∈ (hS.finite.subset (subset_rfl : 𝕊 ⊆ 𝕊)).toFinset, mS S) := by
        rw [hFsame]
      _ = ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊, m j := by
        simpa [mS] using (sum_partition (h𝕊' := (subset_rfl : 𝕊 ⊆ 𝕊)) (f := m))
      _ = ∑ j ∈ Wb', m j := by rw [hslabs_eq]
  have hV_split : (∑ S ∈ F, vS S) = (∑ j ∈ Wb', v j) := by
    calc
      (∑ S ∈ F, vS S) = (∑ S ∈ (hS.finite.subset (subset_rfl : 𝕊 ⊆ 𝕊)).toFinset, vS S) := by
        rw [hFsame]
      _ = ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊, v j := by
        simpa [vS] using (sum_partition (h𝕊' := (subset_rfl : 𝕊 ⊆ 𝕊)))
      _ = ∑ j ∈ Wb', v j := by rw [hslabs_eq]
  have hd : d * (∑ S ∈ F, vS S) ≤ ∑ S ∈ F, mS S := by
    rw [hV_split, hM_split]
    simpa [d, m, v] using
      (ShadedBody.sum_volumeReal_shade_eq_fullness_mul (s := Wb') (V := YW)).symm.le
  have hMarkov :
      (1 - (1/100 : ENNReal)) * (∑ S ∈ F, mS S) ≤
        ∑ S ∈ {S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}, mS S := by
    refine Kakeya.le_sum_filter_of_mul_sum_le (J := F) (m := mS) (v := vS)
      (d := d) (κ := (1/100 : ENNReal)) ?_ ?_ hd
    · have ht : (∑ S ∈ F, mS S) = (∑ j ∈ Wb', volume (YW j).shade) := by
        simpa [m] using hM_split
      rw [ht]
      exact hM_ne_top
    · norm_num
  -- a slab satisfies the denseSlabs clause iff it satisfies the Markov selection
  have hdense_iff (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
      ((1 / 100 : ENNReal) * d * vS S ≤ mS S) ↔ (d * vS S ≤ (100 : ENNReal) * mS S) := by
    have h1 : (100 : ENNReal) * (1 / 100 : ENNReal) = 1 := by
      rw [one_div]
      simpa [mul_one] using
        (ENNReal.mul_inv_cancel_left (a := (100 : ENNReal)) (b := (1 : ENNReal))
          (by norm_num : (100 : ENNReal) ≠ 0)
          (by norm_num : (100 : ENNReal) ≠ ⊤))
    have h2 : (1 / 100 : ENNReal) * (100 : ENNReal) = 1 := by
      rw [mul_comm, h1]
    constructor
    · intro h
      calc
        d * vS S = (100 : ENNReal) * (((1 / 100 : ENNReal) * d) * vS S) := by
            rw [mul_assoc, ← mul_assoc, h1, one_mul]
        _ ≤ (100 : ENNReal) * mS S := mul_le_mul_right h (100 : ENNReal)
    · intro h
      calc
        (1 / 100 : ENNReal) * d * vS S = (1 / 100 : ENNReal) * (d * vS S) := by rw [mul_assoc]
        _ ≤ (1 / 100 : ENNReal) * ((100 : ENNReal) * mS S) := mul_le_mul_right h (1 / 100 : ENNReal)
        _ = mS S := by rw [← mul_assoc, h2, one_mul]
  -- the Markov-selected slabs, shedding those with empty subfamily
  have hdense_sum : (∑ S ∈ Fd, mS S) = ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊d, m j := by
    simpa [Fd, mS] using (sum_partition (h𝕊' := h𝕊d_sub) (f := m))
  have hShed :
      (∑ S ∈ {S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}, mS S) = ∑ S ∈ Fd, mS S := by
    let q : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) → Prop :=
      fun S => (slabBodies cfg Wb' slabOf S).Nonempty
    have hfilter : ({S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}).filter q = Fd := by
      apply Finset.ext
      intro S
      constructor
      · intro hmem
        rcases Finset.mem_filter.mp hmem with ⟨hSAl, hqS⟩
        rcases Finset.mem_filter.mp hSAl with ⟨hSF, hSmarkov⟩
        apply (Set.Finite.mem_toFinset (hS.finite.subset h𝕊d_sub)).mpr
        unfold 𝕊d denseSlabs
        exact ⟨(Set.Finite.mem_toFinset hS.finite).mp hSF, (by simpa [q] using hqS),
          (hdense_iff S).mp hSmarkov⟩
      · intro hmem
        have hS𝕊d : S ∈ 𝕊d := (Set.Finite.mem_toFinset (hS.finite.subset h𝕊d_sub)).mp hmem
        rcases (show S ∈ denseSlabs cfg Wb' slabOf YW 𝕊 by simpa [𝕊d] using hS𝕊d) with
          ⟨hS𝕊, hne, hdens⟩
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_filter.mpr
          exact ⟨(Set.Finite.mem_toFinset hS.finite).mpr hS𝕊, (hdense_iff S).mpr hdens⟩
        · simpa [q] using hne
    have hzero : ∀ S ∈ {S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}, ¬ q S → mS S = 0 := by
      intro S hS hqnot
      have hls : slabBodies cfg Wb' slabOf S = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        simpa [q] using hqnot
      dsimp [mS]
      rw [hls]
      simp
    calc
      (∑ S ∈ {S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}, mS S)
          = (∑ S ∈ ({S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}).filter q, mS S) +
              (∑ S ∈ ({S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}).filter
                (fun S => ¬ q S), mS S) := by
            rw [← Finset.sum_filter_add_sum_filter_not
                {S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S} q (fun S => mS S)]
      _ = ∑ S ∈ ({S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}).filter q, mS S := by
            have hz : (∑ S ∈ ({S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}).filter
                (fun S => ¬ q S), mS S) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro S hS
              exact hzero S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
            rw [hz]
            simp
      _ = ∑ S ∈ Fd, mS S := by rw [hfilter]
  have h99 : (99 / 100 : ENNReal) = 1 - (1 / 100 : ENNReal) := by
    have hsum' : (99 / 100 : ENNReal) + 1 / 100 = 1 := by
      calc
        (99 / 100 : ENNReal) + 1 / 100 = (99 + 1) / 100 := by
              exact (ENNReal.add_div (a := (99 : ENNReal)) (b := (1 : ENNReal))
                (c := (100 : ENNReal))).symm
        _ = (100 : ENNReal) / 100 := by norm_num
        _ = 1 := by
              exact ENNReal.div_self (by norm_num : (100 : ENNReal) ≠ 0)
                (by norm_num : (100 : ENNReal) ≠ ⊤)
    exact (ENNReal.sub_eq_of_eq_add (by norm_num : (1 / 100 : ENNReal) ≠ ⊤)
      (by rw [hsum'])).symm
  calc
    (99 / 100 : ENNReal) * (∑ j ∈ Wb', m j)
        = (1 - (1/100 : ENNReal)) * (∑ j ∈ Wb', m j) := by rw [h99]
    _ = (1 - (1/100 : ENNReal)) * (∑ S ∈ F, mS S) := by rw [hM_split]
    _ ≤ ∑ S ∈ {S ∈ F | (1/100 : ENNReal) * d * vS S ≤ mS S}, mS S := hMarkov
    _ = ∑ S ∈ Fd, mS S := hShed
    _ = ∑ j ∈ slabsBodies cfg Wb' slabOf 𝕊d, m j := hdense_sum

/-- **The dense slabs form a `99/100`-refinement** (blueprint
`lem:ml2tangentialDenseSlabs`(ii), first half).

`𝕎'''_B = ⨆_{S ∈ 𝕊_dens} 𝕎''_S`, with the shading inherited from `Y_{𝕎''_B}`, is a
`99/100`-refinement of `(𝕎''_B, Y_{𝕎''_B})`.

This is `Kakeya.VeryNotSticky.tangentialDenseSlabs_mass` fed to
`Kakeya.VeryNotSticky.tangentialSlabRecast_isCRefinement_iff` at `c = 99/100`; like that
lemma it needs no positivity hypothesis. -/
theorem tangentialDenseSlabs_isCRefinement (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ShadedBody.IsCRefinement
      (slabsBodies cfg Wb' slabOf (denseSlabs cfg Wb' slabOf YW 𝕊)) YW Wb' YW (99 / 100) := by
  classical
  constructor
  · constructor
    · intro j hj
      exact (Finset.mem_filter.mp hj).1
    · intro j hj
      exact ⟨rfl, Set.Subset.rfl⟩
  · -- the `99/100`-mass condition
    have hm99 : ((99 / 100 : NNReal) : ENNReal) = (99 / 100 : ENNReal) := by norm_num
    rw [hm99]
    exact tangentialDenseSlabs_mass cfg hS YW

/-- **There is at least one dense slab** (blueprint `lem:ml2tangentialDenseSlabs`(ii), second
half).

`𝕊_dens ≠ ∅`: by `Kakeya.VeryNotSticky.tangentialDenseSlabs_mass` and `hmass` the right-hand
side of item (i) is positive, and an empty `𝕊_dens` makes it zero.

Non-emptiness is what `Kakeya.VeryNotSticky.tangentialSlabDecompMultChain` needs in order to
select a slab at all, so it is recorded on its own rather than as a conjunct of the
refinement. -/
theorem tangentialDenseSlabs_nonempty (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {B : bd.bι} {Wb' : Finset bd.ω} {θ : NNReal}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hmass : 0 < ∑ j ∈ Wb', volume (YW j).shade) :
    (denseSlabs cfg Wb' slabOf YW 𝕊).Nonempty := by
  classical
  have hrhs :
      0 < ∑ j ∈ slabsBodies cfg Wb' slabOf (denseSlabs cfg Wb' slabOf YW 𝕊),
          volume (YW j).shade := by
    have hL : 0 < (99 / 100 : ENNReal) * ∑ j ∈ Wb', volume (YW j).shade := by
      exact ENNReal.mul_pos (by norm_num : (99 / 100 : ENNReal) ≠ 0) (ne_of_gt hmass)
    exact lt_of_lt_of_le hL (tangentialDenseSlabs_mass cfg hS YW)
  have hnb : (slabsBodies cfg Wb' slabOf (denseSlabs cfg Wb' slabOf YW 𝕊)).Nonempty := by
    by_contra hne
    have hs : slabsBodies cfg Wb' slabOf (denseSlabs cfg Wb' slabOf YW 𝕊) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hs] at hrhs
    simp at hrhs
  rcases hnb with ⟨j, hj⟩
  exact ⟨slabOf j, (Finset.mem_filter.mp hj).2⟩

/-- **A dense slab is dense, division-free form** (blueprint
`lem:ml2tangentialDenseSlabs`(iii), first half).

Every `S ∈ 𝕊_dens` satisfies `λ(𝕎''_B, Y) ∑_{W ∈ 𝕎''_S}|W| ≤ 100 ∑_{W ∈ 𝕎''_S}|Y(W)|`.

This is the definition of `Kakeya.VeryNotSticky.denseSlabs` read off, so it needs neither the
partition property of `Kakeya.VeryNotSticky.IsSlabFamily` nor the ambient positivity
hypotheses of items (i)–(ii). -/
theorem tangentialDenseSlabs_density (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {Wb' : Finset bd.ω} {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hSd : S ∈ denseSlabs cfg Wb' slabOf YW 𝕊) :
    (ShadedBody.fullness Wb' YW : ENNReal) *
        ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).carrier ≤
      100 * ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).shade := by
  exact hSd.2.2

/-- **A dense slab is dense, quotient form** (blueprint `lem:ml2tangentialDenseSlabs`(iii),
second half).

Every `S ∈ 𝕊_dens` of positive total volume satisfies
`λ(𝕎''_B, Y) ≤ 100 λ(𝕎''_S, Y_{𝕎''_S})`.

It is stated separately from
`Kakeya.VeryNotSticky.tangentialDenseSlabs_density`, and under the extra hypothesis `hvolS`,
because `λ(𝕎''_S, Y_{𝕎''_S})` divides by `∑_{W ∈ 𝕎''_S}|W|`, and `𝕎''_S ≠ ∅` alone does not
make that positive — `Kakeya.VeryNotSticky.volume_body_pos` does. This is the form the density
chain `Kakeya.VeryNotSticky.tangentialDensityChain` consumes. -/
theorem tangentialDenseSlabs_fullness_le (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {Wb' : Finset bd.ω} {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hSd : S ∈ denseSlabs cfg Wb' slabOf YW 𝕊)
    (hvolS : 0 < ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).carrier) :
    ShadedBody.fullness Wb' YW ≤ 100 * ShadedBody.fullness (slabBodies cfg Wb' slabOf S) YW := by
  let VS : ENNReal := ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).carrier
  let MS : ENNReal := ∑ j ∈ slabBodies cfg Wb' slabOf S, volume (YW j).shade
  have hdens := tangentialDenseSlabs_density cfg YW hSd
  have hVSne0 : VS ≠ 0 := by
    dsimp [VS]
    exact hvolS.ne'
  have hVSne_top : VS ≠ ⊤ := by
    dsimp [VS]
    exact (ENNReal.sum_ne_top (s := slabBodies cfg Wb' slabOf S)
      (f := fun j => volume (YW j).carrier)).2
      (fun j _ => (YW j).isCompact'.measure_ne_top)
  have hMS : MS = (ShadedBody.fullness (slabBodies cfg Wb' slabOf S) YW : ENNReal) * VS := by
    dsimp [MS, VS]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul
      (s := slabBodies cfg Wb' slabOf S) (V := YW)
  have hEN : (ShadedBody.fullness Wb' YW : ENNReal) ≤
      (100 : ENNReal) * (ShadedBody.fullness (slabBodies cfg Wb' slabOf S) YW : ENNReal) := by
    calc
      (ShadedBody.fullness Wb' YW : ENNReal)
          = ((ShadedBody.fullness Wb' YW : ENNReal) * VS) / VS := by
            rw [ENNReal.mul_div_cancel_right hVSne0 hVSne_top]
      _ ≤ (100 * MS) / VS := by
            simpa [MS] using (ENNReal.div_le_div_right hdens VS)
      _ = ((100 : ENNReal) * (ShadedBody.fullness (slabBodies cfg Wb' slabOf S) YW : ENNReal) * VS)
            / VS := by
            rw [hMS, mul_assoc]
      _ = (100 : ENNReal) * (ShadedBody.fullness (slabBodies cfg Wb' slabOf S) YW : ENNReal) := by
            rw [ENNReal.mul_div_cancel_right hVSne0 hVSne_top]
  exact_mod_cast hEN

/-- **Bounded overlap of the slab cells** — the re-cut of blueprint
`lem:ml2slabAxisSeparation` against the refined source.

The blueprint derived a *pairwise normal separation* from (S1) and (S2), by the overlap picture
"two slabs of thicknesses `∼ (r₁, r₁, (a/b) r₁)` inside a ball of radius `∼ r₁` whose directions
make an angle `≪ a/b` overlap in more than half of either one, contradicting essential
disjointness". That derivation is false — `∼ b/a` disjoint parallel translates of one such box
fit in the ball, and translates have equal normals — and, as the refined text makes explicit,
so is its conclusion for the family that is actually built: the slab cells are lattice
translates in one normal coordinate, of width `Cθ` at spacing `cθ`
(`260115_kakeyadetailedproofv3_revised_detailed.tex` l.1677-1680), so consecutive cells overlap
and are parallel.

What the source proves, and all its counting uses, is the cone-restricted bound of
l.1684-1688 — the whole-family form is false for the source's family, since its net of normals
ranges over *all* directions — which is clause (S4″). This lemma is
its projection: it exists so that `Kakeya.VeryNotSticky.tangentialSlabFibreCount` has a named
input rather than reaching into the structure, exactly as `slabAxisSeparation` did before
it. -/
theorem slabConeCount (cfg : VeryNotSticky.{u}) {bd : BallData cfg} {B : bd.bι}
    {Wb' : Finset bd.ω} {θ : NNReal}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    (hS : IsSlabFamily cfg B Wb' θ 𝕊 slabOf) (x v : EuclideanSpace ℝ (Fin 3)) {α : ℝ}
    (hα : 0 ≤ α) :
    (({S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
        NonSlab.lineAngle (bodyNormal S) v ≤ α}.ncard : ℕ) : ℝ) ≤
      (slabConeCountConstant bd.C₀ : ℝ) * (α / ((cfg.a / cfg.b : NNReal) : ℝ) + 1) ^ 2 :=
  hS.S4'' x v α hα

/-- The two scale facts that the tangential hypothesis `θ < δ^{-τ'} a/b` carries with it: the
aspect ratio is positive, and `δ^{-τ'} ≥ 1`. Both come from combining it with `θ ≥ a/b`
(`Kakeya.VeryNotSticky.TypicalAngleData.hθab'`), and both are needed by
`Kakeya.VeryNotSticky.tangentialSlabFibreCount` — the first to make the separation scale
`c a/b` of blueprint `slabAxisSeparation` nonzero, the second to compare it with the cone
aperture. -/
private lemma tangentialFibre_scales (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} (ta : TypicalAngleData cfg tc hB τ')
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b)) :
    0 < cfg.a / cfg.b ∧ 1 ≤ cfg.δ ^ (-τ') := by
  have hθge0 : (0 : ℝ) ≤ (ta.θ : ℝ) := NNReal.coe_nonneg ta.θ
  have hdge0 : 0 ≤ ((cfg.δ ^ (-τ') : NNReal) : ℝ) := NNReal.coe_nonneg (cfg.δ ^ (-τ'))
  have htangR : (ta.θ : ℝ) <
      ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) := by
    exact_mod_cast htang
  have hq_le_θR : ((cfg.a / cfg.b : NNReal) : ℝ) ≤ (ta.θ : ℝ) := by
    exact_mod_cast ta.hθab'
  have hposR : 0 < ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) :=
    lt_of_le_of_lt hθge0 htangR
  have hqR : 0 < ((cfg.a / cfg.b : NNReal) : ℝ) :=
    pos_of_mul_pos_right hposR hdge0
  have habθR : ((cfg.a / cfg.b : NNReal) : ℝ) <
      ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) :=
    lt_of_le_of_lt hq_le_θR htangR
  have h1rR : (1 : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) <
      ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) := by
    simpa using habθR
  have hdR : (1 : ℝ) < ((cfg.δ ^ (-τ') : NNReal) : ℝ) := by
    by_contra hle
    have hmul : ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) ≤
        (1 : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_of_not_gt hle) hqR.le
    nlinarith
  exact ⟨by exact_mod_cast hqR, by exact_mod_cast (le_of_lt hdR)⟩

/-- **The aperture of the cone** (blueprint `lem:ml2tangentialSlabFibreCount`, the display
following `anglebound`).

If `x` is shaded by the body `W₁ = bd.Wb j₁` of `𝕎''_B` and also by some body of `𝕎''_S`, then
the normal of `S` lies within `3 C_{lem:ml2typicalangle} δ^{-τ'} a/b` of the normal of `W₁`:
`∠(n(S), n(W₁)) ≤ ∠(n(S), n(W₂)) + ∠(n(W₂), n(W₁)) ≤ 2θ + Ctyp θ ≤ 3 Ctyp θ`, the first summand
by the angle clause of `Kakeya.VeryNotSticky.slabBodies`, the second by blueprint `anglebound`
(the field `Kakeya.VeryNotSticky.TypicalAngleData.hangle`), the last step by
`Kakeya.VeryNotSticky.TypicalAngleData.hCtyp1`, and then `θ < δ^{-τ'} a/b`. -/
private lemma tangentialFibre_cap (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} (ta : TypicalAngleData cfg tc hB τ')
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    {x : EuclideanSpace ℝ (Fin 3)} {j₁ : bd.ω} (hj₁ : j₁ ∈ ta.sel)
    (hxj₁ : x ∈ (ta.YW j₁).shade)
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (hxS : x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW) :
    axisAngle S (bd.Wb j₁) ≤
      3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) := by
  classical
  -- `hxS` : `x` lies in the union of the shadings over `slabBodies cfg ta.sel slabOf S`.
  rcases Set.mem_iUnion₂.mp hxS with ⟨j, hj, hjx⟩
  -- `j ∈ slabBodies cfg ta.sel slabOf S` unfolds to `j ∈ ta.sel` plus `slabOf j = S`; the
  -- slab angle clause is now (S3′) of the family, read at `j`.
  rw [slabBodies, Finset.mem_filter] at hj
  rcases hj with ⟨hjsel, hjeq⟩
  have hjang : axisAngle (bd.Wb j) S ≤ 2 * (ta.θ : ℝ) := by
    rw [← hjeq]; exact (hS.S3 j hjsel).2.2
  -- typicality on the bodies: `∠(n(W_j), n(W_j₁)) ≤ Ctyp·θ` since both shade `x`.
  have hangle : axisAngle (bd.Wb j) (bd.Wb j₁) ≤ (ta.Ctyp : ℝ) * (ta.θ : ℝ) :=
    ta.hangle x j hjsel j₁ hj₁ hjx hxj₁
  -- triangle inequality, then bound the two summands.
  have htrian : axisAngle S (bd.Wb j₁) ≤
      axisAngle (bd.Wb j) S + axisAngle (bd.Wb j) (bd.Wb j₁) := by
    simpa [axisAngle_comm] using (axisAngle_le_add S (bd.Wb j) (bd.Wb j₁))
  have hbnd : axisAngle S (bd.Wb j₁) ≤ 2 * (ta.θ : ℝ) + (ta.Ctyp : ℝ) * (ta.θ : ℝ) := by
    exact le_trans htrian (add_le_add hjang hangle)
  -- `2θ + Ctyp·θ ≤ 3·Ctyp·θ` by `1 ≤ Ctyp` and `0 ≤ θ`.
  have hCtyp1 : (1 : ℝ) ≤ (ta.Ctyp : ℝ) := by exact_mod_cast ta.hCtyp1
  have hθnonneg : 0 ≤ (ta.θ : ℝ) := by exact NNReal.coe_nonneg ta.θ
  have hbnd2 : 2 * (ta.θ : ℝ) + (ta.Ctyp : ℝ) * (ta.θ : ℝ) ≤
      3 * (ta.Ctyp : ℝ) * (ta.θ : ℝ) := by
    nlinarith
  -- `3·Ctyp·θ ≤ 3·Ctyp·δ^(-τ')·(a/b)` from the tangential hypothesis `htang`.
  have hθle : (ta.θ : ℝ) ≤
      ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) := by
    exact_mod_cast htang.le
  have hbnd3 : 3 * (ta.Ctyp : ℝ) * (ta.θ : ℝ) ≤
      3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
        ((cfg.a / cfg.b : NNReal) : ℝ) := by
    have hc : 0 ≤ 3 * (ta.Ctyp : ℝ) := by nlinarith [hCtyp1]
    calc
      3 * (ta.Ctyp : ℝ) * (ta.θ : ℝ)
          ≤ (3 * (ta.Ctyp : ℝ)) *
              (((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hθle hc
      _ = 3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
          ((cfg.a / cfg.b : NNReal) : ℝ) := by
            ring
  exact le_trans (le_trans hbnd hbnd2) hbnd3

/-- Transport of a real cardinality bound to the `ENNReal` shape the statement of
`Kakeya.VeryNotSticky.tangentialSlabFibreCount` uses. -/
private lemma ennreal_natCast_le_of_real_le {n : ℕ} {K δ : NNReal} {s : ℝ} (hδ : 0 < δ)
    (h : (n : ℝ) ≤ (K : ℝ) * ((δ ^ s : NNReal) : ℝ)) :
    ((n : ℕ) : ENNReal) ≤ (K : ENNReal) * (δ : ENNReal) ^ s := by
  have hnn : (n : NNReal) ≤ K * (δ ^ s : NNReal) := by
    exact_mod_cast h
  have hen : ((n : NNReal) : ENNReal) ≤ (K : ENNReal) * ((δ ^ s : NNReal) : ENNReal) := by
    exact ENNReal.coe_le_coe.mpr hnn
  calc
    ((n : ℕ) : ENNReal) = ((n : NNReal) : ENNReal) := by simp
    _ ≤ (K : ENNReal) * ((δ ^ s : NNReal) : ENNReal) := hen
    _ = (K : ENNReal) * (δ : ENNReal) ^ s := by
      rw [ENNReal.coe_rpow_of_ne_zero hδ.ne' s]

/-- A point of the shaded union of `𝕍_{𝕊'}` is shaded by one of the bodies of `𝕎''_B`. This is
the step that produces the body `W₁` whose normal is the axis of the cone in blueprint
`lem:ml2tangentialSlabFibreCount`. -/
private lemma exists_shade_of_mem_slabsBodies (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {Wb' : Finset bd.ω} {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ShadedBody.iUnionShade (slabsBodies cfg Wb' slabOf 𝕊') YW) :
    ∃ j ∈ Wb', x ∈ (YW j).shade := by
  classical
  -- `hx` : `x` lies in the union of the shadings over `slabsBodies cfg Wb' slabOf 𝕊'`.
  rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hjx⟩
  -- `j ∈ slabsBodies cfg Wb' slabOf 𝕊'` unfolds (Finset.filter) to `j ∈ Wb'` plus a slab witness.
  rcases Finset.mem_filter.mp hj with ⟨hjW, hSlab⟩
  exact ⟨j, hjW, hjx⟩


/-- **The packing bound, read on a finite family of convex bodies.**

A finite set of convex bodies whose normals all lie within `α` of a fixed unit direction and
are pairwise `σ`-separated has at most `C_{lem:coneDirectionCount} (α/σ)²` elements. Distinct
bodies automatically have distinct normals here, because `σ > 0` while a direction makes angle
`0` with itself, so the count of bodies equals the count of normals and
`Kakeya.NonSlab.card_le_coneDirectionCount` applies directly.

This is the whole content of the covering argument of blueprint
`lem:ml2tangentialSlabFibreCount`, stated with no reference to `cfg`, `bd` or the slab family:
that is what keeps its elaboration cheap. Everything is phrased through
`Kakeya.VeryNotSticky.bodyNormal`, never through
`NonSlab.bodyNormal finrank_euclideanSpace_fin _`, whose repeated elaboration at
`EuclideanSpace ℝ (Fin 3)` exhausts the heartbeat budget. -/
private lemma card_le_coneDirectionCount_bodyNormal
    (F : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))))
    {v₀ : EuclideanSpace ℝ (Fin 3)} (hv₀ : ‖v₀‖ = 1) {σ α : ℝ} (hσ : 0 < σ) (hσα : σ ≤ α)
    (hcap : ∀ S ∈ F, NonSlab.lineAngle (bodyNormal S) v₀ ≤ α)
    (hsep : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' →
      σ ≤ NonSlab.lineAngle (bodyNormal S) (bodyNormal S')) :
    (F.card : ℝ) ≤ (NonSlab.coneDirectionCountConstant : ℝ) * (α / σ) ^ 2 := by
  classical
  -- injectivity of `bodyNormal` on `F`
  have hinj : Set.InjOn bodyNormal (F : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) := by
    intro S hSm S' hS'm heq
    by_contra hne
    have h1 := hsep S (Finset.mem_coe.mp hSm) S' (Finset.mem_coe.mp hS'm) hne
    rw [heq, NonSlab.lineAngle_self (bodyNormal_ne_zero S')] at h1
    linarith
  have hcard : (F.image bodyNormal).card = F.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  refine NonSlab.card_le_coneDirectionCount hσ hσα hv₀ (F.image bodyNormal) ?_ ?_ ?_
  · intro w hw
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hw
    exact norm_bodyNormal S
  · intro w hw
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hw
    exact hcap S hS
  · intro w hw w' hw' hne
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
    obtain ⟨S', hS', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw')
    exact hsep S hS S' hS' (fun h => hne (by rw [h]))

/-- The cap clause of the packing bound, in the `Kakeya.NonSlab.lineAngle` shape that
`Kakeya.NonSlab.card_le_coneDirectionCount` consumes. Same reason as
`Kakeya.VeryNotSticky.tangentialFibre_sep` for being a lemma of its own. -/
private lemma tangentialFibre_cap' (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} (ta : TypicalAngleData cfg tc hB τ')
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    {x : EuclideanSpace ℝ (Fin 3)} {j₁ : bd.ω} (hj₁ : j₁ ∈ ta.sel)
    (hxj₁ : x ∈ (ta.YW j₁).shade)
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (hxS : x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW) :
    NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
      3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ) := by
  rw [← axisAngle_eq_lineAngle]
  exact tangentialFibre_cap cfg ta htang hj₁ hxj₁ hS hxS

/-- **The packing step of blueprint `lem:ml2tangentialSlabFibreCount`, re-proved from the
cone-restricted (S4″).**

Any finite set `F` of slabs of the family, each of whose subfamilies shades the point `x`, has
at most `C^fib δ^{-2τ'}` elements.

**The route changed with the re-cut and the statement did not.** Before, the bound came from a
packing argument: clause (S4′) separated the normals of the slabs of `F` and
`Kakeya.NonSlab.card_le_coneDirectionCount` counted them inside the cone of aperture
`3 Ctyp δ^{-τ'} (a/b)` that typicality confines them to. The refined source's slab cells are
lattice translates and have no such separation, so (S4′) is gone; what it now reads is (S4″),
which *is* the count, at the `δ`-free `Kakeya.VeryNotSticky.slabConeCountConstant`. Both
geometric steps that fed the packing argument survive unchanged, and they are exactly the two
hypotheses (S4″) takes: the shaded point `x` of a body of `𝕎''_S` lies in the `C₀ a`-thickening
of `S`, and the normal of `S` lies in the cone of aperture `α = 3 Ctyp δ^{-τ'} (a/b)` about the
normal of the body `W₁ = bd.Wb j₁` shading `x` (`tangentialFibre_cap'`, unchanged). **That
second step is why the licensed clause is cone-restricted and the whole-family form is not
needed**: the consumer never counts slabs outside the cone.

The arithmetic is then: `F` injects into
`{S ∈ 𝕊 : x ∈ N_{C₀ a}(S) ∧ ∠(n(S), n(W₁)) ≤ α}`, (S4″) bounds that set's `ncard` by
`slabConeCountConstant(C₀) (α/(a/b) + 1)²`, the scale `a/b` cancels inside the clause
(`α/(a/b) = 3 Ctyp δ^{-τ'}`), and `1 ≤ Ctyp δ^{-τ'}` — from `ta.hCtyp1` and the tangential
guard through `tangentialFibre_scales` — turns `(3 Ctyp δ^{-τ'} + 1)²` into
`16 Ctyp² δ^{-2τ'}`, which is `slabDecompFibreConstant bd.C₀ ta.Ctyp · δ^{-2τ'}` by
`Kakeya.VeryNotSticky.slabDecompFibreConstant_eq`. -/
private lemma tangentialFibre_card_le (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} (ta : TypicalAngleData cfg tc hB τ')
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    {x : EuclideanSpace ℝ (Fin 3)} {j₁ : bd.ω} (hj₁ : j₁ ∈ ta.sel)
    (hxj₁ : x ∈ (ta.YW j₁).shade)
    (F : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))))
    (hF𝕊 : ∀ S ∈ F, S ∈ 𝕊)
    (hFx : ∀ S ∈ F, x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW) :
    (F.card : ℝ) ≤ (slabDecompFibreConstant bd.C₀ ta.Ctyp : ℝ) *
      ((cfg.δ ^ (-(2 * τ')) : NNReal) : ℝ) := by
  classical
  obtain ⟨hq, hpow⟩ := tangentialFibre_scales cfg ta htang
  have hqge : (0 : ℝ) < ((cfg.a / cfg.b : NNReal) : ℝ) := by exact_mod_cast hq
  have hdge : (1 : ℝ) ≤ ((cfg.δ ^ (-τ') : NNReal) : ℝ) := by exact_mod_cast hpow
  have hCtyp1 : (1 : ℝ) ≤ (ta.Ctyp : ℝ) := by exact_mod_cast ta.hCtyp1
  -- the cone aperture of `tangentialFibre_cap'`
  have hα0 : (0 : ℝ) ≤ 3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
      ((cfg.a / cfg.b : NNReal) : ℝ) :=
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (ta.Ctyp : ℝ))
      (NNReal.coe_nonneg _)) (NNReal.coe_nonneg _)
  -- `1 ≤ Ctyp δ^{-τ'}`, the step that turns the `+1` of the cell count into a factor `16/9`
  have ht : (1 : ℝ) ≤ (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) := by
    have h := mul_le_mul hCtyp1 hdge (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ (ta.Ctyp : ℝ))
    simpa using h
  -- The overlap condition gives the first cone-count membership.
  --  §C.4, condition C-C1, unchanged).  The shaded point `x` of a body of `𝕎''_S`
  -- lies in `N_{τ₂(W)}(W)` by the enlargement sandwich, and `τ₂(W) ≤ C₀ a` by (C4), so `x` is
  -- in the `C₀ a`-thickening of every slab of `F`.
  have hxth : ∀ S ∈ F, x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier := by
    intro S hSF
    obtain ⟨j, hjmem, hxj⟩ := Set.mem_iUnion₂.mp (hFx S hSF)
    have hjmem' : j ∈ slabBodies cfg ta.sel slabOf S := by simpa using hjmem
    have hjsel : j ∈ ta.sel := (Finset.mem_filter.mp hjmem').1
    have hjS : slabOf j = S := (Finset.mem_filter.mp hjmem').2
    have hjb : j ∈ (tc.thinBall hB).bodies' := ta.hsel hjsel
    have hjB : j ∈ bd.bodies B := (tc.thinBall hB).bodies'_subset hjb
    -- `x` lies in the carrier of the outer body `W j`
    have hxc : x ∈ ((tc.thinBall hB).W j).carrier := by
      have hcar := (ta.hrefine.1.2 j hjsel).1
      have hx1 : x ∈ (ta.YW j).carrier := (ta.YW j).shade_subset hxj
      rwa [show (ta.YW j).carrier = ((tc.thinBall hB).W j).carrier from
        congrArg ConvexSpaceBody.carrier hcar] at hx1
    -- the enlargement sandwich puts it in `N_{τ₂(Wb j)}(Wb j)`
    have hxN : x ∈ Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier := by
      have hle := (tc.thinBall hB).W_le_cthickening j hjb
      have hx2 : x ∈ (ConvexSpaceBody.cthickening (bd.Wb j).scale (bd.Wb j)).carrier :=
        (SetLike.coe_subset_coe.mpr hle) hxc
      rwa [ConvexSpaceBody.cthickening_carrier] at hx2
    -- the radius is at most `C₀ a`
    have hscale : (bd.Wb j).scale ≤ (bd.C₀ : ℝ) * (cfg.a : ℝ) := by
      have h2 := (bd.bodies_thickness B hB j hjB 2).2
      simp only [Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h2
      have : (bd.Wb j).scale = Metric.thickness ℝ (bd.Wb j).carrier 2 := by
        change Metric.thickness ℝ (bd.Wb j).carrier
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) = _
        rw [finrank_euclideanSpace_fin]
      rw [this]
      exact h2
    -- and the body sits inside its slab by (S3)
    have hbodyS : (bd.Wb j).carrier ⊆ S.carrier := by
      have := (hS.S3 j hjsel).2.1
      rwa [hjS] at this
    exact Metric.cthickening_mono hscale _
      (Metric.cthickening_subset_of_subset _ hbodyS hxN)
  -- the second membership: typicality confines the normals of `F` to one cone about `n(W₁)`
  have hxcap : ∀ S ∈ F, NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
      3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
        ((cfg.a / cfg.b : NNReal) : ℝ) := fun S hSF =>
    tangentialFibre_cap' cfg ta htang hj₁ hxj₁ hS (hFx S hSF)
  -- `F` sits inside the set (S4″) counts
  have hGfin : {S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
      NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
        3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
          ((cfg.a / cfg.b : NNReal) : ℝ)}.Finite :=
    hS.finite.subset (Set.sep_subset _ _)
  have hFG : (F : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) ⊆
      {S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
        NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
          3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
            ((cfg.a / cfg.b : NNReal) : ℝ)} := by
    intro S hSF
    exact ⟨hF𝕊 S (by simpa using hSF), hxth S (by simpa using hSF),
      hxcap S (by simpa using hSF)⟩
  have hcardle : (F.card : ℝ) ≤
      (({S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
        NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
          3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
            ((cfg.a / cfg.b : NNReal) : ℝ)}.ncard : ℕ) : ℝ) := by
    have h1 : (F : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))).ncard = F.card :=
      Set.ncard_coe_finset F
    have h2 : F.card ≤
        {S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
            3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
              ((cfg.a / cfg.b : NNReal) : ℝ)}.ncard := by
      rw [← h1]
      exact Set.ncard_le_ncard hFG hGfin
    exact_mod_cast h2
  -- (S4″) at `(x, n(W₁), α)`
  have hS4 := hS.S4'' x (bodyNormal (bd.Wb j₁))
    (3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) * ((cfg.a / cfg.b : NNReal) : ℝ)) hα0
  -- the scale `a/b` cancels inside the clause
  have hdiv : (3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
        ((cfg.a / cfg.b : NNReal) : ℝ)) / ((cfg.a / cfg.b : NNReal) : ℝ)
      = 3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) := by
    field_simp
  rw [hdiv] at hS4
  -- `(3 Ctyp δ^{-τ'} + 1)² ≤ 16 Ctyp² (δ^{-τ'})²`
  have hSCC0 : (0 : ℝ) ≤ (slabConeCountConstant bd.C₀ : ℝ) := NNReal.coe_nonneg _
  have hsq0 : ∀ t : ℝ, 1 ≤ t → (3 * t + 1) ^ 2 ≤ 16 * t ^ 2 := by
    intro t htt
    nlinarith [sq_nonneg (t - 1), htt]
  have hsq : (3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) + 1) ^ 2 ≤
      16 * (ta.Ctyp : ℝ) ^ 2 * ((cfg.δ ^ (-τ') : NNReal) : ℝ) ^ 2 := by
    have h := hsq0 ((ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ)) ht
    nlinarith [h]
  have hd2 : ((cfg.δ ^ (-(2 * τ')) : NNReal) : ℝ) = ((cfg.δ ^ (-τ') : NNReal) : ℝ) ^ 2 := by
    have : (cfg.δ ^ (-(2 * τ')) : NNReal) = (cfg.δ ^ (-τ') : NNReal) ^ (2 : ℕ) := by
      rw [← NNReal.rpow_natCast (cfg.δ ^ (-τ')) 2, ← NNReal.rpow_mul]
      norm_num
      ring_nf
    rw [this]
    push_cast
    ring
  have hfib : (slabDecompFibreConstant bd.C₀ ta.Ctyp : ℝ) =
      (slabConeCountConstant bd.C₀ : ℝ) * 16 * (ta.Ctyp : ℝ) ^ 2 := by
    rw [slabDecompFibreConstant]
    push_cast
    ring
  calc (F.card : ℝ)
      ≤ (({S ∈ 𝕊 | x ∈ Metric.cthickening ((bd.C₀ : ℝ) * (cfg.a : ℝ)) S.carrier ∧
          NonSlab.lineAngle (bodyNormal S) (bodyNormal (bd.Wb j₁)) ≤
            3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) *
              ((cfg.a / cfg.b : NNReal) : ℝ)}.ncard : ℕ) : ℝ) := hcardle
    _ ≤ (slabConeCountConstant bd.C₀ : ℝ) *
        (3 * (ta.Ctyp : ℝ) * ((cfg.δ ^ (-τ') : NNReal) : ℝ) + 1) ^ 2 := hS4
    _ ≤ (slabConeCountConstant bd.C₀ : ℝ) *
        (16 * (ta.Ctyp : ℝ) ^ 2 * ((cfg.δ ^ (-τ') : NNReal) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hSCC0
    _ = (slabDecompFibreConstant bd.C₀ ta.Ctyp : ℝ) * ((cfg.δ ^ (-(2 * τ')) : NNReal) : ℝ) := by
      rw [hfib, hd2]; ring

/-- **One fibre meets few slabs** (blueprint `lem:ml2tangentialSlabFibreCount`).

In the tangential case `θ < δ^{-τ'} a/b`, typicality of `θ` bounds the angle between the
*normals* of any two bodies of `𝕎''_B` sharing a shaded point by `Ctyp θ` (the field
`ta.hangle`), so the normals of the slabs of `𝕊'` whose subfamily shades a fixed point `x` all
lie in a cone of aperture `3 Ctyp δ^{-τ'} a/b` about the normal of any one body shading `x`.
Since the re-cut of (S4) to (S4″) the count is read off the clause itself
(`Kakeya.VeryNotSticky.slabConeCount`): at the shaded point `x` the slabs whose subfamily
shades `x` all contain `x` in their `C₀ a`-thickenings *and* have their normals in the cone of
aperture `α = 3 Ctyp δ^{-τ'} (a/b)` about `n(W₁)`, and (S4″) bounds how many of those there are
by `slabConeCountConstant(C₀) (α/(a/b) + 1)² ≤ C^fib δ^{-2τ'}`, the scale `a/b` cancelling.

Typicality travels in the bundle `ta`, through `ta.htyp` and `ta.Ctyp`, exactly as in
`Kakeya.VeryNotSticky.tangentialSlabDecomp`; the blueprint states it as "`θ` is a typical
angle for `(𝕎''_B, Y_{𝕎''_B})` with constant `C_{lem:ml2typicalangle}`, as produced by
Proposition `lem:ml2typicalangle`", which is what that bundle is.

**The signature.** Fourteen binder groups is above the usual threshold, so here is one line
per group, saying what the statement loses without it. The first five are the ambient data
that fix the meaning of every symbol on both sides and are all inferable from later
arguments: `cfg` is Configuration `hyp:ml2setup`, carrying `δ`, `a`, `b` and `r₁`; `τ'` is
the exponent of the tangential threshold, appearing in `htang` and in the conclusion; `bd` is
the per-ball data of `hyp:ml2setup`, carrying the index type `bd.ω`, the bodies `bd.Wb` and
the thickness constant `bd.C₀` of the conclusion; `tc` is the thin-case configuration, needed
only to type `ta`; `B` is the ball. Then: `hB` is `B ∈ 𝔅`, without which `tc.thinBall` — and
hence `ta` — has nothing to be about. `ta` is the typical-angle bundle, and it is what
supplies *four* separate ingredients of the statement, which is why it is a bundle and not
four binders: the index set `ta.sel = 𝕎''_B`, the shading `ta.YW`, the angle `ta.θ` and its
typicality constant `ta.Ctyp`; without typicality (`ta.htyp`) the cone in the proof has no
aperture bound and the conclusion is false. `𝕊` and `hS` are the slab family: `hS` supplies
(S4″), the cone-restricted point count, which `slabConeCount` names, and (S2), which fixes
their scale `a/b`; without them the slabs counted are arbitrary convex bodies and no bound
holds. `htang` is the tangential case hypothesis, `θ < δ^{-τ'} a/b`; without it the cone has
aperture `Ctyp θ` with `θ` unbounded and the count is not `δ^{-2τ'}`. `𝕊'` and `h𝕊'` are the
subfamily being counted and its inclusion in `𝕊`; `h𝕊'` is what makes `hS` apply to `𝕊'`, and
hence what makes the counted set finite. Finally `x` and `hx` are the fibre point: `hx` puts
`x` in the shaded union, which is what produces the body `W₁` whose normal is the axis of the
cone, and it is also the only route by which `ta.hCtyp1` — the lower bound `1 ≤ Ctyp` that the
aperture step `2θ + Ctyp θ ≤ 3 Ctyp θ` needs — becomes relevant; it is what the consumer
`tangentialSlabFibreCountMult` has available, `x` ranging over the domain of integration
`E = U(𝕍_{𝕊'}, Y)`.

The count is `Set.ncard`, Mathlib's cardinality of a set, and not the `card` of a `Finset`
built from `hS.finite.subset h𝕊'`: the blueprint counts
`#{S ∈ 𝕊' : x ∈ U(𝕎''_S, Y_{𝕎''_S})}`, a set, and phrasing the conclusion through
`Set.Finite.toFinset` would make it depend on the proof term `hS`. Finiteness is not lost —
`hS.finite.subset h𝕊'` still supplies it inside the proof — and `Set.ncard` of a finite set is
its cardinality. -/
theorem tangentialSlabFibreCount (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ')
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    {𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))} (h𝕊' : 𝕊' ⊆ 𝕊)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ShadedBody.iUnionShade (slabsBodies cfg ta.sel slabOf 𝕊') ta.YW) :
    ({S ∈ 𝕊' | x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW}.ncard :
        ENNReal) ≤
      (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * τ')) := by
  classical
  obtain ⟨j₁, hj₁, hxj₁⟩ := exists_shade_of_mem_slabsBodies cfg hx
  have hfin : {S ∈ 𝕊' | x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW}.Finite :=
    (hS.finite.subset h𝕊').subset (Set.sep_subset _ _)
  have hF𝕊 : ∀ S ∈ hfin.toFinset, S ∈ 𝕊 := fun S hSF =>
    h𝕊' ((Set.Finite.mem_toFinset hfin).mp hSF).1
  have hFx : ∀ S ∈ hfin.toFinset,
      x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW := fun S hSF =>
    ((Set.Finite.mem_toFinset hfin).mp hSF).2
  have hreal := tangentialFibre_card_le cfg ta hS htang hj₁ hxj₁ hfin.toFinset hF𝕊 hFx
  have hncard :
      {S ∈ 𝕊' | x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW}.ncard
        = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hncard]
  exact ennreal_natCast_le_of_real_le cfg.hδ hreal

/-- **From the fibre count to a multiplicity bound** (blueprint
`lem:ml2tangentialSlabFibreCountMult`).

Applying `MeasureTheory.sum_measure_inter_eq_setLIntegral_card` to the shaded unions
`U(𝕎''_S, Y_{𝕎''_S})`, `S ∈ 𝕊'`, over `E = U(𝕍_{𝕊'}, Y)` turns the pointwise bound
`tangentialFibreSlabCount` of `Kakeya.VeryNotSticky.tangentialSlabFibreCount` into
`μ(𝕍_{𝕊'}, Y) ≤ C^fib δ^{-2τ'} max_{S ∈ 𝕊'} μ(𝕎''_S, Y_{𝕎''_S})`.

The maximum is rendered existentially, as a slab realising it: `𝕊'` is finite and, since
`𝕍_{𝕊'} ≠ ∅`, has a slab with nonempty subfamily, so the two forms agree, and the existential
is what the one consumer, `Kakeya.VeryNotSticky.tangentialSlabDecompMultChain`, uses. The two
positivity hypotheses are not decoration: without `hne` the maximum is over an empty set, and
without `hU` the final division is illegitimate.

**The signature.** It is that of `Kakeya.VeryNotSticky.tangentialSlabFibreCount` with the
fibre point `(x, hx)` — which is integrated out — replaced by the two positivity hypotheses
`hne` and `hU`, so the account of the first twelve groups given in that docstring applies
verbatim: `cfg`, `τ'`, `bd`, `tc`, `B` are the ambient data, `hB` places `B` in `𝔅`, `ta`
bundles `𝕎''_B = ta.sel`, its shading `ta.YW`, the angle `ta.θ` and the typicality constant
`ta.Ctyp`, `𝕊`/`hS` are the slab family with (S1)–(S3), `htang` is the tangential case
hypothesis, and `𝕊'`/`h𝕊'` are the subfamily and its inclusion. The last two are as described
above. -/
theorem tangentialSlabFibreCountMult (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ')
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    {𝕊' : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))} (h𝕊' : 𝕊' ⊆ 𝕊)
    (hne : (slabsBodies cfg ta.sel slabOf 𝕊').Nonempty)
    (_hU : 0 < volume (ShadedBody.iUnionShade (slabsBodies cfg ta.sel slabOf 𝕊') ta.YW)) :
    ∃ S ∈ 𝕊', ShadedBody.multiplicity (slabsBodies cfg ta.sel slabOf 𝕊') ta.YW ≤
      (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * τ')) *
        ShadedBody.multiplicity (slabBodies cfg ta.sel slabOf S) ta.YW := by
  classical
  let F : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
    (hS.finite.subset h𝕊').toFinset
  let A : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun S => ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW
  let E := ShadedBody.iUnionShade (slabsBodies cfg ta.sel slabOf 𝕊') ta.YW
  let M : ENNReal :=
    (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * τ'))
  -- (a) the finite index set `F` is nonempty.
  have hFne : F.Nonempty := by
    rcases hne with ⟨j, hj⟩
    rw [slabsBodies] at hj
    exact ⟨slabOf j,
      (Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mpr (Finset.mem_filter.mp hj).2⟩
  -- (b) every `A S`, `S ∈ F`, is contained in `E`.
  have hsub : ∀ S ∈ F, A S ⊆ E := by
    intro S hSF x hx
    have hS𝕊' : S ∈ 𝕊' := (Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mp hSF
    dsimp [A] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨j, hjS, hjx⟩
    have hjW : j ∈ ta.sel := (Finset.mem_filter.mp hjS).1
    have hmem : j ∈ slabsBodies cfg ta.sel slabOf 𝕊' :=
      Finset.mem_filter.mpr ⟨hjW, by rw [(Finset.mem_filter.mp hjS).2]; exact hS𝕊'⟩
    change x ∈ ShadedBody.iUnionShade (slabsBodies cfg ta.sel slabOf 𝕊') ta.YW
    exact Set.mem_iUnion₂.mpr ⟨j, hmem, hjx⟩
  -- (c) the `A S` and `E` are measurable.
  have hmeasA : ∀ S ∈ F, MeasurableSet (A S) := by
    intro S hS
    simpa [A] using
      ShadedBody.measurableSet_iUnion_shade (s := slabBodies cfg ta.sel slabOf S) (V := ta.YW)
  have hmeasE : MeasurableSet E := by
    simpa [E] using
      ShadedBody.measurableSet_iUnion_shade (s := slabsBodies cfg ta.sel slabOf 𝕊') (V := ta.YW)
  -- (d) pointwise fibre bound, bridging `Finset.card` to `Set.ncard`.
  have hcard : ∀ x ∈ E, ({S ∈ F | x ∈ A S}.card : ENNReal) ≤ M := by
    intro x hx
    have hfib := tangentialSlabFibreCount cfg hB ta hS htang h𝕊' hx
    have hset : (F.filter (fun S => x ∈ A S) : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) =
        ({S ∈ 𝕊' | x ∈ A S} : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) := by
      ext S
      simp only [Finset.mem_coe, Finset.mem_filter, F]
      constructor <;> intro ⟨h1, h2⟩
      · exact ⟨(Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mp h1, h2⟩
      · exact ⟨(Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mpr h1, h2⟩
    have hcard' : ({S ∈ F | x ∈ A S}.card : ENNReal) =
        ({S ∈ 𝕊' | x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW}.ncard :
            ENNReal) := by
      calc
        ({S ∈ F | x ∈ A S}.card : ENNReal)
            = ((F.filter (fun S => x ∈ A S) : Finset (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) :
                Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))).ncard := by
              rw [Set.ncard_coe_finset]
        _ = ({S ∈ 𝕊' | x ∈ A S}.ncard : ENNReal) := by rw [← hset]
        _ = ({S ∈ 𝕊' | x ∈ ShadedBody.iUnionShade (slabBodies cfg ta.sel slabOf S) ta.YW}.ncard :
            ENNReal) := by
              simp [A]
    rw [hcard']
    exact hfib
  -- (e) sum the fibre bound over the index set `F`.
  have hsum : ∑ S ∈ F, volume (A S) ≤ M * volume E := by
    exact MeasureTheory.sum_measure_le_mul_measure_of_card_le (μ := volume) (s := F) (A := A)
      hmeasA (F := E) hmeasE hsub (M := M) hcard
  -- (f) pick the slab `S₀` maximising `μ(𝕎''_S, Y)` over the nonempty `F`.
  let μS : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) → ENNReal :=
    fun S => ShadedBody.multiplicity (slabBodies cfg ta.sel slabOf S) ta.YW
  rcases Finset.exists_max_image F μS hFne with ⟨S₀, hS₀F, hmax⟩
  -- (g) slabwise mass: `∑_{W ∈ 𝕍_{𝕊'}} |Y(W)| ≤ μS S₀ · |U(𝕍_{𝕊'}, Y)|`.
  have hmass : ∑ j ∈ slabsBodies cfg ta.sel slabOf 𝕊', volume (ta.YW j).shade ≤
      (M * μS S₀) * volume E := by
    calc
      ∑ j ∈ slabsBodies cfg ta.sel slabOf 𝕊', volume (ta.YW j).shade
          = ∑ S ∈ F, ∑ j ∈ slabBodies cfg ta.sel slabOf S, volume (ta.YW j).shade := by
            simpa [F] using
              (sum_slabBodies_eq_sum_slabsBodies cfg (B := B) (Wb' := ta.sel) (θ := ta.θ)
                hS h𝕊' (fun j => volume (ta.YW j).shade)).symm
      _ = ∑ S ∈ F, μS S * volume (A S) := by
            refine Finset.sum_congr rfl fun S hS => ?_
            simpa [μS, A] using
              (ShadedBody.sum_shade_eq_multiplicity_mul_union
                (s := slabBodies cfg ta.sel slabOf S) (V := ta.YW))
      _ ≤ ∑ S ∈ F, μS S₀ * volume (A S) := by
            refine Finset.sum_le_sum ?_
            intro S hS
            gcongr
            exact hmax S hS
      _ = μS S₀ * ∑ S ∈ F, volume (A S) := by rw [← Finset.mul_sum]
      _ ≤ μS S₀ * (M * volume E) := by
            exact mul_le_mul_of_nonneg_left hsum (zero_le : 0 ≤ μS S₀)
      _ = (M * μS S₀) * volume E := by ring
  have hunion : ShadedBody.multiplicity (slabsBodies cfg ta.sel slabOf 𝕊') ta.YW ≤ M * μS S₀ := by
    rw [ShadedBody.multiplicity_le_iff]
    simpa [E] using hmass
  exact ⟨S₀, (Set.Finite.mem_toFinset (hS.finite.subset h𝕊')).mp hS₀F,
    by simpa [M, μS] using hunion⟩

/-- **The density chain at a dense slab** (blueprint `lem:ml2tangentialDensityChain`).

`δ^{8η} ≤ C_{lem:ml2tangentialSlabDecomp} λ(𝕎''_S, Y_{𝕎''_S})` for every dense slab `S`, with
`C_{lem:ml2tangentialSlabDecomp} = 100 tc.C` the constant
`Kakeya.VeryNotSticky.tangentialSlabDecompConstant`. This is the `dense` field of
`Kakeya.VeryNotSticky.IsDenseSlab`, and it is the density clause of
`Kakeya.VeryNotSticky.tangentialSlabDecomp`.

Four inequalities chain: `δ^{2η} ≤ c` (`ta.hc`, blueprint `tangentialRefinementFactor`),
`δ^{6η} ≤ tc.C λ(𝕎'_B, Y_{𝕎'_B})` ((T2), `ThinCase.ThinBall.fullness_bodies` at the `tb` index
`2η`),
`c λ(𝕎'_B, Y_{𝕎'_B}) ≤ λ(𝕎''_B, Y_{𝕎''_B})`
(`ShadedBody.IsCRefinement.mul_fullness_le`, blueprint `lem:ml2fullnessRefine`), and
`λ(𝕎''_B, Y_{𝕎''_B}) ≤ 100 λ(𝕎''_S, Y_{𝕎''_S})`
(`Kakeya.VeryNotSticky.tangentialDenseSlabs_fullness_le`).

The exponent is `8η`: the two factors — the `δ^{6η}` of (T2) at the `tb` index `2η` (F8) and
the `δ^{2η}` of the refinement — are independent and neither can be dropped, and the blueprint
gives a counterexample to the `2η` form.

No slab-family *hypothesis* is a binder: no link of the chain reads
`Kakeya.VeryNotSticky.IsSlabFamily`, in particular not its partition clause (S3), and the
only thing `hSd` is used for is the pair of clauses `(slabBodies … S).Nonempty` and the
division-free density inequality of `Kakeya.VeryNotSticky.denseSlabs`. The family `𝕊` itself
is still an (implicit) binder, carried purely so that the hypothesis can be stated in the
membership form `S ∈ 𝕊_dens` that `Kakeya.VeryNotSticky.tangentialSlabDecompMultChain`
produces and `Kakeya.VeryNotSticky.tangentialDenseSlabs_fullness_le` consumes; it is inferred
from `hSd` at every call site. -/
theorem tangentialDensityChain (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ')
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hSd : S ∈ denseSlabs cfg ta.sel slabOf ta.YW 𝕊) :
    (cfg.δ : ENNReal) ^ (8 * cfg.η) ≤
      ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) *
        (ShadedBody.fullness (slabBodies cfg ta.sel slabOf S) ta.YW : ENNReal) := by
  classical
  let hrefl : ShadedBody.IsCRefinement (tc.thinBall hB).bodies' (tc.thinBall hB).W
      (tc.thinBall hB).bodies' (tc.thinBall hB).W 1 :=
    ⟨⟨subset_rfl, fun i _ => ⟨rfl, Set.Subset.rfl⟩⟩, by simp⟩
  have hVol' : 0 < ∑ j ∈ (tc.thinBall hB).bodies',
      volume ((tc.thinBall hB).W j).carrier :=
    thinBallPositivity_carrier_pos cfg tc hB (c := 1) one_pos hrefl
  -- positivity of the selected slab's bodies
  have hvolS : 0 < ∑ j ∈ slabBodies cfg ta.sel slabOf S, volume (ta.YW j).carrier := by
    rcases hSd.2.1 with ⟨j, hj⟩
    have hj_sel : j ∈ ta.sel := (Finset.mem_filter.mp hj).1
    have hj_body : j ∈ (tc.thinBall hB).bodies' := ta.hsel hj_sel
    have hEq : volume (ta.YW j).carrier = volume ((tc.thinBall hB).W j).carrier := by
      rw [show (ta.YW j).toConvexSpaceBody = ((tc.thinBall hB).W j).toConvexSpaceBody from
        (ta.hrefine.1.2 j hj_sel).1]
    have hpos_j : 0 < volume (ta.YW j).carrier := by
      rw [hEq]
      exact (tc.thinBall hB).volume_W_pos
        (fun i hi => volume_body_pos cfg bd hB ((tc.thinBall hB).bodies'_subset hi)) j hj_body
    have hnonneg : ∀ i ∈ slabBodies cfg ta.sel slabOf S,
        0 ≤ volume (ta.YW i).carrier := by
      intro i hi
      positivity
    exact lt_of_lt_of_le hpos_j
      (Finset.single_le_sum (s := slabBodies cfg ta.sel slabOf S)
        (f := fun i => volume (ta.YW i).carrier) hnonneg hj)
  -- the chain
  have hδE_ne0 : (cfg.δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδE_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top (r := cfg.δ)
  -- (1) δ^(2η) ≤ c, cast
  have hcE : (cfg.δ : ENNReal) ^ (2 * cfg.η) ≤ (ta.c : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne' (2 * cfg.η)]
    exact_mod_cast ta.hc
  -- (3)
  have h3n : ta.c * ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
      ShadedBody.fullness ta.sel ta.YW :=
    ShadedBody.IsCRefinement.mul_fullness_le ta.sel ta.YW
      (tc.thinBall hB).bodies' (tc.thinBall hB).W hVol' ta.hrefine
  have h3 : (ta.c : ENNReal) *
      (ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W : ENNReal) ≤
      (ShadedBody.fullness ta.sel ta.YW : ENNReal) := by
    exact_mod_cast h3n
  -- (4)
  have h4n : ShadedBody.fullness ta.sel ta.YW ≤
      100 * ShadedBody.fullness (slabBodies cfg ta.sel slabOf S) ta.YW :=
    tangentialDenseSlabs_fullness_le cfg ta.YW hSd hvolS
  have h4 : (ShadedBody.fullness ta.sel ta.YW : ENNReal) ≤
      (100 : ENNReal) * (ShadedBody.fullness (slabBodies cfg ta.sel slabOf S) ta.YW : ENNReal) := by
    exact_mod_cast h4n
  calc
    (cfg.δ : ENNReal) ^ (8 * cfg.η)
        = (cfg.δ : ENNReal) ^ ((2 * cfg.η) + 3 * (2 * cfg.η)) := by
          congr 1
          ring
    _ = (cfg.δ : ENNReal) ^ (2 * cfg.η) * (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) := by
          rw [ENNReal.rpow_add (2 * cfg.η) (3 * (2 * cfg.η)) hδE_ne0 hδE_ne_top]
    _ ≤ (ta.c : ENNReal) * (cfg.δ : ENNReal) ^ (3 * (2 * cfg.η)) := by
          gcongr
    _ ≤ (ta.c : ENNReal) * ((tc.C : ENNReal) *
          (ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W : ENNReal)) := by
          gcongr
          exact (tc.thinBall hB).fullness_bodies
    _ ≤ ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) *
          (ShadedBody.fullness (slabBodies cfg ta.sel slabOf S) ta.YW : ENNReal) := by
          rw [tangentialSlabDecompConstant]
          calc
            (ta.c : ENNReal) * ((tc.C : ENNReal) *
                (ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W : ENNReal))
                = (tc.C : ENNReal) * ((ta.c : ENNReal) *
                    (ShadedBody.fullness (tc.thinBall hB).bodies' (tc.thinBall hB).W : ENNReal)) :=
                  by ring
            _ ≤ (tc.C : ENNReal) * (ShadedBody.fullness ta.sel ta.YW : ENNReal) := by
                  gcongr
            _ ≤ (tc.C : ENNReal) * ((100 : ENNReal) *
                  (ShadedBody.fullness (slabBodies cfg ta.sel slabOf S) ta.YW : ENNReal)) := by
                  gcongr
            _ = ((100 * tc.C : NNReal) : ENNReal) *
                  (ShadedBody.fullness (slabBodies cfg ta.sel slabOf S) ta.YW : ENNReal) := by
                  rw [← mul_assoc, mul_comm (tc.C : ENNReal) (100 : ENNReal)]
                  norm_num


/-- **The multiplicity chain at a dense slab** (blueprint
`lem:ml2tangentialSlabDecompMultChain`).

Three steps, all in the direction `μ(coarse) ≤ c⁻¹ μ(fine)` that
`ShadedBody.IsCRefinement.mul_multiplicity_le` (blueprint `lem:ml2multRefine`) provides:

`μ(𝕎'_B) ≤ δ^{-2η} μ(𝕎''_B) ≤ δ^{-2η} (100/99) μ(𝕎'''_B)
  ≤ δ^{-2η} (100/99) C^fib δ^{-2τ'} μ(𝕎''_S)`,

the first by `ta.hrefine` and `ta.hc`, the second by
`Kakeya.VeryNotSticky.tangentialDenseSlabs_isCRefinement` and the third by
`Kakeya.VeryNotSticky.tangentialSlabFibreCountMult` at `𝕊' = 𝕊_dens`. Their side conditions
are supplied by the `Kakeya.VeryNotSticky.thinBallPositivity_*` group.

The returned slab lies in `𝕊_dens`, so it satisfies every clause of
`Kakeya.VeryNotSticky.IsDenseSlab` at `Wd = slabBodies cfg ta.sel slabOf S`: the geometric ones
by `Kakeya.VeryNotSticky.IsSlabFamily` and the definition of `slabBodies`, and the density one
by `Kakeya.VeryNotSticky.tangentialDensityChain`. -/
theorem tangentialSlabDecompMultChain (cfg : VeryNotSticky.{u}) {τ' : ℝ} {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ')
    {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
    {slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hS : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf)
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b)) :
    ∃ S ∈ denseSlabs cfg ta.sel slabOf ta.YW 𝕊,
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
        (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
          (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) *
          ShadedBody.multiplicity (slabBodies cfg ta.sel slabOf S) ta.YW := by
  classical
  let 𝕊d : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :=
    denseSlabs cfg ta.sel slabOf ta.YW 𝕊
  have h𝕊d : denseSlabs cfg ta.sel slabOf ta.YW 𝕊 ⊆ 𝕊 := fun S hSd => hSd.1
  let μ₁ : ENNReal := ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
  let μ₂ : ENNReal := ShadedBody.multiplicity ta.sel ta.YW
  let μ₃ : ENNReal := ShadedBody.multiplicity (slabsBodies cfg ta.sel slabOf 𝕊d) ta.YW
  change ∃ S ∈ 𝕊d, μ₁ ≤ (100 / 99 : ENNReal) *
    (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
    (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) *
    ShadedBody.multiplicity (slabBodies cfg ta.sel slabOf S) ta.YW
  -- δ viewed as an ENNReal
  have hδpos : (0 : ENNReal) < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδne0 : (cfg.δ : ENNReal) ≠ 0 := hδpos.ne'
  have hδne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- positivity of the composed refinement factor `ta.c * (99/100)`
  have hδpow_pos : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (2 * cfg.η) :=
    ENNReal.rpow_pos hδpos hδne_top
  have hδ_le_cE : (cfg.δ : ENNReal) ^ (2 * cfg.η) ≤ (ta.c : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ) (2 * cfg.η)]
    exact ENNReal.coe_le_coe.mpr ta.hc
  have hc_pos_E : (0 : ENNReal) < (ta.c : ENNReal) := lt_of_lt_of_le hδpow_pos hδ_le_cE
  have hc_pos : 0 < ta.c := ENNReal.coe_pos.mp hc_pos_E
  have hcpos : 0 < ta.c * (99 / 100 : NNReal) := mul_pos hc_pos (by norm_num)
  -- the composed refinement `V := slabsBodies cfg ta.sel slabOf 𝕊d` of `𝕎'_B`
  let hdense : ShadedBody.IsCRefinement (slabsBodies cfg ta.sel slabOf 𝕊d) ta.YW ta.sel ta.YW
      (99 / 100) :=
    tangentialDenseSlabs_isCRefinement cfg hS ta.YW
  have hVref : ShadedBody.IsCRefinement (slabsBodies cfg ta.sel slabOf 𝕊d) ta.YW
      (tc.thinBall hB).bodies' (tc.thinBall hB).W (ta.c * (99 / 100 : NNReal)) :=
    ShadedBody.IsCRefinement.trans hdense ta.hrefine
  have hne : (slabsBodies cfg ta.sel slabOf 𝕊d).Nonempty :=
    thinBallPositivity_nonempty cfg tc hB hcpos hVref
  have hU : 0 < volume (ShadedBody.iUnionShade (slabsBodies cfg ta.sel slabOf 𝕊d) ta.YW) :=
    thinBallPositivity_iUnionShade_pos cfg tc hB hcpos hVref
  -- STEP 1: μ₁ ≤ δ^{-2η} μ₂ from ta.hrefine and ta.hc
  have hδpow_ne0 : (cfg.δ : ENNReal) ^ (2 * cfg.η) ≠ 0 := ne_of_gt hδpow_pos
  have hδpow_ne_top : (cfg.δ : ENNReal) ^ (2 * cfg.η) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδne0 hδne_top
  have hδpow_def : ((cfg.δ : ENNReal) ^ (2 * cfg.η))⁻¹ = (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) := by
    rw [← ENNReal.rpow_neg]
  have hfine1 : (ta.c : ENNReal) * μ₁ ≤ μ₂ :=
    ShadedBody.IsCRefinement.mul_multiplicity_le (s := (tc.thinBall hB).bodies')
      (V := (tc.thinBall hB).W) (s' := ta.sel) (V' := ta.YW) ta.hrefine
  have hm1 : (cfg.δ : ENNReal) ^ (2 * cfg.η) * μ₁ ≤ μ₂ := by
    calc
      (cfg.δ : ENNReal) ^ (2 * cfg.η) * μ₁ ≤ (ta.c : ENNReal) * μ₁ := by gcongr
      _ ≤ μ₂ := hfine1
  have hstep1 : μ₁ ≤ (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * μ₂ := by
    calc
      μ₁ = ((cfg.δ : ENNReal) ^ (2 * cfg.η))⁻¹ *
          (((cfg.δ : ENNReal) ^ (2 * cfg.η)) * μ₁) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hδpow_ne0 hδpow_ne_top, one_mul]
      _ ≤ ((cfg.δ : ENNReal) ^ (2 * cfg.η))⁻¹ * μ₂ := by
            gcongr
      _ = (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * μ₂ := by
            rw [hδpow_def]
  -- STEP 2: μ₂ ≤ (100/99) μ₃ from the dense-slab refinement
  have hfine2 : (99 / 100 : ENNReal) * μ₂ ≤ μ₃ := by
    have hres : ((99 / 100 : NNReal) : ENNReal) * μ₂ ≤ μ₃ :=
      ShadedBody.IsCRefinement.mul_multiplicity_le (s := ta.sel) (V := ta.YW)
        (s' := slabsBodies cfg ta.sel slabOf 𝕊d) (V' := ta.YW) hdense
    have hm99 : ((99 / 100 : NNReal) : ENNReal) = (99 / 100 : ENNReal) := by norm_num
    rwa [hm99] at hres
  have hstep2 : μ₂ ≤ (100 / 99 : ENNReal) * μ₃ := by
    have hprod : (100 / 99 : ENNReal) * (99 / 100 : ENNReal) = 1 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        (100 * (99 : ENNReal)⁻¹) * (99 * (100 : ENNReal)⁻¹)
            = 100 * ((99 : ENNReal)⁻¹ * 99) * (100 : ENNReal)⁻¹ := by ac_rfl
        _ = 100 * (100 : ENNReal)⁻¹ := by
              rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
        _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    calc
      μ₂ = (100 / 99 : ENNReal) * ((99 / 100 : ENNReal) * μ₂) := by
            rw [← mul_assoc, hprod, one_mul]
      _ ≤ (100 / 99 : ENNReal) * μ₃ := by
            gcongr
  -- STEP 3: the fibre-count multiplicity bound at 𝕊d
  have hstep3 : ∃ S ∈ 𝕊d,
      μ₃ ≤ (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * τ')) *
        ShadedBody.multiplicity (slabBodies cfg ta.sel slabOf S) ta.YW := by
    exact tangentialSlabFibreCountMult cfg hB ta hS htang h𝕊d hne hU
  -- combine
  rcases hstep3 with ⟨S, hSd, hcoef⟩
  refine ⟨S, hSd, ?_⟩
  let μ₄ : ENNReal := ShadedBody.multiplicity (slabBodies cfg ta.sel slabOf S) ta.YW
  change μ₁ ≤ (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
    (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) * μ₄
  have hδcomb : (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * (cfg.δ : ENNReal) ^ (-(2 * τ')) =
      (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) := by
    rw [← ENNReal.rpow_add (-(2 * cfg.η)) (-(2 * τ')) hδne0 hδne_top]
    have hexp : -(2 * cfg.η) + -(2 * τ') = -(2 * τ') - 2 * cfg.η := by ring
    rw [hexp]
  calc
    μ₁ ≤ (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * μ₂ := hstep1
    _ ≤ (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * ((100 / 99 : ENNReal) * μ₃) := by
          gcongr
    _ ≤ (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) *
          ((100 / 99 : ENNReal) * ((slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
            (cfg.δ : ENNReal) ^ (-(2 * τ')) * μ₄)) := by
          gcongr
    _ = (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
          (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) * μ₄ := by
      have hre : (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) *
          ((100 / 99 : ENNReal) * ((slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
            (cfg.δ : ENNReal) ^ (-(2 * τ')) * μ₄)) =
          (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
            ((cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * (cfg.δ : ENNReal) ^ (-(2 * τ'))) * μ₄ := by
            ac_rfl
      rw [hre, hδcomb]

/-- **Constant in `Kakeya.VeryNotSticky.slabCard`** (blueprint
`def:ml2tangentialSlabDeltamaxConstant`, `C^Δ_{lem:ml2tangentialSlabDeltamax}`).

`CΔ` is *admissible* if it dominates the product of three losses: (a) the constant implicit in
the `⪅` of `factmaxmod2` of blueprint `lemmafactmaxbias`, at the ball `B` and the bias `ϱ`;
(b) the constant by which the anisotropic transport of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` distorts `Δ_max`; and (c) the square of the
absolute constant of blueprint `def:tubeCountFromDeltamaxConstant`.

Like `Kakeya.VeryNotSticky.IsSlabDecompMultConstant` this is a *predicate* on a constant and
not a formula, because (a) comes from a `⪅`, which `Kakeya.LEApprox` supplies only
existentially. Item (a) is the `Cbias` of `Kakeya.VeryNotSticky.BallData.bodies_antiClustering`,
the constant of GWZ (83) at `U = B` (clause (C4)); a producer of `SlabPackage` meets clause
(A3) from that field alone once `Cbias ≤ CΔ`, so it need not be
recorded here. Item (b) has no Lean form yet — it is precisely what clause (A3) of
`IsAnisotropicSlabRescale` assumes rather than derives — so what is recorded is item
(c), in the Lean shape it takes here: counting the rescaled bodies against the unit ball
through `ConvexSpaceBody.IsKatzTao.card_le_div_real` costs the reciprocal `3! = 6` of the
inscribed-simplex constant of `Convex.prod_thickness_le_volumeReal`, the volume `|B₁| ≤ 8` of
the unit ball and the cube `C₀³` of the thickness comparison constant, a product at most
`2^10 C₀³`. The predicate would have to be strengthened if (b) acquired a Lean form.

It is carried as `Kakeya.VeryNotSticky.SlabPackage.CΔAdmissible`, and `card_le` is what
`Kakeya.VeryNotSticky.slabCard` reads: together with the fixed-scale threshold
`SlabPackage.CΔ_le`, `CΔ ≤ δ^{-ϱ/2}`, it
gives `2^10 C₀³ ≤ δ^{-ϱ/2}`, which is exactly the absorption that step needs. An earlier version
stated that consequence again as a field of
`Kakeya.VeryNotSticky.SlabMultKT` and left this structure unused, which both axiomatised the
same bound twice and hid an extra assumption in that bundle. Note also that `one_le` is not
independent of `card_le`, since `C₀ ≥ 1`; it is kept because it is the sense in which `CΔ` is
a *loss*, and it is what the docstrings of the transport clauses appeal to.

What is used, and all that is used, is that some admissible `CΔ` is a function of `C₀`, of
`Cbias` and of absolute constants alone: independent of `S`, of `W` and of the scales `a`,
`b`, `r₁`, and sub-polynomial in `δ⁻¹`, so that the threshold `SlabPackage.CΔ_le` is
available. It is never a power of `δ`. -/
structure IsSlabDeltamaxConstant (C₀ CΔ : NNReal) : Prop where
  /-- `CΔ` is a genuine multiplicative loss -/
  one_le : 1 ≤ CΔ
  /-- item (c): `CΔ` dominates the absolute constant of the tube count against the unit ball -/
  card_le : (2 : NNReal) ^ 10 * C₀ ^ 3 ≤ CΔ

/-! ### The input bundles of the tangential leaf -/

/-- **Katz–Tao input for the multiplicity inside a slab** (blueprint
`lem:ml2tangentialSlabMult`(i)–(ii), i.e. the analytic half of `lem:ml2tangential`(b)).

The threshold exponent `η₁` is the opaque fullness threshold that GWZ Lemma 3.7 (blueprint
`genKKT`, `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`) attaches to the pair
`(ϱ, β)`, and it is what `Kakeya.VeryNotSticky.KTRho2ScaleData` demands on the fullness side
of the estimate: fullness at `δ^{η₁}`. The one threshold field connects it to the chain that
has to discharge that side, and it is not implied by `Kakeya.VeryNotSticky.CaseParams`, whose
budgets relate `η` to `ϱ` and say nothing about either against `η₁`:

* `fullness_threshold`, `9η ≤ η₁`, lets the density chain of blueprint
  `lem:ml2tangentialSlabFull` — which produces `λ(𝕋̃, Y_{𝕋̃}) ≥ δ^{9η}`, the `8η` of the
  density clause of `Kakeya.VeryNotSticky.tangentialSlabDecomp` plus the ninth `η` that
  `densityConstant` spends on the constant — discharge the fullness side.

The Katz–Tao side has no threshold clause. `estimate` is read at the `Δ_max` level `δ^{-3ϱ}`
that `Kakeya.VeryNotSticky.slabKatzTao` supplies — clause (A3) of
`Kakeya.VeryNotSticky.IsAnisotropicSlabRescale`, `CΔ δ^{-2ϱ}`, with the threshold
`CΔ ≤ δ^{-ϱ/2}` gives `Δ_max ≤ δ^{-5ϱ/2}` for the rescaled *geometric* family, and one
further half-power `δ^{-ϱ/2}` pays for the passage to the rescaled *shaded* family, whose
carriers are the enlarged ones, through
`Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement` — and at the loss
`4ϱ ≥ ϱ + 3ϱ(1-β)`, which is what Lemma 3.7 gives with `Δ_max^{1-β}` as a factor (GWZ (104):
`δ^{-O(ηbias)} δ^{-ηbias(1-β)} |𝕋̃|^β`). An earlier version carried a second field
`katzTao_threshold`, `3ϱ ≤ η₁`, and read `estimate` at the diagonal `(ϱ, η₁, η₁)` of
`KTRho2ScaleData`; the pair was jointly unsatisfiable for `β < 2/3`, since
`η₁(ϱ, β) ≤ ϱ/(1-β)` for every threshold `K_KT(β)` can provide.

`densityConstant` is blueprint `tangentialSlabDensityThreshold`, item (ii): the fixed-scale
threshold discharging the constant `tangentialSlabDecompConstant tc.C` of the density clause
against one further power `δ^{-η}`. -/
structure SlabMultKT (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) where
  /-- the fullness threshold exponent `η₁(ϱ, β)` of GWZ Lemma 3.7 (blueprint `genKKT`) -/
  η₁ : ℝ
  /-- `9η ≤ η₁`: the density chain reaches the fullness threshold.

  It reads `9η` and not `8η` because `Kakeya.VeryNotSticky.IsDenseSlab.dense` reads `8η`
  (which in turn follows `Kakeya.ThinCase.ThinBall.fullness_bodies` at `δ^{3η}`, read at the
  `tb` index `2η` — the (C5) exponent in the density clause) and
  `densityConstant` below charges one further `η`. This is a lower bound on **`η₁`**, not on
  `η`: `η₁` is the exponent threshold that GWZ Lemma 3.7 attaches to the pair `(ϱ, β)` and it
  is chosen after `η`, so raising the coefficient only forces a larger `η₁`. -/
  fullness_threshold : 9 * cfg.η ≤ η₁
  /-- GWZ Lemma 3.7 (`genKKT`) at this `δ` for bodies comparable to `ρ₂`-tubes, read at the
  `Δ_max` level `δ^{-3ϱ}` that `Kakeya.VeryNotSticky.slabKatzTao` supplies (clause (A3) of the
  rescaling plus the two absorbed constants), at the fullness threshold `η₁`, with loss
  `δ^{-4ϱ} ≥ δ^{-ϱ} · (δ^{-3ϱ})^{1-β}` (GWZ (104): `δ^{-O(ηbias)} δ^{-ηbias(1-β)}`). No
  threshold clause relates `ϱ` to `η₁`: `η₁(ϱ, β) ≤ ϱ/(1-β)` for every `K_KT`-derived
  threshold, so `3ϱ ≤ η₁` was unsatisfiable for `β < 2/3`. See
  `Kakeya.VeryNotSticky.KTRho2ScaleData` for why it is stated for `ShadedBody` with a
  thickness hypothesis rather than for `ShadedTube`. -/
  estimate : cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀) (4 * cfg.ϱ) η₁ (3 * cfg.ϱ)
  /-- blueprint `tangentialSlabDensityThreshold` -/
  densityConstant : ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤
    (cfg.δ : ENNReal) ^ (-cfg.η)

/-- Pin: the field list of `SlabMultKT` — `katzTao_threshold` is gone and nothing
else changed. -/
def statement_of_universal_slabMultKT (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (tc : ThinConfig cfg bd) (η₁ : ℝ) : Prop :=
  9 * cfg.η ≤ η₁ ∧
    cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀) (4 * cfg.ϱ) η₁ (3 * cfg.ϱ) ∧
    ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)

theorem statement_of_universal_slabMultKT_pinned (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} (kt : SlabMultKT cfg tc) :
    statement_of_universal_slabMultKT cfg bd tc kt.η₁ :=
  ⟨kt.fullness_threshold, kt.estimate, kt.densityConstant⟩

/-- **The slab package at a ball and a typical angle** (blueprint `lem:ml2tangential`(a)
together with the rescaling of item (b)).

This is everything the tangential leaf needs that depends on the ball `B` and on the typical
angle `ta.θ` with its constant `ta.Ctyp`: the slab family `𝕊` of blueprint
`hyp:ml2tangentialSlabFamily`, the admissible multiplicity constant `Cμ` with its fixed-scale
threshold `tangentialSlabMultThreshold`, and the anisotropic rescaling
`hyp:ml2anisotropicSlabRescale` with its constant `CΔ` and the threshold
`tangentialDeltamaxThreshold`.

The three groups travel together, and not as three bundles, because the rescaling clause
mentions the family: `rescale` is quantified over the pairs `(S, Wd)` that
`Kakeya.VeryNotSticky.tangentialSlabDecomp` can return *out of this `𝕊`*, i.e. over
`Kakeya.VeryNotSticky.IsDenseSlab cfg ta 𝕊 S Wd`. Quantifying it over all convex bodies
would demand an affine map turning every contained body into a `ρ₂`-tube, which is
unsatisfiable and would make the hypothesis — and hence the leaf — vacuous; dropping the
angle clause from the antecedent has the same effect, for the reason recorded in
`Kakeya.VeryNotSticky.IsDenseSlab`.

The package is indexed by the whole typical-angle bundle `ta` rather than by `θ` and `Ctyp`
separately, because `isSlabFamily` and `rescale` both need `ta.sel`, the index set the
refinement is recorded on; see `Kakeya.VeryNotSticky.IsDenseSlab`. -/
structure SlabPackage (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    {tc : ThinConfig cfg bd} {B : bd.bι} {hB : B ∈ bd.bs} {τ' : ℝ}
    (ta : TypicalAngleData cfg tc hB τ') where
  /-- the slab family of blueprint `hyp:ml2tangentialSlabFamily`, assumed and not constructed -/
  𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
  /-- the assignment of each body of `𝕎''_B` to the slab of `𝕊` it is counted in — GWZ's
  `𝕎''_B = ⊔_S 𝕎''_S` (l.2350) read as an assignment, since the filter sets of (28) need not be
  disjoint for a maximal essentially disjoint family -/
  slabOf : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- it is a slab family for `(B, θ)`, decomposing the refinement `𝕎''_B` indexed by
  `ta.sel` through `slabOf` (blueprint `hyp:ml2tangentialSlabFamily`(S3)) -/
  isSlabFamily : IsSlabFamily cfg B ta.sel ta.θ 𝕊 slabOf
  /-- the multiplicity constant of the decomposition -/
  Cμ : NNReal
  /-- it is admissible for the thickness constant `bd.C₀` and the typicality constant `Ctyp` -/
  CμAdmissible : IsSlabDecompMultConstant bd.C₀ ta.Ctyp Cμ
  /-- blueprint `tangentialSlabMultThreshold` -/
  Cμ_le : (Cμ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-τ')
  /-- the anisotropic change of variables attached to each slab -/
  L : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) →
    EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)
  /-- the `Δ_max` distortion constant of the transport -/
  CΔ : NNReal
  /-- it is admissible in the sense of blueprint `def:ml2tangentialSlabDeltamaxConstant`; this
  subsumes `1 ≤ CΔ` and supplies the cardinality constant `2^10 C₀³` that
  `Kakeya.VeryNotSticky.slabCard` absorbs into `CΔ_le` -/
  CΔAdmissible : IsSlabDeltamaxConstant (latticeRescaleConstant bd.C₀) CΔ
  /-- blueprint `tangentialDeltamaxThreshold` -/
  CΔ_le : (CΔ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2))
  /-- the rescaling works at every dense slab of `𝕊` -/
  rescale : ∀ (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω),
    IsDenseSlab cfg ta 𝕊 S Wd →
      IsAnisotropicSlabRescale cfg S Wd (L S) (latticeRescaleConstant bd.C₀) CΔ

/-- **The inputs of the tangential leaf** (blueprint `lem:ml2tangential`(a)–(c)).

One field per item of the blueprint statement. None of the three is implied by `cfg`, by
`params` or by `Kakeya.VeryNotSticky.CaseScale`, and none of the three lemmas of this file
discharges its own, so they are received here and threaded from
`Kakeya.VeryNotSticky.CaseSideData` down through `Kakeya.VeryNotSticky.exists_goalMult`,
`Kakeya.goalMult_of_a_le`, `Kakeya.VeryNotSticky.goalMult_of_b_le` and
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge`, exactly as `hβ1`, the thick-density
thresholds and `hslabScale` already are. That threading is what the blueprint means by "they
travel to the consumers of this leaf"; leaving it undone would leave the tangential branch of
`goalMult_of_multBodies_ge` open and its conclusion unearned.

`slab` is quantified over the ball and over the typical-angle package because the slab family
and the admissible constant depend on both, and neither is available at the point where the
bundle is arranged: the ball is chosen inside `goalMult_of_b_le` and the angle is produced
inside `goalMult_of_multBodies_ge`. -/
structure TangentialInputs (cfg : VeryNotSticky.{u}) {bd : BallData cfg}
    (tc : ThinConfig cfg bd) (τ' : ℝ) where
  /-- item (a), with the rescaling of item (b), at every ball and every typical angle -/
  slab : ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
    SlabPackage cfg ta
  /-- item (b), analytic half -/
  slabMult : SlabMultKT cfg tc
  /-- item (c); the bundle lives with
  `Kakeya.VeryNotSticky.nonslabSplitBoundPB` in `MainLemma2/SplitInputsLoose.lean`.

  **Retyped in lockstep with conjunct 6**:
  the hierarchy of `Kakeya.VeryNotSticky.PBSplitInputs` is `Tube.PartitionBrackets`, which the
  exact `Tube.UniformTubeSet` and the loose `Kakeya.LooseUniform.LooseUniformTubeSet` both
  instantiate, so the field is *weaker* than before and every producer of the old field still
  serves it through `Kakeya.VeryNotSticky.SplitInputs.toPB`. -/
  split : PBSplitInputs cfg bd

/-- **Reduction to a single dense slab** (blueprint `lem:ml2tangentialSlabDecomp`).

In the tangential case the typicality of `θ` bounds the angle between the *normals* of any two
bodies of `𝕎''_B` that share a shaded point by `⪅ θ ≤ δ^{-τ'} a/b`. Decomposing `𝕎''_B` over a
maximal essentially disjoint family `𝕊` of slabs `S ⊆ B` with affine thicknesses
`∼ (r₁, r₁, (a/b) r₁)` therefore spreads each fibre over at most `δ^{-O(τ')}` of the
subfamilies

`𝕎''_S = {W ∈ 𝕎''_B : W ⊆ S and ∠(n(W), n(S)) ≤ 2θ}`,

and discarding the slabs on which the density `λ(𝕎''_S, Y_{𝕎''_S})` is less than a hundredth
of `λ(𝕎''_B, Y_{𝕎''_B})` is a `⪆ 1` refinement. What survives is a *single* slab, the one
realising the maximum, which is why the conclusion is an existential over one `S` rather than
over a dense subfamily.

The family `𝕊` is *data*, not output: its existence is a maximality argument that the
blueprint does not carry out, so it is assumed here in the form
`Kakeya.VeryNotSticky.IsSlabFamily`, exactly as the blueprint statement assumes it, and the
selected slab is returned together with its membership `S ∈ 𝕊`. It travels, with the
admissible multiplicity constant and its threshold, in the single bundle
`sp : Kakeya.VeryNotSticky.SlabPackage cfg ta` — the same bundle
`Kakeya.VeryNotSticky.TangentialInputs.slab` produces — whose fields `sp.𝕊`,
`sp.isSlabFamily`, `sp.Cμ`, `sp.CμAdmissible` and `sp.Cμ_le` are what this statement reads.

The two data returned are the slab `S` and the index set `Wd` of `𝕎''_S ⊆ 𝕎''_B`; the shading
on it is the refined shading `ta.YW` produced together with `θ` by
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`, restricted to `Wd`. Their seven geometric
clauses — membership in `𝕊`, the two clauses of (S2), non-emptiness, containment in `ta.sel`
and the angle — together with the density clause are bundled as
`Kakeya.VeryNotSticky.IsDenseSlab`, which is what
`Kakeya.VeryNotSticky.tangentialSlabMult` consumes and what the rescaling hypothesis of
`Kakeya.VeryNotSticky.goalMult_of_theta_lt` is quantified over. The angle clause is stated
with `Kakeya.NonSlab.bodyNormal`, the normal of blueprint `def:ml2bodyNormal`, on both sides:
it is what makes the rescaling of `Kakeya.VeryNotSticky.tangentialSlabMult` turn the bodies of
`𝕎''_S` into `ρ₂`-tubes — the stretch acts in the thin direction of `S`, so what it needs is
that the thin direction of `W` be aligned with it — and without it that lemma is false. Read
on `bodyAxis`, as an earlier version had it, the clause constrained the *long* directions and
gave the rescaling nothing.

The plank presentation, the angle `θ`, its constant `Ctyp` and the refinement `(𝕎''_B, YW)`
travel in the bundle `ta : Kakeya.VeryNotSticky.TypicalAngleData cfg tc hB τ'`, the output of
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`; the hypothesis `a/b ≤ θ` of the blueprint
statement is `ta.hθab'`.

**The two clauses, and their constants.** Only the multiplicity clause is a separate conjunct
of the conclusion; the density clause is the field `IsDenseSlab.dense`, whose exponent and
constant are discussed there. The multiplicity clause renders the blueprint's
`δ^{-O(τ')}` by the explicit factor `δ^{-C_sep τ'/4}`, one quarter of the budget
`Kakeya.VeryNotSticky.parameterSeparationConstant`. Three powers of `δ` are charged to that
quarter: the `δ^{-2τ'}` of the fibre count, the `δ^{-2η}` that the passage from `𝕎'_B` to the
`c`-refinement `𝕎''_B` costs (blueprint `lem:ml2multRefine`; the earlier statement of this
clause did not name it), and the further `δ^{-τ'}` that pays for the constant `sp.Cμ` by the
threshold `sp.Cμ_le`, blueprint `tangentialSlabMultThreshold`. That
`3τ' + 2η ≤ C_sep τ'/4` is blueprint `lem:ml2tangentialSlabDecompExponent`, which needs
`7η < τ'` and hence `params.transverse` together with `hβ1 : β ≤ 1` — the only genuine
relation between the parameters used here, the rest being the generosity of
`C_sep/4 = 2^18`.

`Wd.Nonempty` is part of `IsDenseSlab` because the selected slab lies in `𝕊_dens`, whose
definition `tangentialSdens` requires `𝕎''_S ≠ ∅`; it is the hypothesis of blueprint
`lem:ml2tangentialSlabRescale`, so `tangentialSlabMult` cannot do without it.

The non-slab case hypothesis `b ≤ δ^{2·exscal}` is *not* a binder here. The blueprint proof —
the fibre count via typicality and axis separation, the density chain, and the exponent check
`lem:ml2tangentialSlabDecompExponent` — never reads it. Nor does
`Kakeya.VeryNotSticky.tangentialSlabMult`, whose Katz–Tao input is stated at the scale `ρ₂`
itself: the hypothesis is spent only in `Kakeya.VeryNotSticky.nonslabSplitBound`, in the form
`ρ₂ ≤ δ^{exscal}`, and it enters this file exactly once, as the binder `hnotslab` of
`Kakeya.VeryNotSticky.goalMult_of_theta_lt`. -/
theorem tangentialSlabDecomp (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (ta : TypicalAngleData cfg tc hB τ')
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    -- the slab family `𝕊` of blueprint `hyp:ml2tangentialSlabFamily` with its admissible
    -- multiplicity constant, assumed: `sp.𝕊`, `sp.isSlabFamily`, `sp.Cμ`, `sp.CμAdmissible`
    -- and `sp.Cμ_le`
    (sp : SlabPackage cfg ta) :
    ∃ (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω),
      IsDenseSlab cfg ta sp.𝕊 S Wd ∧
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
        (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * τ' / 4)) *
          ShadedBody.multiplicity Wd ta.YW := by
  classical
  obtain ⟨S, hSd, hmult⟩ := tangentialSlabDecompMultChain cfg hB ta sp.isSlabFamily htang
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδle1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hbudget : 3 * τ' + 2 * cfg.η ≤ parameterSeparationConstant * τ' / 4 :=
    (tangentialSlabDecompExponent params hβ1).2
  have hCμ : (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-τ') := by
    have h1 : (((100 / 99 : NNReal) * slabDecompFibreConstant bd.C₀ ta.Ctyp : NNReal) : ENNReal) ≤
        (sp.Cμ : ENNReal) := by exact_mod_cast sp.CμAdmissible.typ_le
    have hCeq : (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) =
        (((100 / 99 : NNReal) * slabDecompFibreConstant bd.C₀ ta.Ctyp : NNReal) : ENNReal) := by
      rw [ENNReal.coe_mul]
      rw [show (100 / 99 : ENNReal) = ((100 / 99 : NNReal) : ENNReal) by norm_num]
    exact le_trans (le_of_eq hCeq) (le_trans h1 sp.Cμ_le)
  refine ⟨S, slabBodies cfg ta.sel sp.slabOf S, ?_, ?_⟩
  · exact
      { mem := hSd.1
        subset := Finset.filter_subset _ _
        nonempty := hSd.2.1
        thicknesses := sp.isSlabFamily.S2_thicknesses S hSd.1
        ball_meets := sp.isSlabFamily.S2_ball_meets S hSd.1
        -- with (S3) an assignment the two geometric clauses of a
        -- dense slab are (S3′) read at `j`, transported along `sp.slabOf j = S`
        bodies_subset := fun j hj => by
          obtain ⟨hjsel, hjeq⟩ := (mem_slabBodies_iff cfg).mp hj
          rw [← hjeq]
          exact (sp.isSlabFamily.S3 j hjsel).2.1
        angle := fun j hj => by
          obtain ⟨hjsel, hjeq⟩ := (mem_slabBodies_iff cfg).mp hj
          rw [← hjeq]
          exact (sp.isSlabFamily.S3 j hjsel).2.2
        angle_ratio := fun j hj => by
          obtain ⟨hjsel, hjeq⟩ := (mem_slabBodies_iff cfg).mp hj
          rw [← hjeq]
          exact sp.isSlabFamily.S3_ratio j hjsel
        dense := tangentialDensityChain cfg hB ta hSd }
  · calc
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
          ≤ (100 / 99 : ENNReal) * (slabDecompFibreConstant bd.C₀ ta.Ctyp : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) *
              ShadedBody.multiplicity (slabBodies cfg ta.sel sp.slabOf S) ta.YW := hmult
      _ ≤ (cfg.δ : ENNReal) ^ (-τ') * (cfg.δ : ENNReal) ^ (-(2 * τ') - 2 * cfg.η) *
              ShadedBody.multiplicity (slabBodies cfg ta.sel sp.slabOf S) ta.YW := by
            gcongr
      _ = (cfg.δ : ENNReal) ^ (-(3 * τ' + 2 * cfg.η)) *
              ShadedBody.multiplicity (slabBodies cfg ta.sel sp.slabOf S) ta.YW := by
            rw [← ENNReal.rpow_add (-τ') (-(2 * τ') - 2 * cfg.η) hδ0 hδtop]
            congr 1
            congr 1
            ring
      _ ≤ (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * τ' / 4)) *
              ShadedBody.multiplicity (slabBodies cfg ta.sel sp.slabOf S) ta.YW := by
            exact mul_le_mul_left
              (ENNReal.rpow_le_rpow_of_exponent_ge hδle1 (by linarith)) _

/-! ### Multiplicity inside one dense slab (blueprint `lem:ml2tangentialSlabMult`)

The commentary below belongs to `Kakeya.VeryNotSticky.tangentialSlabMult`, stated at the end of
this section; it is a section note rather than that theorem's docstring because the four steps
of its proof are isolated as private lemmas in between.

Let `S` be the dense slab produced by `Kakeya.VeryNotSticky.tangentialSlabDecomp` and put
`ρ₂ = b / r₁`. The linear change of variables carrying `S` to the unit ball sends the two
axes of length `∼ r₁` to unit length and stretches the short axis, of length `∼ (a/b) r₁`, by
`∼ b/a`; a body `W ∈ 𝕎''_S` has affine thicknesses `∼ (r₁, b, a)` and, by the angle clause,
its *normal* is within `θ` of that of `S` — so its thin direction is the one the stretch acts
in — and it is carried to a `ρ₂`-tube. That is the content
of blueprint `hyp:ml2anisotropicSlabRescale`, an *assumption*: the blueprint has the
isotropic homothety toolkit but not the anisotropic comparison, so the rescaling is carried
in the bundle `sp : Kakeya.VeryNotSticky.SlabPackage cfg ta` — the same bundle
`Kakeya.VeryNotSticky.TangentialInputs.slab` produces and
`Kakeya.VeryNotSticky.tangentialSlabDecomp` consumes — as the map `sp.L S`, the constant
`sp.CΔ` with `sp.CΔAdmissible`, and `sp.rescale S Wd hslab : IsAnisotropicSlabRescale cfg S Wd
(sp.L S) sp.CΔ`. The family
`𝕎''_S` becomes a family `𝕋̃` of `ρ₂`-tubes in the unit ball with the same `λ` and the same
`μ` (blueprint `lem:ml2tangentialSlabRescale`, whose hypotheses are `hWdne` and the positivity
of the shaded union), and with

`Δ_max(𝕋̃) ≤ CΔ δ^{-2ϱ} ≤ δ^{-5ϱ/2}` and `|𝕋̃| ≤ δ^{-3ϱ} ρ₂^{-2}`,

blueprint `tangentialDeltamaxConclusion`. The first inequality is clause (A3) of `hL`,
blueprint `lem:ml2tangentialDeltamaxTransport`, which folds into `CΔ` the `⪅` constant of the
biased maximal density factoring bound `factmaxmod2` of `lemmafactmaxbias` (through
`Δ_max(𝕎''_S) ≤ Δ_max(𝕎_B)`, GWZ (83) at `U = B` — `Cbias δ^{-2ϱ}`, the (C4) field
`bodies_antiClustering` of `bd`), the distortion of the transport itself and the constant of
`lem:tubeCountFromDeltamax`; the second follows from it. Of the two half-powers, one pays for
`sp.CΔ` itself and the other for the absorbed `δ`-free constant — `volume_comparison.C 3` in
`Kakeya.VeryNotSticky.slabKatzTao`, `48 C₀³` in `Kakeya.VeryNotSticky.slabCard` — which
`sp.CΔAdmissible.card_le` (`2^10 C₀³ ≤ CΔ`) routes through the same threshold; both are
discharged by `sp.CΔ_le`, `CΔ ≤ δ^{-ϱ/2}`, blueprint `tangentialDeltamaxThreshold`, and it is (A3) that keeps `sp.CΔ` from being vacuous: the two
hypotheses pull in opposite directions.

GWZ Lemma 3.7 (blueprint `genKKT`) is then run with `ϱ` in place of `ε` through
`kt.estimate`, read at the `Δ_max` level `δ^{-3ϱ}` and at the loss `4ϱ ≥ ϱ + 3ϱ(1-β)` — GWZ
(104), `δ^{-O(ηbias)} δ^{-ηbias(1-β)} |𝕋̃|^β`, the factor `δ^{-ηbias(1-β)}` being `Δ_max^{1-β}`
— giving `μ(𝕎''_S, Y_{𝕎''_S}) = μ(𝕋̃, Y_{𝕋̃}) ≤ δ^{-4ϱ} |𝕋̃|^β ≤ δ^{-7ϱ} ρ₂^{-2β}`, using
`(δ^{-3ϱ})^β ≤ δ^{-3ϱ}` and hence `hβ1 : β ≤ 1`. Blueprint
`lem:ml2tangentialSlabMultAbsorb` with `k = 2`, `m = 7` turns the display into the conclusion:
one quarter `δ^{-C_sep ϱ/4}` of `Kakeya.VeryNotSticky.parameterSeparationConstant`, of whose
`2^18` available powers seven are spent.

The two constants of blueprint `tangentialSlabMultAbsorbThreshold` do not appear. Both `⪅`
of the blueprint display are constant-free in the Lean rendering: the Katz–Tao one is absorbed
into `kt.estimate`, which is the *cross-section* form of
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` and carries no implicit factor, and the
change-of-variables one is absorbed into
`tangentialSlabRescaleInvariance`, which asserts equality of `λ` and of `μ`. Carrying them as
free parameters `Cabs₁`, `Cabs₂` occurring only in their own thresholds would have been
vacuous.

**The fullness hypothesis, and where the corrected `8η` lands.** `hslab.dense` is the density
clause of `tangentialSlabDecomp`,
`δ^{8η} ≤ tangentialSlabDecompConstant tc.C · λ(𝕎''_S, Y_{𝕎''_S})`, with the factor `100` of
the slab selection and the doubled exponent forced as recorded there.
It is consumed at exactly one place, blueprint `lem:ml2tangentialSlabFull`: with
`kt.densityConstant`,
the threshold `tangentialSlabDensityThreshold` discharging the constant
`tangentialSlabDecompConstant tc.C` against a
ninth `δ^{η}`, it gives `λ(𝕋̃, Y_{𝕋̃}) ≥ δ^{9η} ≥ δ^{η₁}` and hence the fullness hypothesis of
`K_KT(β)`. So the correction is invisible in the conclusion, which is unchanged, and it does
not enter the accumulated budget of `Kakeya.VeryNotSticky.goalMult_of_theta_lt` either.

The fullness threshold `η₁` and the one inequality that bounds it travel in
`kt : Kakeya.VeryNotSticky.SlabMultKT cfg tc`, together with `kt.densityConstant`, blueprint
item (ii). `kt.fullness_threshold`, `9η ≤ η₁`, is not implied by
`Kakeya.VeryNotSticky.CaseParams`: the budgets of `params` relate `η` to `ϱ`, whereas `η₁` is
the opaque threshold that GWZ Lemma 3.7 (blueprint `genKKT`) attaches to the pair `(ϱ, β)`,
and `η ≪ ϱ` says nothing about `η` against `η₁`. It has content here because `η₁` is the
threshold at which `kt.estimate` demands its fullness hypothesis: `9η ≤ η₁` is what lets the
density chain `λ(𝕋̃, Y_{𝕋̃}) ≥ δ^{9η}` discharge the fullness side. The Katz–Tao side has no
threshold clause: `kt.estimate` is read at the `Δ_max` level `δ^{-3ϱ}` that
`Kakeya.VeryNotSticky.slabKatzTao` supplies, exactly as Lemma 3.7 takes `Δ_max` as a factor.
An earlier version carried a second clause `kt.katzTao_threshold : 3ϱ ≤ η₁` (before that,
`2ϱ ≤ η₁`) and read `kt.estimate` at the diagonal `Δ_max` level `δ^{-η₁}`; the pair was
jointly unsatisfiable for `β < 2/3`, because `η₁(ϱ, β) ≤ ϱ/(1-β)` for every threshold
`K_KT(β)` can provide.

`kt.estimate` is `Kakeya.VeryNotSticky.KTRho2ScaleData`, not
`Kakeya.VeryNotSticky.KTScaleData`: the latter speaks only about subfamilies `s' ⊆ cfg.s` of
the fixed family of `δ`-tubes at the fixed fullness threshold `δ^{cfg.η}`, and says nothing
about `μ(Wd, YW)`, whereas what is needed here is the estimate for the rescaled family of
`ρ₂`-tubes in `B₁` indexed by `Wd ⊆ bd.ω` at the threshold `δ^{η₁}` — the reading at the small
Katz–Tao parameter `τ = δ ≤ ρ₂` of Remark `multBoundsDeltaVsRho`. Together with the
threshold clause this is blueprint item (i).

The eight clauses about the pair `(S, Wd)` travel in
`hslab : Kakeya.VeryNotSticky.IsDenseSlab cfg ta sp.𝕊 S Wd`, the conclusion of
`Kakeya.VeryNotSticky.tangentialSlabDecomp` at the same `sp`; the family itself is used only
to instantiate `sp.rescale`, this lemma otherwise reading `hslab.mem`'s companions alone.

**Why the shading is `ta.YW` and not a free family.** An earlier version took a free
`YW : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3))` together with `θ`, `hθab`, `hθ1`, and in
that form the statement was *refutable*: nothing linked `YW j` to the factoring body
`bd.Wb j`, so taking every `YW j` to be one and the same fully shaded body made
`λ(Wd, YW) = 1` — hence the density hypothesis vacuously true — while `μ(Wd, YW) = |Wd|`,
which the Katz–Tao input bounds only by `≈ δ^{-3ϱ} ρ₂^{-2}`, above the conclusion's
`δ^{-C_sep ϱ/4} ρ₂^{-2β}` for `ρ₂` near `δ^{1-exscal}`. Taking the refinement bundle `ta` and
reading the shading off it as `ta.YW` repairs this: `hslab.subset : Wd ⊆ ta.sel` together with
`ta.hrefine` gives `(ta.YW j).toConvexSpaceBody = ((tc.thinBall hB).W j).toConvexSpaceBody` for
every `j ∈ Wd`, and the enlargement sandwich `Kakeya.ThinCase.ThinBall.Wb_le_W` /
`Kakeya.ThinCase.ThinBall.W_le_cthickening` places that body between the geometric body
`bd.Wb j` and its closed `τ₂(bd.Wb j)`-neighbourhood. The equality
`(ta.YW j).toConvexSpaceBody = bd.Wb j` of the earlier statement is *false* for the corrected
factoring proposition, whose outer bodies are genuine enlargements; what replaces it is the
sandwich, and the sandwich is exactly what makes the geometric clauses of `hslab` — stated
about `bd.Wb` — still bear on the shaded family the conclusion is about. Each such passage
costs at most one factor of `2` in a comparison constant or one factor
`Metric.volume_comparison.C 3` in a density, and both are charged where they are used: the
first to the comparison constant `2 bd.C₀` of `Kakeya.VeryNotSticky.KTRho2ScaleData`, the
second to the `Δ_max` level `δ^{-3ϱ}` of `Kakeya.VeryNotSticky.slabKatzTao` through
`sp.CΔAdmissible.card_le` and `sp.CΔ_le`. The
localisation, the tube profile and the `Δ_max` bound for the enlarged carriers come
respectively from clause (A1'), clause (A2') and
`Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement`.
It also removes `YW`, `θ`, `hθab` and `hθ1` as separate binders: the angle bounds
`a/b ≤ θ ≤ 1` are `ta.hθab'` and `ta.hθ1`, and they are still used for the same two purposes
as before, the lower bound in the fibre geometry and the upper bound in making the tilt of a
body against the *normal* of `S` at most one, which the rescaling needs. This lemma does *not*
read `ta.htyp` — typicality is spent in `tangentialSlabDecomp`, in the fibre count.

The blueprint's third expression `ρ₂^{βζ} |𝕋_{ρ₂}|^β` is *not* used: it is obtained from
`ρ₂^{-2β}` by `|𝕋_{ρ₂}| ≥ ρ₂^{-2-ζ}`, and the assembly cancels it again against the
`ρ₂^{(2+ζ)β}` of `Kakeya.VeryNotSticky.nonslabSplitBound`, so the middle form is the one that
keeps the combination free of the family `𝕋_{ρ₂}`. -/
section SlabMultSteps

variable {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {tc : ThinConfig cfg bd} {B : bd.bι}
  {hB : B ∈ bd.bs} {τ' : ℝ} {ta : TypicalAngleData cfg tc hB τ'}
  {𝕊 : Set (ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))}
  {S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {Wd : Finset bd.ω}

/-- **The volume of a body with a `ρ`-tube thickness profile** (the inscribed-simplex input of
`Kakeya.VeryNotSticky.slabCard`).

A convex bounded body whose affine thicknesses are comparable, with constant `C₀`, to the
`ρ`-tube profile `(1, ρ, ρ)` has volume at least `ρ² / (6 C₀³)`. The `6` is `3!`, the reciprocal
of the inscribed-simplex constant `Metric.lt_volume_convexHull.c 3` of
`Convex.prod_thickness_le_volumeReal`, and the `C₀³` is one factor of `C₀` per axis: by
definition `HasThicknesses K C₀ t` unfolds to
`∀ k, (C₀ : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ K k ∧ Metric.thickness ℝ K k ≤ C₀ * t k`,
so the product over the three axes is at least `C₀⁻³ * 1 * ρ * ρ`.

It is isolated because it is the one genuinely geometric step of the cardinality count, the rest
of `Kakeya.VeryNotSticky.slabCard` being the Katz–Tao counting lemma and bookkeeping.

It is the single statement of this fact in the development, and it is public so that the
`KTRho2` interface can cite it: its `ENNReal` form
`Kakeya.VeryNotSticky.ofReal_le_volume_of_tubeProfile` (`MainLemma2/KTRho2Interface.lean`) is a
one-line application of it. -/
lemma volume_ge_of_tubeProfile {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hconv : Convex ℝ K) (hbdd : Bornology.IsBounded K) {C₀ ρ : NNReal} (hC₀ : 1 ≤ C₀)
    (hprof : HasThicknesses K C₀ ![(1 : ℝ), (ρ : ℝ), (ρ : ℝ)]) :
    ((ρ : ℝ) ^ 2) / (6 * (C₀ : ℝ) ^ 3) ≤ MeasureTheory.volume.real K := by
  -- `6 = 3!` is the reciprocal of the inscribed-simplex constant
  -- `Metric.lt_volume_convexHull.c 3`, so the goal is a direct instance of
  -- `Convex.prod_thickness_le_volumeReal` once the three thicknesses are bounded below.
  have hC0ne : (C₀ : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀))
  have h0 : (C₀ : ℝ)⁻¹ * 1 ≤ Metric.thickness ℝ K 0 := by
    simpa using (hprof 0).1
  have h1 : (C₀ : ℝ)⁻¹ * (ρ : ℝ) ≤ Metric.thickness ℝ K 1 := by
    simpa using (hprof 1).1
  have h2 : (C₀ : ℝ)⁻¹ * (ρ : ℝ) ≤ Metric.thickness ℝ K 2 := by
    simpa using (hprof 2).1
  have ha1 : 0 ≤ (C₀ : ℝ)⁻¹ * 1 := by positivity
  have ha2 : 0 ≤ (C₀ : ℝ)⁻¹ * (ρ : ℝ) := by positivity
  have ht0 : 0 ≤ Metric.thickness ℝ K 0 := Metric.thickness_nonneg K 0
  have ht1 : 0 ≤ Metric.thickness ℝ K 1 := Metric.thickness_nonneg K 1
  have ht2 : 0 ≤ Metric.thickness ℝ K 2 := Metric.thickness_nonneg K 2
  have h01 : ((C₀ : ℝ)⁻¹ * 1) * ((C₀ : ℝ)⁻¹ * (ρ : ℝ)) ≤
      Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 := by
    exact mul_le_mul h0 h1 ha2 ht0
  have hprod_lower :
      (((C₀ : ℝ)⁻¹ * 1) * ((C₀ : ℝ)⁻¹ * (ρ : ℝ))) * ((C₀ : ℝ)⁻¹ * (ρ : ℝ))
        ≤ Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 * Metric.thickness ℝ K 2 := by
    exact mul_le_mul h01 h2 ha2 (mul_nonneg ht0 ht1)
  have hvol : (6 : ℝ)⁻¹ *
      (Metric.thickness ℝ K 0 * Metric.thickness ℝ K 1 * Metric.thickness ℝ K 2) ≤
      MeasureTheory.volume.real K := by
    have hv0 := Convex.prod_thickness_le_volumeReal (E := EuclideanSpace ℝ (Fin 3)) hconv hbdd
    rw [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] at hv0
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ] at hv0
    norm_num [Metric.lt_volume_convexHull.c] at hv0
    simpa using hv0
  have hLHS : (ρ : ℝ) ^ 2 / (6 * (C₀ : ℝ) ^ 3) =
      (6 : ℝ)⁻¹ * (((C₀ : ℝ)⁻¹ * 1) * ((C₀ : ℝ)⁻¹ * (ρ : ℝ))) * ((C₀ : ℝ)⁻¹ * (ρ : ℝ)) := by
    field_simp [hC0ne]
  rw [hLHS]
  nlinarith [hprod_lower, hvol, ha1, ha2, ht0, ht1, ht2, show 0 ≤ (6 : ℝ)⁻¹ by positivity]

/-- **Step 1 of `Kakeya.VeryNotSticky.tangentialSlabMult`: the dense slab is `δ^{η₁}`-full**
(blueprint `lem:ml2tangentialSlabFull`).

The density clause `hslab.dense` of the selected slab reads
`δ^{8η} ≤ tangentialSlabDecompConstant tc.C * λ(𝕎''_S, Y_{𝕎''_S})`, and `kt.densityConstant`
discharges that constant against a ninth power `δ^{η}`, giving `λ ≥ δ^{9η}`. Since `0 < δ ≤ 1`
the map `s ↦ δ^s` is antitone, so `kt.fullness_threshold : 9η ≤ η₁` turns that into
`λ ≥ δ^{η₁}`, which is the fullness hypothesis of `Kakeya.VeryNotSticky.KTRho2ScaleData`.

This is stated for the original shading `ta.YW`; the assembly transports it to the rescaled
family by `ShadedBody.fullness_affineImage`, which is an equality. -/
lemma slabFullness (hslab : IsDenseSlab cfg ta 𝕊 S Wd) (kt : SlabMultKT cfg tc) :
    cfg.δ ^ kt.η₁ ≤ ShadedBody.fullness Wd ta.YW := by
  have hδE_pos : 0 < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδE_ne0 : (cfg.δ : ENNReal) ≠ 0 := hδE_pos.ne'
  have hδE_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE_le_one : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hη1_nonneg : 0 ≤ kt.η₁ := by
    have h5 : (0 : ℝ) ≤ 9 * cfg.η := mul_nonneg (by norm_num) cfg.hη.le
    exact le_trans h5 kt.fullness_threshold
  have h1 : (cfg.δ : ENNReal) ^ (8 * cfg.η) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) * (ShadedBody.fullness Wd ta.YW : ENNReal) := by
    exact hslab.dense.trans
      (mul_le_mul_left kt.densityConstant (ShadedBody.fullness Wd ta.YW : ENNReal))
  have hmain : (cfg.δ : ENNReal) ^ (9 * cfg.η) ≤ (ShadedBody.fullness Wd ta.YW : ENNReal) := by
    calc
      (cfg.δ : ENNReal) ^ (9 * cfg.η)
          = (cfg.δ : ENNReal) ^ (cfg.η + 8 * cfg.η) := by ring_nf
      _ = (cfg.δ : ENNReal) ^ cfg.η * (cfg.δ : ENNReal) ^ (8 * cfg.η) := by
          rw [ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
      _ ≤ (cfg.δ : ENNReal) ^ cfg.η *
            ((cfg.δ : ENNReal) ^ (-cfg.η) * (ShadedBody.fullness Wd ta.YW : ENNReal)) := by
            exact mul_le_mul' le_rfl h1
      _ = (cfg.δ : ENNReal) ^ (cfg.η + -cfg.η) * (ShadedBody.fullness Wd ta.YW : ENNReal) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
      _ = ShadedBody.fullness Wd ta.YW := by
            have hsum : cfg.η + -cfg.η = 0 := by ring
            rw [hsum, ENNReal.rpow_zero, one_mul]
  have hanti : (cfg.δ : ENNReal) ^ kt.η₁ ≤ (cfg.δ : ENNReal) ^ (9 * cfg.η) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one kt.fullness_threshold
  rw [← ENNReal.coe_le_coe]
  rw [ENNReal.coe_rpow_of_nonneg _ hη1_nonneg]
  exact hanti.trans hmain

/-- **Step 2 of `Kakeya.VeryNotSticky.tangentialSlabMult`: the rescaled family is Katz–Tao at
`δ^{-3ϱ}`** (blueprint `lem:ml2tangentialSlabDeltamax`, first half).

Clause (A3) of `Kakeya.VeryNotSticky.IsAnisotropicSlabRescale` gives
`Δ_max(L(𝕎''_S)) ≤ CΔ δ^{-2ϱ}` for any realisation of the image family of the *geometric*
bodies `bd.Wb` as convex bodies. What the Katz–Tao estimate is applied to is the image family
of the *shaded* carriers `((tc.thinBall hB).W j).carrier`, which are enlargements of those
bodies, so a third step is needed.

Three inequalities chain. `Kakeya.ThinCase.ThinBall.isVolumeControlledEnlargement` makes the
outer carriers a `volume_comparison.C 3`-volume-controlled enlargement of `bd.Wb` in the sense
of `ConvexSpaceBody.IsVolumeControlledEnlargement`; an affine equivalence multiplies every
volume by the same factor `|det L|` and preserves inclusions, so the property survives the
transport with the *same* constant; and
`ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao` then transfers the bound, giving
`Δ_max ≤ volume_comparison.C 3 · CΔ δ^{-2ϱ}` for the enlarged image family. The two constants
are absorbed half a power of `δ^{-ϱ}` each: `volume_comparison.C 3 = 384 ≤ 2^10 C₀³ ≤ CΔ` by
`sp.CΔAdmissible.card_le`, and `CΔ ≤ δ^{-ϱ/2}` by `sp.CΔ_le`, twice (using the half exponents in (A3) and `CΔ_le`). That leaves `δ^{-3ϱ}`,
which is the conclusion: it is the `Δ_max` level at which
`Kakeya.VeryNotSticky.SlabMultKT.estimate` is read (weakening it further to `δ^{-η₁}` through a threshold clause `3ϱ ≤ η₁`, unsatisfiable for
`β < 2/3` since `η₁(ϱ, β) ≤ ϱ/(1-β)` for every threshold `K_KT(β)` can provide). Monotonicity
of `ConvexSpaceBody.IsKatzTao` in its constant does the rest.

The half-power spent on `volume_comparison.C 3` is the whole cost of the correction to
Proposition 5.1 at this step: with `(tc.thinBall hB).W j = bd.Wb j` the middle inequality is
the identity and `δ^{-5ϱ/2}` would do.

The realisation `V` is quantified rather than named, exactly as in (A3), because the image of an
affine equivalence does not carry the convexity, compactness and interior data of
`ConvexSpaceBody` for free; the hypothesis `hV` pins down the carriers, which is all that
`Δ_max` sees. -/
lemma slabKatzTao {sp : SlabPackage cfg ta}
    (hslab : IsDenseSlab cfg ta sp.𝕊 S Wd)
    (V : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hV : ∀ j ∈ Wd, (V j).carrier = (sp.L S) '' ((tc.thinBall hB).W j).carrier) :
    ConvexSpaceBody.IsKatzTao Wd V ((cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ))) := by
  classical
  have hδE_ne0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hδE_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE_le_one : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  -- Step 1: clause (A3) of the anisotropic rescaling at the affine-image family of the
  -- geometric bodies `bd.Wb`.
  set L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) := sp.L S
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  let Vg : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j => (bd.Wb j).affineImage L.toAffineMap hcont
  have hVg : ∀ j ∈ Wd, (Vg j).carrier = L '' (bd.Wb j).carrier := fun j _ => rfl
  have hKTg : ConvexSpaceBody.IsKatzTao Wd Vg
      ((sp.CΔ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) :=
    (sp.rescale S Wd hslab).A3 Vg hVg
  -- Step 2: `V` is a `volume_comparison.C 3`-volume-controlled enlargement of `Vg`.
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let C3 : ENNReal := (Metric.volume_comparison.C 3 : ENNReal)
  have hvce : ConvexSpaceBody.IsVolumeControlledEnlargement (tc.thinBall hB).bodies' bd.Wb
      (fun j => ((tc.thinBall hB).W j).toConvexSpaceBody) C3 := by
    simpa [C3, hfin] using ThinCase.ThinBall.isVolumeControlledEnlargement (tc.thinBall hB)
  have henl : ConvexSpaceBody.IsVolumeControlledEnlargement Wd Vg V C3 := by
    intro j hj
    have hj' : j ∈ (tc.thinBall hB).bodies' := ta.hsel (hslab.subset hj)
    have hinc : Vg j ≤ V j := by
      change (Vg j).carrier ⊆ (V j).carrier
      rw [hV j hj]
      change L '' (bd.Wb j).carrier ⊆ L '' ((tc.thinBall hB).W j).carrier
      exact Set.image_mono (SetLike.coe_subset_coe.mpr ((tc.thinBall hB).Wb_le_W j hj'))
    have hvolw : volume ((tc.thinBall hB).W j).carrier ≤ C3 * volume (bd.Wb j).carrier := by
      simpa [C3, hfin] using (hvce j hj').2
    let d : ENNReal := ENNReal.ofReal
      |LinearMap.det ((sp.L S).linear : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))|
    have hvw : volume ((sp.L S) '' ((tc.thinBall hB).W j).carrier) =
        d * volume ((tc.thinBall hB).W j).carrier := by
      simpa [d, AffineEquiv.coe_toAffineMap] using
        (Kakeya.volume_affineImage (sp.L S) ((tc.thinBall hB).W j).carrier)
    have hvg : volume (Vg j).carrier = d * volume (bd.Wb j).carrier := by
      dsimp [Vg, d]
      rw [ConvexSpaceBody.volume_affineImage (bd.Wb j) (sp.L S) hcont]
    have hvol : volume (V j).carrier ≤ C3 * volume (Vg j).carrier := by
      rw [hV j hj, hvg]
      rw [hvw]
      calc
        d * volume ((tc.thinBall hB).W j).carrier
            ≤ d * (C3 * volume (bd.Wb j).carrier) := by gcongr
        _ = C3 * (d * volume (bd.Wb j).carrier) := by ring
    exact ⟨hinc, hvol⟩
  -- Step 3: absorb the constants, half a power of `δ^{-ϱ}` each:
  -- `C3 · CΔ · δ^{-2ϱ} ≤ δ^{-ϱ/2} · δ^{-ϱ/2} · δ^{-2ϱ} = δ^{-3ϱ}`.
  have hC3_le : (Metric.volume_comparison.C 3 : NNReal) ≤ (2 : NNReal) ^ 10 * bd.C₀ ^ 3 := by
    have hC3 : (Metric.volume_comparison.C 3 : ℝ) ≤ (384 : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    have h2 : (384 : NNReal) ≤ (2 : NNReal) ^ 10 := by norm_num
    have hC0 : (1 : NNReal) ≤ bd.C₀ ^ 3 := one_le_pow₀ bd.hC₀
    have hbig : (384 : NNReal) ≤ (2 : NNReal) ^ 10 * bd.C₀ ^ 3 := by
      calc
        (384 : NNReal) ≤ (2 : NNReal) ^ 10 * 1 := by simpa using h2
        _ ≤ (2 : NNReal) ^ 10 * bd.C₀ ^ 3 :=
              mul_le_mul_of_nonneg_left hC0 (by positivity)
    have hC3n : (Metric.volume_comparison.C 3 : NNReal) ≤ (384 : NNReal) := by
      exact_mod_cast hC3
    exact hC3n.trans hbig
  have hC3pow : C3 ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
    have h1 : ((Metric.volume_comparison.C 3 : NNReal) : ENNReal) ≤
        (((2 : NNReal) ^ 10 * bd.C₀ ^ 3 : NNReal) : ENNReal) := by
      exact ENNReal.coe_le_coe.mpr hC3_le
    -- R6: `CΔAdmissible.card_le` is now stated at `latticeRescaleConstant bd.C₀`, which
    -- dominates `bd.C₀` (`le_alignedRescaleConstant`); only a `δ`-free numeral grows.
    have hCal : bd.C₀ ≤ latticeRescaleConstant bd.C₀ :=
      le_latticeRescaleConstant bd.hC₀
    have h2 : ((2 ^ 10 * bd.C₀ ^ 3 : NNReal) : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) := by
      refine le_trans (ENNReal.coe_le_coe.mpr ?_)
        ((ENNReal.coe_le_coe.mpr sp.CΔAdmissible.card_le).trans sp.CΔ_le)
      gcongr
    simpa [C3] using h1.trans h2
  have hprod : C3 * (sp.CΔ : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) :=
    mul_le_mul' hC3pow sp.CΔ_le
  have h3 : (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) *
        (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) = (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) := by
    rw [← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
    rw [← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
    congr 1
    ring
  exact ConvexSpaceBody.IsKatzTao.mono
    (ConvexSpaceBody.IsVolumeControlledEnlargement.isKatzTao henl hKTg) (by
      calc
        C3 * ((sp.CΔ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)))
            = (C3 * (sp.CΔ : ENNReal)) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by
              rw [mul_assoc]
        _ ≤ ((cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2))) *
              (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by gcongr
        _ = (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) *
              (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) := by ring
        _ = (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) := h3)

/-- **Step 3 of `Kakeya.VeryNotSticky.tangentialSlabMult`: the rescaled family is small**
(blueprint `tangentialDeltamaxConclusion`, `|𝕋̃| ≤ δ^{-3ϱ} ρ₂^{-2}`).

Count the rescaled bodies inside the unit ball with
`ConvexSpaceBody.IsKatzTao.card_le_div_real`, using the Katz–Tao bound
`CΔ δ^{-2ϱ} ≤ δ^{-5ϱ/2}` of clause (A3) with the threshold `sp.CΔ_le` and
the volume lower bound supplied by `Convex.prod_thickness_le_volumeReal`: each image body is,
by clause (A2), of thicknesses comparable to `(1, ρ₂, ρ₂)` with constant `bd.C₀`, so its volume
is at least `ρ₂² / (6 bd.C₀³)`, the `6` being `3!`, the reciprocal of the inscribed-simplex
constant in dimension three. The containment in the unit ball is clause (A1) together with
`hslab.bodies_subset`.

That produces `|𝕎''_S| ≤ 6 bd.C₀³ |B₁| δ^{-5ϱ/2} ρ₂^{-2}`, and the absolute factor
`6 bd.C₀³ |B₁| ≤ 2^10 bd.C₀³` is absorbed into the remaining half-power `δ^{-ϱ/2}`, leaving
the displayed form. That absorption is a *threshold* and not an exponent charge: by the
constant/exponent distinction at the head of this file a factor `δ^{-s}` with `s > 0` is `≥ 1`
but does not dominate a given constant, since `δ` is allowed up to `1`, so the quarter budget
`δ^{-C_sep ϱ/4}` cannot pay for it and half a power `δ^{-ϱ/2}` is spent here instead — the
spare power the blueprint's `δ^{-3ϱ}` carries over the `δ^{-2ϱ}` that `Δ_max` alone supplies,
split into two half-power factors: one for `CΔ`, one here.

It is not assumed. The two clauses of the package do it: `sp.CΔAdmissible.card_le`, item (c)
of blueprint `def:ml2tangentialSlabDeltamaxConstant`, gives `2^10 bd.C₀³ ≤ CΔ`, and
`sp.CΔ_le`, blueprint `tangentialDeltamaxThreshold`, gives `CΔ ≤ δ^{-ϱ/2}`. -/
lemma slabCard {sp : SlabPackage cfg ta}
    (hslab : IsDenseSlab cfg ta sp.𝕊 S Wd) :
    (Wd.card : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ)) := by
  -- R6: the volume floor is read at the comparison constant of clause (A2), which is now
  -- `latticeRescaleConstant bd.C₀`; the numeral `48 Cal³` is absorbed by
  -- `SlabPackage.CΔAdmissible.card_le` (stated at the same constant) and `CΔ_le`.  **The
  -- conclusion's exponent `3ϱ` does not move**: only a `δ`-free numeral grows.
  -- positivity of δ and ρ₂
  set Cal : NNReal := latticeRescaleConstant bd.C₀ with hCal_def
  have hCalOne : (1 : NNReal) ≤ Cal :=
    one_le_latticeRescaleConstant bd.hC₀
  have hδ : (cfg.δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδ_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb_pos : (0 : NNReal) < cfg.b := by
    have ha_pos : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact lt_of_lt_of_le ha_pos cfg.hdims.2.1
  have hr1_pos : (0 : NNReal) < cfg.r₁ := by
    unfold r₁
    exact NNReal.rpow_pos cfg.hδ
  have hρ_pos : (0 : NNReal) < cfg.rho2 := by
    unfold rho2
    exact div_pos hb_pos hr1_pos
  have hρ : (cfg.rho2 : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hρ_pos).ne'
  have hρ_top : (cfg.rho2 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hρR : (0 : ℝ) < (cfg.rho2 : ℝ) := by exact_mod_cast hρ_pos
  have hC0R : (0 : ℝ) < (Cal : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hCalOne)
  have hdenpos : (0 : ℝ) < (cfg.rho2 : ℝ) ^ 2 / (6 * (Cal : ℝ) ^ 3) :=
    div_pos (pow_pos hρR 2) (mul_pos (by norm_num : (0 : ℝ) < (6 : ℝ)) (pow_pos hC0R 3))
  -- the rescaled family
  let V : bd.ω → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j => (bd.Wb j).affineImage
      ((sp.L S) : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
      (AffineMap.continuous_of_finiteDimensional _)
  have hV : ∀ j ∈ Wd, (V j).carrier = (sp.L S) '' (bd.Wb j).carrier := by
    intro j _; rfl
  have hres : IsAnisotropicSlabRescale cfg S Wd (sp.L S) (latticeRescaleConstant bd.C₀) sp.CΔ :=
    sp.rescale S Wd hslab
  have hKT_base : ConvexSpaceBody.IsKatzTao Wd V
      (sp.CΔ * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) :=
    hres.A3 V hV
  -- `CΔ δ^{-2ϱ} ≤ δ^{-ϱ/2} δ^{-2ϱ} = δ^{-5ϱ/2}` by the threshold `sp.CΔ_le`
  have hKT : ConvexSpaceBody.IsKatzTao Wd V ((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) := by
    have hmul : (sp.CΔ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ≤
        (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) :=
      mul_le_mul' sp.CΔ_le (le_refl ((cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))))
    have hadd : (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) =
        (cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2)) := by
      rw [← ENNReal.rpow_add _ _ hδ hδ_top]
      congr 1
      ring
    apply ConvexSpaceBody.IsKatzTao.mono hKT_base
    exact hmul.trans_eq hadd
  let K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := ConvexSpaceBody.closedBall 0 1 (by norm_num)
  let v : ENNReal := ENNReal.ofReal ((1 : ℝ) * (cfg.rho2 : ℝ) * (cfg.rho2 : ℝ) /
    (6 * (Cal : ℝ) ^ 3))
  have h_sub : ∀ j ∈ Wd, V j ≤ K := by
    intro j hj
    change (V j).carrier ⊆ (K : Set (EuclideanSpace ℝ (Fin 3)))
    rw [hV j hj]
    exact hres.A1 j hj
  have h_vol_lb : ∀ j ∈ Wd, v ≤ volume (V j).carrier := by
    intro j hj
    have hthick : Kakeya.HasThicknesses (V j).carrier Cal
        ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)] := by
      rw [hV j hj]
      exact hres.A2 j hj
    have hlbreal : (cfg.rho2 : ℝ) ^ 2 / (6 * (Cal : ℝ) ^ 3) ≤
        MeasureTheory.volume.real (V j).carrier := by
      exact volume_ge_of_tubeProfile (K := (V j).carrier)
        (ConvexSpaceBody.convex (V j)) (ConvexSpaceBody.isBounded (V j)) hCalOne hthick
    have hfin : volume (V j).carrier ≠ ⊤ :=
      (ConvexSpaceBody.isCompact (V j)).measure_lt_top.ne
    change ENNReal.ofReal ((1 : ℝ) * (cfg.rho2 : ℝ) * (cfg.rho2 : ℝ) /
      (6 * (Cal : ℝ) ^ 3)) ≤ volume (V j).carrier
    rw [ENNReal.ofReal_le_iff_le_toReal hfin]
    rw [show (1 : ℝ) * (cfg.rho2 : ℝ) * (cfg.rho2 : ℝ) = (cfg.rho2 : ℝ) ^ 2 by ring]
    simpa [MeasureTheory.Measure.real] using hlbreal
  have h_card_mul : (Wd.card : ENNReal) * v ≤
      ((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) * volume K.carrier :=
    ConvexSpaceBody.IsKatzTao.card_mul_le hKT h_sub h_vol_lb
  have hvt : v ≠ ⊤ := by
    dsimp [v]
    exact ENNReal.ofReal_ne_top
  have hv0 : v ≠ 0 := by
    dsimp [v]
    exact ENNReal.ofReal_ne_zero_iff.mpr hdenpos
  have h_card : (Wd.card : ENNReal) ≤
      (((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) * volume K.carrier) / v :=
    (ENNReal.le_div_iff_mul_le (Or.inl hv0) (Or.inl hvt)).mpr h_card_mul
  have hvol8 : volume K.carrier ≤ (8 : ENNReal) := by
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hc := volume_closedBall_le_two_pow_finrank (E := EuclideanSpace ℝ (Fin 3))
    rw [hfin] at hc
    have hconf : volume K.carrier = volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ)) := by
      simp [K, ConvexSpaceBody.closedBall]
    rw [hconf]
    simpa [show (2 : ENNReal) ^ (3 : ℕ) = (8 : ENNReal) by norm_num] using hc
  -- the reciprocal of v and the absolute constant
  have varg_pos : (0 : ℝ) < (1 : ℝ) * (cfg.rho2 : ℝ) * (cfg.rho2 : ℝ) /
      (6 * (Cal : ℝ) ^ 3) := by
    rw [show (1 : ℝ) * (cfg.rho2 : ℝ) * (cfg.rho2 : ℝ) = (cfg.rho2 : ℝ) ^ 2 by ring]
    exact hdenpos
  have hv_inv : v⁻¹ = ENNReal.ofReal ((6 * (Cal : ℝ) ^ 3) / ((cfg.rho2 : ℝ) ^ 2)) := by
    dsimp [v]
    rw [← ENNReal.ofReal_inv_of_pos varg_pos]
    congr 1
    field_simp [hC0R.ne', hρR.ne']
  have h8inv : (8 : ENNReal) * v⁻¹ =
      (((48 * Cal ^ 3 : NNReal) : ENNReal) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) := by
    rw [hv_inv]
    -- `8 · (6 C₀³/ρ₂²) = 48 C₀³ · ρ₂^{-2}` in ENNReal, via `ofReal`.
    have hρpow : (cfg.rho2 : ENNReal) ^ (-(2 : ℝ)) =
        ENNReal.ofReal (1 / ((cfg.rho2 : ℝ) ^ 2)) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rw [ENNReal.ofReal_rpow_of_pos hρR]
      congr 1
      rw [Real.rpow_neg hρR.le (2 : ℝ)]
      simp
    have hcoef : ((48 * Cal ^ 3 : NNReal) : ENNReal) =
        ENNReal.ofReal (48 * (Cal : ℝ) ^ 3) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    calc
      (8 : ENNReal) * ENNReal.ofReal ((6 * (Cal : ℝ) ^ 3) / ((cfg.rho2 : ℝ) ^ 2))
          = ENNReal.ofReal ((48 * (Cal : ℝ) ^ 3) / ((cfg.rho2 : ℝ) ^ 2)) := by
              rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num]
              rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (8 : ℝ))]
              congr 1
              field_simp [hρR.ne']
              ring
      _ = (((48 * Cal ^ 3 : NNReal) : ENNReal) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) := by
              rw [hcoef, hρpow]
              rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 48 * (Cal : ℝ) ^ 3)]
              congr 1
              field_simp [hρR.ne']
  have hCconst : (((48 * Cal ^ 3 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2))) := by
    have h48 : ((48 * Cal ^ 3 : NNReal) : ENNReal) ≤
        ((2 ^ 10 * Cal ^ 3 : NNReal) : ENNReal) := by
      exact_mod_cast (mul_le_mul_of_nonneg_right (by norm_num : (48 : NNReal) ≤ (2 ^ 10 : NNReal))
        (by positivity : (0 : NNReal) ≤ Cal ^ 3))
    -- `2^10 C₀³ ≤ CΔ ≤ δ^{-ϱ/2}`: admissibility of `CΔ` and the fixed-scale threshold (F11)
    have hCΔ : ((2 ^ 10 * Cal ^ 3 : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) :=
      (ENNReal.coe_le_coe.mpr sp.CΔAdmissible.card_le).trans sp.CΔ_le
    exact h48.trans hCΔ
  calc
    (Wd.card : ENNReal) ≤ (((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) * volume K.carrier) / v :=
      h_card
    _ = (((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) * volume K.carrier) * v⁻¹ := by rfl
    _ ≤ (((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) * (8 : ENNReal)) * v⁻¹ := by
          gcongr
    _ = ((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) * (8 * v⁻¹) := by ac_rfl
    _ = ((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) *
          (((48 * Cal ^ 3 : NNReal) : ENNReal) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) := by
          rw [h8inv]
    _ ≤ ((cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2))) *
          (((cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2))) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) := by
          gcongr
    _ = (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ)) := by
          have hpow : (cfg.δ : ENNReal) ^ (-(5 * cfg.ϱ / 2)) * (cfg.δ : ENNReal) ^ (-(cfg.ϱ / 2)) =
              (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) := by
            rw [← ENNReal.rpow_add _ _ hδ hδ_top]
            congr 1
            ring
          rw [← mul_assoc, hpow]

/-- **Step 4 of `Kakeya.VeryNotSticky.tangentialSlabMult`: the exponent absorption** (blueprint
`lem:ml2tangentialSlabMultAbsorb` with `k = 2`, `m = 7`).

Pure `ENNReal` arithmetic, with no geometry and no constants left in it. Substituting the
cardinality bound of Step 3 into the Katz–Tao conclusion `μ ≤ δ^{-4ϱ} |𝕎''_S|^β` — the loss
`4ϱ` at which `Kakeya.VeryNotSticky.SlabMultKT.estimate` is read — gives

`μ ≤ δ^{-4ϱ} (δ^{-3ϱ} ρ₂^{-2})^β = δ^{-4ϱ} δ^{-3ϱβ} ρ₂^{-2β} ≤ δ^{-7ϱ} ρ₂^{-2β}`,

using `hβ1 : β ≤ 1` and `0 < δ ≤ 1` for `(δ^{-3ϱ})^β ≤ δ^{-3ϱ}`. Seven of the `C_sep/4 = 2^18`
available powers of `δ^{-ϱ}` are spent, and `cfg.hϱ : 0 < ϱ` with the antitonicity of
`s ↦ δ^s` closes the gap to the quarter budget. -/
private lemma slabMultAbsorb (hβ1 : cfg.β ≤ 1) {μ : ENNReal}
    (hμ : μ ≤ (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) *
      ((cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) ^ cfg.β) :
    μ ≤ (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) *
      (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
  have hδE_ne0 : (cfg.δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδE_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE_le_one : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hstep : (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ) * cfg.β) ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one
    nlinarith [cfg.hϱ, hβ1]
  have hsplit : (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) *
        ((cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) ^ cfg.β
      = (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) * (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ) * cfg.β) *
          (cfg.rho2 : ENNReal) ^ ((-(2 : ℝ)) * cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ cfg.hβ.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    ac_rfl
  have hle_mostly : (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) *
        (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ) * cfg.β) *
        (cfg.rho2 : ENNReal) ^ ((-(2 : ℝ)) * cfg.β) ≤
      (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) * (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) *
        (cfg.rho2 : ENNReal) ^ ((-(2 : ℝ)) * cfg.β) := by
    gcongr
  have hpow : (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) * (cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) *
        (cfg.rho2 : ENNReal) ^ ((-(2 : ℝ)) * cfg.β) =
      (cfg.δ : ENNReal) ^ (-(7 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
    rw [← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
    congr 2 <;> ring
  have hfδ : (cfg.δ : ENNReal) ^ (-(7 * cfg.ϱ)) ≤
      (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one
    unfold parameterSeparationConstant
    have hbig : (28 : ℝ) ≤ 2 ^ 20 := by norm_num
    nlinarith [cfg.hϱ, hbig]
  calc μ ≤ _ := hμ
    _ = _ := hsplit
    _ ≤ _ := hle_mostly
    _ = _ := hpow
    _ ≤ (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) *
          (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := mul_le_mul' hfδ le_rfl

end SlabMultSteps

/-- **Multiplicity inside one dense slab** (blueprint `lem:ml2tangentialSlabMult`).

At the dense slab `S` produced by `Kakeya.VeryNotSticky.tangentialSlabDecomp`, the anisotropic
rescaling of blueprint `hyp:ml2anisotropicSlabRescale` turns `𝕎''_S` into a family of
`ρ₂`-tubes in the unit ball with the same `μ` and the same `λ`, and the Katz–Tao estimate for
`ρ₂`-tubes bounds its multiplicity by `δ^{-7ϱ} ρ₂^{-2β}`, which fits inside the quarter budget
`δ^{-C_sep ϱ/4}`.

The proof is the composition of the four steps `Kakeya.VeryNotSticky.slabFullness`,
`slabKatzTao`, `Kakeya.VeryNotSticky.slabCard` and `slabMultAbsorb`
above, the transport between the two coordinate systems being
`ShadedBody.fullness_affineImage` and `ShadedBody.multiplicity_affineImage`, both exact. See
the section note above for the full commentary.

The blueprint statement of `lem:ml2tangentialSlabMult` also lists the case hypotheses
`params`, `b ≤ δ^{2·exscal}` and `θ < δ^{-τ'} a/b`; none of them is a binder here, because
the argument never reads them. The tangential and non-slab case distinctions are spent one
step earlier, in `Kakeya.VeryNotSticky.tangentialSlabDecomp`, which produces the dense slab
`hslab`, and the parameter budget is spent one step later, in
`Kakeya.VeryNotSticky.goalMult_of_theta_lt`. What this lemma needs of the case is exactly
`hslab` and the rescaling `sp.rescale` it feeds. -/
theorem tangentialSlabMult (cfg : VeryNotSticky.{u}) {τ' : ℝ}
    (hβ1 : cfg.β ≤ 1)
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (ta : TypicalAngleData cfg tc hB τ')
    -- blueprint item (iii): the anisotropic rescaling `hyp:ml2anisotropicSlabRescale` with its
    -- `Δ_max` transport `lem:ml2tangentialDeltamaxTransport`, for an admissible `CΔ` subject to
    -- the threshold `tangentialDeltamaxThreshold`: `sp.L`, `sp.CΔ`, `sp.CΔAdmissible`,
    -- `sp.rescale` and `sp.CΔ_le`
    (sp : SlabPackage cfg ta)
    -- the dense slab produced by `tangentialSlabDecomp`, with its subfamily `𝕎''_S`
    (S : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (Wd : Finset bd.ω)
    (hslab : IsDenseSlab cfg ta sp.𝕊 S Wd)
    -- blueprint items (i) and (ii): availability of GWZ Lemma 3.7 (`genKKT`) for `ρ₂`-tubes at
    -- Katz–Tao parameter `δ` with loss `4ϱ`, `Δ_max` level `3ϱ` and fullness threshold `η₁`, its
    -- one threshold clause `9η ≤ η₁`, and `tangentialSlabDensityThreshold`
    (kt : SlabMultKT cfg tc) :
    ShadedBody.multiplicity Wd ta.YW ≤
      (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) *
        (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
  let L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) := sp.L S
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L := by
    convert (L.toContinuousAffineEquiv.toHomeomorph).measurableEmbedding using 1
    ext x
    rfl
  let T : bd.ω → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j => (ta.YW j).affineImage L.toAffineMap hcont hemb
  have hcarrier_T : ∀ j ∈ Wd, (T j).carrier = (sp.L S) '' ((tc.thinBall hB).W j).carrier := by
    intro j hj
    have hsub : j ∈ ta.sel := hslab.subset hj
    have htorig : (ta.YW j).toConvexSpaceBody = ((tc.thinBall hB).W j).toConvexSpaceBody :=
      (ta.hrefine.1.2 j hsub).1
    dsimp [T]
    change (sp.L S) '' ((ta.YW j).carrier) = (sp.L S) '' ((tc.thinBall hB).W j).carrier
    congr 1
    exact congrArg (fun K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => K.carrier) htorig
  let Cal : NNReal := latticeRescaleConstant bd.C₀
  have hCalOne : (1 : NNReal) ≤ Cal :=
    one_le_latticeRescaleConstant bd.hC₀
  have hres : IsAnisotropicSlabRescale cfg S Wd (sp.L S) Cal sp.CΔ :=
    sp.rescale S Wd hslab
  have h1 : ∀ j ∈ Wd, (T j).carrier ⊆ Metric.closedBall 0 1 := by
    intro j hj
    rw [hcarrier_T j hj]
    have hj' : j ∈ (tc.thinBall hB).bodies' := ta.hsel (hslab.subset hj)
    calc
      (sp.L S) '' ((tc.thinBall hB).W j).carrier
          ⊆ (sp.L S) '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier := by
            exact Set.image_mono
              (SetLike.coe_subset_coe.mpr ((tc.thinBall hB).W_le_cthickening j hj'))
      _ ⊆ Metric.closedBall 0 1 := hres.A1' j hj
  have hb_pos : (0 : NNReal) < cfg.b := by
    have ha_pos : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact lt_of_lt_of_le ha_pos cfg.hdims.2.1
  have hr1_pos : (0 : NNReal) < cfg.r₁ := by
    unfold r₁
    exact NNReal.rpow_pos cfg.hδ
  have hrho_pos : (0 : NNReal) < cfg.rho2 := by
    unfold rho2
    exact div_pos hb_pos hr1_pos
  have hrhoR : 0 ≤ (cfg.rho2 : ℝ) := by
    exact_mod_cast hrho_pos.le
  let t : Fin 3 → ℝ := ![(1 : ℝ), (cfg.rho2 : ℝ), (cfg.rho2 : ℝ)]
  have htk : ∀ k, 0 ≤ t k := by
    intro k
    fin_cases k <;> simp [t, hrhoR]
  have h2 : ∀ j ∈ Wd, HasThicknesses (T j).carrier (2 * Cal) t := by
    intro j hj
    have hB_eq : (T j).carrier = (sp.L S) '' ((tc.thinBall hB).W j).carrier :=
      hcarrier_T j hj
    have hj' : j ∈ (tc.thinBall hB).bodies' := ta.hsel (hslab.subset hj)
    let A : Set (EuclideanSpace ℝ (Fin 3)) := (sp.L S) '' (bd.Wb j).carrier
    let C : Set (EuclideanSpace ℝ (Fin 3)) :=
      (sp.L S) '' ((bd.Wb j).cthickening (bd.Wb j).scale).carrier
    have hAB : A ⊆ (T j).carrier := by
      rw [hB_eq]
      exact Set.image_mono
        (SetLike.coe_subset_coe.mpr ((tc.thinBall hB).Wb_le_W j hj'))
    have hBC : (T j).carrier ⊆ C := by
      rw [hB_eq]
      exact Set.image_mono
        (SetLike.coe_subset_coe.mpr ((tc.thinBall hB).W_le_cthickening j hj'))
    have hBbdd : Bornology.IsBounded (T j).carrier := by
      exact (T j).toConvexSpaceBody.isCompact'.isBounded
    have hCbdd : Bornology.IsBounded C := by
      exact ((((bd.Wb j).cthickening (bd.Wb j).scale).isCompact').image hcont).isBounded
    intro k
    constructor
    · have hinv : ((2 * Cal : NNReal) : ℝ)⁻¹ ≤ ((Cal : NNReal) : ℝ)⁻¹ := by
        have hcast : ((2 * Cal : NNReal) : ℝ) = 2 * ((Cal : NNReal) : ℝ) := by norm_cast
        rw [hcast]
        have hcpos : 0 < ((Cal : NNReal) : ℝ) := by
          have h1' : (1 : ℝ) ≤ ((Cal : NNReal) : ℝ) := by exact_mod_cast hCalOne
          linarith
        have h2pos : 0 < 2 * ((Cal : NNReal) : ℝ) := mul_pos (by norm_num) hcpos
        exact (inv_le_inv₀ h2pos hcpos).2 (by linarith)
      have hmono : Metric.thickness ℝ A ≤ Metric.thickness ℝ (T j).carrier := by
        exact Metric.thickness_monotone hBbdd hAB
      calc
        ((2 * Cal : NNReal) : ℝ)⁻¹ * t k ≤ ((Cal : NNReal) : ℝ)⁻¹ * t k := by
          exact mul_le_mul_of_nonneg_right hinv (htk k)
        _ ≤ Metric.thickness ℝ A k := (hres.A2 j hj k).1
        _ ≤ Metric.thickness ℝ (T j).carrier k := hmono k
    · have hmono : Metric.thickness ℝ (T j).carrier ≤ Metric.thickness ℝ C := by
        exact Metric.thickness_monotone hCbdd hBC
      calc
        Metric.thickness ℝ (T j).carrier k ≤ Metric.thickness ℝ C k := hmono k
        _ ≤ ((2 * Cal : NNReal) : ℝ) * t k := (hres.A2' j hj k).2
  -- hypothesis (3): Katz–Tao at `δ^{-3ϱ}`, the `Δ_max` level at which `kt.estimate` is read
  have h3 : ConvexSpaceBody.IsKatzTao Wd (fun j ↦ (T j).toConvexSpaceBody)
      ((cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ))) :=
    slabKatzTao hslab (fun j => (T j).toConvexSpaceBody) hcarrier_T
  -- hypothesis (4): `δ^{η₁}`-fullness, transported by the (exact) affine invariance of `λ`
  have h4 : cfg.δ ^ kt.η₁ ≤ ShadedBody.fullness Wd T := by
    calc
      cfg.δ ^ kt.η₁ ≤ ShadedBody.fullness Wd ta.YW := slabFullness hslab kt
      _ = ShadedBody.fullness Wd T := by
        rw [← ShadedBody.fullness_affineImage Wd ta.YW L hcont hemb]
  have hKT_est : ShadedBody.multiplicity Wd T ≤
      (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) * (Wd.card : ENNReal) ^ cfg.β := by
    exact kt.estimate Wd T h1 h2 h3 h4
  have hcardpow : (Wd.card : ENNReal) ^ cfg.β ≤
      ((cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) ^ cfg.β := by
    exact (ENNReal.monotone_rpow_of_nonneg cfg.hβ.le) (slabCard hslab)
  have hμ0 : ShadedBody.multiplicity Wd T ≤
      (cfg.δ : ENNReal) ^ (-(4 * cfg.ϱ)) *
        ((cfg.δ : ENNReal) ^ (-(3 * cfg.ϱ)) * (cfg.rho2 : ENNReal) ^ (-(2 : ℝ))) ^ cfg.β := by
    exact hKT_est.trans (mul_le_mul' le_rfl hcardpow)
  rw [← ShadedBody.multiplicity_affineImage Wd ta.YW L hcont hemb]
  exact slabMultAbsorb hβ1 hμ0

/-- [Main Lemma 2, tangential case] (blueprint `lem:ml2tangential`).
In the configuration `cfg`, together with the per-ball data `bd` of Configuration
`hyp:ml2setup`, the thin-case configuration `tc` of Configuration `hyp:ml2thinsetup` over it,
a ball `B ∈ 𝔅`, the thin-case refinement `a ≤ δ^{1-τ}` and
`b ≤ δ^{exscal} r_1 = δ^{2·exscal}`, with `θ` a typical angle of intersection with constant
`Ctyp` (blueprint Def 6.12, `Kakeya.IsTypicalPlankAngle`) for the plank
family `P` realising the factoring slabs `𝕎'_B` (aspect ratio `a'/b' = a/b`), and `τ'` as in
`goalMult_of_theta_ge`,
suppose we are in the *tangential case*, i.e. `θ < δ^{-τ'} (a/b)`. The field
`params.tangential` replaces the blueprint's `O(ϱ + τ')` loss by the explicit coefficient
`Kakeya.VeryNotSticky.parameterSeparationConstant`. The multiplicity estimate `eqgoalmuT`
then holds with the gain

`ν = exscal β ζ / 2`.

The weaker conclusion `∃ ν > 0, cfg.goalMult ν` was insufficient:
`Kakeya.VeryNotSticky.goalMult_of_multBodies_ge` must conclude the *named* exponent
`Kakeya.VeryNotSticky.bigmultExponent`, the minimum of `½ τ' β` and `½ exscal β ζ`, and an
existentially bound gain cannot be weakened to it.

As in the transverse case, the plank family is indexed by `bd.ω` and carried by the family
`𝕎'_B` of the thin-case data at `B`, i.e. `(tc.thinBall hB).bodies'`, and the plank
presentation, the angle, its constant and the `⪆ 1` refinement `(𝕎''_B, Y_{𝕎''_B})` travel in
the single bundle `ta : Kakeya.VeryNotSticky.TypicalAngleData cfg tc hB τ'`, which is exactly
what `Kakeya.VeryNotSticky.exists_isTypicalAnglePlank` returns. The field
`scale.rho2Star_le_one` ensures that the dilated scale `ρ₂*` remains at most one.

`hBmax` is consumed only through `Kakeya.VeryNotSticky.nonslabSplitBound`; see its docstring
for why it is not available from `cfg` alone. `hβ1 : β ≤ 1` is consumed three times over: by
`nonslabSplitBound`, by `tangentialSlabDecomp` (through the exponent check
`lem:ml2tangentialSlabDecompExponent`, which turns `params.transverse` into `7η < τ'`) and by
`tangentialSlabMult` (in the form `(δ^{-3ϱ})^β ≤ δ^{-3ϱ}`).

Items (a)–(c) of blueprint `lem:ml2tangential` are carried explicitly, since none of the
three lemmas above discharges them and nothing else in the tangential case does either. They
travel in the single bundle `tin : Kakeya.VeryNotSticky.TangentialInputs cfg tc τ'`, one
field per item: `tin.slab` is item (a) together with the rescaling of item (b),
`tin.slabMult` the analytic half of item (b), `tin.split` item (c). The bundle is threaded up
to `Kakeya.VeryNotSticky.CaseSideData`, so that the consumers of this leaf carry it rather
than assume its conclusion; see its docstring. The two Katz–Tao hypotheses it contains are
genuinely different cross-sections: `tin.split.katzTao` is
`Kakeya.VeryNotSticky.KTScaleData`, needed by `nonslabSplitBound` for subfamilies of the
`δ`-tubes `cfg.T`, while `tin.slabMult.estimate` is
`Kakeya.VeryNotSticky.KTRho2ScaleData`, needed by `tangentialSlabMult` for the rescaled
`ρ₂`-tubes.

The slab family `𝕊` of blueprint `hyp:ml2tangentialSlabFamily` is assumed, not constructed;
see `Kakeya.VeryNotSticky.IsSlabFamily`. Correspondingly the rescaling data `L` and
`SlabPackage.rescale` are quantified over exactly the pairs `(S, Wd)` that
`tangentialSlabDecomp` can return out of that `𝕊`, i.e. over
`Kakeya.VeryNotSticky.IsDenseSlab cfg ta sp.𝕊 S Wd`. Quantifying `L` over *all* convex
bodies would demand an affine map turning every contained body into a `ρ₂`-tube, which is
unsatisfiable, and would make the hypothesis — and hence this leaf — vacuous; so would
listing the clauses of `IsDenseSlab` by hand and omitting the angle clause, which an earlier
version of this statement did.

The thin-case hypothesis `a ≤ δ^{1-τ}` is *not* carried: the tangential chain never reads it,
`hnotslab` being the only case hypothesis its three lemmas consume, so it was dropped rather
than retained as an unused argument.

The proof is the arithmetic of the blueprint. `tangentialSlabDecomp` and
`tangentialSlabMult` give the outer factor
`μ(𝕎'_B, Y_{𝕎'_B}) ≤ δ^{-C_sep(ϱ+τ')/4} ρ₂^{-2β}`; substituting it into
`nonslabSplitBound` cancels `ρ₂^{-2β}` against `ρ₂^{(2+ζ)β}` and leaves `ρ₂^{ζβ}`, which
`rho2_range` bounds by `δ^{exscal ζ β}`. The three quarter-budgets sum to at most
`C_sep(ϱ+τ')`, since `η < ϱ` by `params.densityBias` and `τ' > 0`, and `params.tangential`
bounds that by `½ exscal β ζ`, leaving exactly the required gain. -/
theorem goalMult_of_theta_lt_explicit (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    -- blueprint `lem:ml2tangential`(a)–(c)
    (tin : TangentialInputs cfg tc τ') :
    cfg.goalMult (cfg.exscal * cfg.β * cfg.ζ / 2) := by
  set sp := tin.slab hB ta with hsp
  let Eouter : ℝ := -((parameterSeparationConstant * (cfg.ϱ + cfg.η)) / 4)
  let Einner : ℝ :=
    -(parameterSeparationConstant * τ' / 4) + -(parameterSeparationConstant * cfg.ϱ / 4)
  let Cρ : ℝ := (2 + cfg.ζ) * cfg.β
  let Eδ : ℝ := -((parameterSeparationConstant * (2 * cfg.ϱ + cfg.η + τ')) / 4)
  have hA_B : Eouter + Einner = Eδ := by
    dsimp [Eouter, Einner, Eδ]; ring
  have hδE_pos : 0 < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδE_ne0 : (cfg.δ : ENNReal) ≠ 0 := hδE_pos.ne'
  have hδE_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE_le_one : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hb_pos : (0 : NNReal) < cfg.b := by
    have ha_pos : (0 : NNReal) < cfg.a := lt_of_lt_of_le cfg.hδ cfg.hdims.1
    exact lt_of_lt_of_le ha_pos cfg.hdims.2.1
  have hr1_pos : (0 : NNReal) < cfg.r₁ := by
    unfold r₁
    exact NNReal.rpow_pos cfg.hδ
  have hρE_pos : 0 < (cfg.rho2 : ENNReal) := by
    rw [ENNReal.coe_pos]
    exact div_pos hb_pos hr1_pos
  have hρE_ne0 : (cfg.rho2 : ENNReal) ≠ 0 := hρE_pos.ne'
  have hρE_ne_top : (cfg.rho2 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hnotslabR : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
    have h2 : cfg.δ ^ (2 * cfg.exscal) = cfg.δ ^ cfg.exscal * cfg.r₁ := by
      unfold r₁
      rw [← NNReal.rpow_add cfg.hδ.ne' cfg.exscal cfg.exscal]
      congr 1; ring
    exact hnotslab.trans_eq h2
  have hle : cfg.rho2 ≤ cfg.δ ^ cfg.exscal := by
    rw [rho2]
    rw [div_le_iff₀ hr1_pos]
    exact hnotslabR
  have hρ2le_e : (cfg.rho2 : ENNReal) ≤ (cfg.δ : ENNReal) ^ cfg.exscal := by
    rw [← ENNReal.coe_rpow_of_nonneg cfg.δ cfg.hexscal.le]
    exact ENNReal.coe_le_coe.mpr hle
  have hρbo : (cfg.rho2 : ENNReal) ^ (cfg.ζ * cfg.β) ≤
      (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ) := by
    calc (cfg.rho2 : ENNReal) ^ (cfg.ζ * cfg.β)
        ≤ ((cfg.δ : ENNReal) ^ cfg.exscal) ^ (cfg.ζ * cfg.β) :=
          ENNReal.rpow_le_rpow hρ2le_e (mul_nonneg cfg.hζ.le cfg.hβ.le)
      _ = (cfg.δ : ENNReal) ^ (cfg.exscal * (cfg.ζ * cfg.β)) := by
          rw [← ENNReal.rpow_mul (cfg.δ : ENNReal) cfg.exscal (cfg.ζ * cfg.β)]
      _ = (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ) := by
          congr 1; ring
  rcases tangentialSlabDecomp cfg params hβ1 tc hB ta htang sp with
    ⟨S, Wd, hslab, hmult⟩
  have hmultWd : ShadedBody.multiplicity Wd ta.YW ≤
      (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) *
        (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) :=
    tangentialSlabMult cfg hβ1 tc hB ta sp S Wd hslab tin.slabMult
  have hmuW_comb : ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W ≤
      (cfg.δ : ENNReal) ^ Einner * (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
    calc
      ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W
        ≤ (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * τ' / 4)) *
            ShadedBody.multiplicity Wd ta.YW := hmult
      _ ≤ (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * τ' / 4)) *
            ((cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) *
              (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β))) := by
            gcongr
      _ = (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * τ' / 4)) *
            (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * cfg.ϱ / 4)) *
            (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
            rw [← mul_assoc]
      _ = (cfg.δ : ENNReal) ^ (-(parameterSeparationConstant * τ' / 4) +
            -(parameterSeparationConstant * cfg.ϱ / 4)) *
            (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
            rw [← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
      _ = (cfg.δ : ENNReal) ^ Einner * (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) := by
            rfl
  have houter :=
    nonslabSplitBoundPB cfg hβ1 hnotslab tc hB hBmax scale tin.split
  have hmain : ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (Eδ + cfg.exscal * cfg.β * cfg.ζ) *
        (cfg.s.card : ENNReal) ^ cfg.β := by
    calc
      ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
        ≤ (cfg.δ : ENNReal) ^ Eouter *
            ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W *
            (cfg.rho2 : ENNReal) ^ Cρ *
            (cfg.s.card : ENNReal) ^ cfg.β := houter
      _ ≤ (cfg.δ : ENNReal) ^ Eouter *
            ((cfg.δ : ENNReal) ^ Einner * (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β))) *
            (cfg.rho2 : ENNReal) ^ Cρ * (cfg.s.card : ENNReal) ^ cfg.β := by
            gcongr
      _ = ((cfg.δ : ENNReal) ^ Eouter * (cfg.δ : ENNReal) ^ Einner) *
            ((cfg.rho2 : ENNReal) ^ (-(2 * cfg.β)) * (cfg.rho2 : ENNReal) ^ Cρ) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            ac_rfl
      _ = (cfg.δ : ENNReal) ^ (Eouter + Einner) *
            (cfg.rho2 : ENNReal) ^ (-(2 * cfg.β) + Cρ) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            rw [← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
            rw [← ENNReal.rpow_add _ _ hρE_ne0 hρE_ne_top]
      _ = (cfg.δ : ENNReal) ^ (Eouter + Einner) * (cfg.rho2 : ENNReal) ^ (cfg.ζ * cfg.β) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            congr 1
            congr 1
            dsimp [Cρ]
            ring_nf
      _ ≤ (cfg.δ : ENNReal) ^ (Eouter + Einner) *
            (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            gcongr
      _ = (cfg.δ : ENNReal) ^ (Eouter + Einner + cfg.exscal * cfg.β * cfg.ζ) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            rw [← ENNReal.rpow_add _ _ hδE_ne0 hδE_ne_top]
      _ = (cfg.δ : ENNReal) ^ (Eδ + cfg.exscal * cfg.β * cfg.ζ) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            congr 1; rw [hA_B]
  have hηltϱ : cfg.η < cfg.ϱ := by
    have hC : (1 : ℝ) ≤ parameterSeparationConstant := by
      unfold parameterSeparationConstant; norm_num
    nlinarith [params.densityBias, cfg.hη, hC]
  have hτ'pos : 0 < τ' := lt_trans params.hτ params.hτ'
  have hCsep0 : 0 < parameterSeparationConstant := by
    unfold parameterSeparationConstant; positivity
  have hlin : 2 * cfg.ϱ + cfg.η + τ' ≤ 4 * cfg.ϱ + 4 * τ' := by
    nlinarith [hηltϱ, cfg.hϱ, hτ'pos]
  have hσ4 : parameterSeparationConstant * (2 * cfg.ϱ + cfg.η + τ') / 4 ≤
      parameterSeparationConstant * (cfg.ϱ + τ') := by
    nlinarith [hlin, hCsep0]
  have hbudget : parameterSeparationConstant * (2 * cfg.ϱ + cfg.η + τ') / 4 ≤
      cfg.exscal * cfg.β * cfg.ζ / 2 :=
    (lt_of_le_of_lt hσ4 params.tangential).le
  have hExp : cfg.exscal * cfg.β * cfg.ζ / 2 ≤ Eδ + cfg.exscal * cfg.β * cfg.ζ := by
    dsimp [Eδ]
    nlinarith [hbudget]
  have hmainFinal : (cfg.δ : ENNReal) ^ (Eδ + cfg.exscal * cfg.β * cfg.ζ) *
      (cfg.s.card : ENNReal) ^ cfg.β ≤
    (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ / 2) * (cfg.s.card : ENNReal) ^ cfg.β := by
    have hδpow : (cfg.δ : ENNReal) ^ (Eδ + cfg.exscal * cfg.β * cfg.ζ) ≤
        (cfg.δ : ENNReal) ^ (cfg.exscal * cfg.β * cfg.ζ / 2) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one hExp
    exact mul_le_mul' hδpow le_rfl
  unfold goalMult
  exact hmain.trans hmainFinal

set_option linter.unusedVariables false in
/-- **[Main Lemma 2, tangential case] with the gain left existential** (blueprint
`lem:ml2tangential`).

`Kakeya.VeryNotSticky.goalMult_of_theta_lt_explicit` read at `ν = ½ exscal β ζ`, which is
positive by `cfg.hexscal`, `cfg.hβ` and `cfg.hζ`. It is the blueprint's own phrasing — "the
goal holds with a positive gain, the blueprint value being `ν = exscal β ζ / 2`" — and is kept
so that blueprint `lem:ml2tangential` has a Lean statement in that shape.

It carries the *same* hypotheses as the explicit form. It is restated with
the explicit form's hypotheses, and proved from it, rather than deleted, because blueprint
`lem:ml2tangential` points its `\lean{...}` at this name.

Like the explicit form it carries `hβ1` without using it; see that docstring. -/
@[nolint unusedArguments]
theorem goalMult_of_theta_lt (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hnotslab : cfg.b ≤ cfg.δ ^ (2 * cfg.exscal))
    {bd : BallData cfg} (tc : ThinConfig cfg bd) {B : bd.bι} (hB : B ∈ bd.bs)
    (hBmax : ∀ (B' : bd.bι) (hB' : B' ∈ bd.bs),
      ShadedBody.multiplicity (tc.thinBall hB').bodies' (tc.thinBall hB').W ≤
        ShadedBody.multiplicity (tc.thinBall hB).bodies' (tc.thinBall hB).W)
    {νA : ℝ} {thr : ScaleThresholds}
    (scale : CaseScale cfg bd τ τ' νA tc.C thr)
    (ta : TypicalAngleData cfg tc hB τ')
    (htang : ta.θ < cfg.δ ^ (-τ') * (cfg.a / cfg.b))
    (tin : TangentialInputs cfg tc τ') :
    ∃ ν > (0 : ℝ), cfg.goalMult ν := by
  exact ⟨cfg.exscal * cfg.β * cfg.ζ / 2, by
    have h₁ : 0 < cfg.exscal := cfg.hexscal
    have h₂ : 0 < cfg.β := cfg.hβ
    have h₃ : 0 < cfg.ζ := cfg.hζ
    positivity,
    goalMult_of_theta_lt_explicit cfg params hβ1 hnotslab tc hB hBmax scale ta htang tin⟩

end Kakeya.VeryNotSticky
