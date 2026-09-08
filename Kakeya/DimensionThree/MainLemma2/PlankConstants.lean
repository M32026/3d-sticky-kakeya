/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody.Counting
public import Kakeya.Homothety
public import Kakeya.Discretization
public import Kakeya.DimensionThree.Volume
public import Kakeya.DimensionThree.MainLemma2.Section6Compat

/-!
# The two named constants of the plank presentation

This file carries the constants `C_{lem:ml2plankpresentation}(C₀)` (blueprint
`def:ml2plankEnclosureConstant`, Lean `Kakeya.VeryNotSticky.plankEnclosureConstant`) and
`C^{sel}(C₀)` (blueprint `def:ml2plankSelectionConstant`, Lean
`Kakeya.VeryNotSticky.plankSelectionConstant`), together with the absolute clustering dilation
constant that the second is built from.

**Why they live here and not with their consumers.** Both are mentioned by fields of
Configuration `hyp:ml2scale`, i.e. by `Kakeya.VeryNotSticky.CaseScale` in
`Kakeya.DimensionThree.MainLemma2.ThinConfig`: `plankEnclosureConstant` by the tenth clause
`plankCard_bias`, and `plankSelectionConstant` by the twelfth,
`typicalAngle_selection`, which is the blueprint's `typicalAngleSelectionThreshold` and the
threshold that `Kakeya.VeryNotSticky.plankSubfamilyMult` consumes as its `hthr`. Their natural
home would be `Kakeya.DimensionThree.MainLemma2.PlankPresentation`, where the lemmas that
produce them live — but that file *imports* `ThinConfig`, so a `CaseScale` clause could not
mention them. Neither constant names any data beyond `C₀`, so both are free to sit at this
earlier point, upstream of `ThinConfig`; that is the whole content of this file's existence.

Only the *definitions* move. Every lemma that uses these constants geometrically —
`Kakeya.VeryNotSticky.plankClusterBound`, `Kakeya.VeryNotSticky.plankSubfamilySelection`,
`Kakeya.VeryNotSticky.plankEnclosureVolume` — stays in `PlankPresentation`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

noncomputable section

/-- Shorthand for the ambient space of the non-slab case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

namespace Kakeya.VeryNotSticky

/-! ### The enclosure constant -/

/-- **Constant in Lemma `lem:ml2plankpresentation`** (blueprint
`def:ml2plankEnclosureConstant`).

`C_{lem:ml2plankpresentation}(C₀)` is the volume loss incurred when the rescaled factoring
body `L_B(W)`, whose affine thicknesses are only *comparable* to `(1, b', a')` with the
constant `C₀` of (C4), is replaced by an exact `a' × b' × 1` plank containing it. It bounds
the ratio `|P| / |L_B(W)|` for the plank `P` produced by
`Prism3D.exists_superset_of_hasThicknesses`, and hence the loss in `Δ_max` when the family
`𝕎'_B` is replaced by the plank family `𝒫`.

It is the exact analogue of `Kakeya.VeryNotSticky.slabPrismEnclosureConstant`, which plays the
same role for the prism enclosure of the slab case, and is given the same provisional value:
`Prism3D.enclosureVolumeConstant C₀ = 48 C₀⁶` is the honest bound for a single body, and the
displayed value leaves room for the fixed dimensional factors of the passage to `Δ_max`.

It lives here, upstream of `Kakeya.VeryNotSticky.CaseScale`, because the tenth clause
`Kakeya.VeryNotSticky.CaseScale.plankCard_bias` of Configuration `hyp:ml2scale` mentions it; a
constant naming no data beyond `C₀` is free to sit at the earlier point. -/
def plankEnclosureConstant (C₀ : NNReal) : NNReal := max 1 (2 ^ 20 * C₀ ^ 6)

lemma one_le_plankEnclosureConstant (C₀ : NNReal) : 1 ≤ plankEnclosureConstant C₀ :=
  le_max_left _ _

/-! ### Bounded clustering: the dilation constant -/

/-- **A clustering dilation constant.**

`C` is a clustering dilation constant when `C ≥ 1` and any two rectangular prisms of `ℝ³` of
equal positive volume that fail to be essentially distinct lie in a common `C`-dilate of the
first. It is the one geometric input of the degree bound
`Kakeya.VeryNotSticky.plankClusterBound`.

The predicate is separated from the constant `Kakeya.VeryNotSticky.clusterDilationConstant`
that realises it because the convex-geometry statement it rests on,
`Kakeya.exists_essOverlapDilate_constant`, supplies its own constant existentially and no
value can be displayed. -/
structure IsClusterDilationConstant (C : NNReal) : Prop where
  /-- a dilation constant is at least `1` -/
  one_le : 1 ≤ C
  /-- two clustered prisms of equal positive volume lie in a common `C`-dilate of the first -/
  subset_dilation : ∀ P Q : PrismNDim 3 E₃ E₃,
    volume (P.carrier : Set E₃) = volume (Q.carrier : Set E₃) →
    0 < volume (P.carrier : Set E₃) →
    ¬ IsEssentiallyDistinct (P.carrier : Set E₃) (Q.carrier : Set E₃) →
    (Q.carrier : Set E₃) ⊆ ((P.dilation C).carrier : Set E₃)

/-- **Clustered planks lie in a common dilate** (blueprint `lem:ml2plankClusterDilate`).

An absolute clustering dilation constant exists. The hypothesis inside
`Kakeya.VeryNotSticky.IsClusterDilationConstant` is equality of *volumes* and not of
half-widths, which is all the proof uses; at the call site the planks do have the same
half-widths `a' × b' × 1` and hence the common volume `8 a' b' > 0`. Positivity is not
decoration: at volume `0` no pair fails to be essentially distinct, so the statement would be
vacuous, but the case has to be excluded rather than argued. -/
theorem exists_isClusterDilationConstant : ∃ C : NNReal, IsClusterDilationConstant C := by
  -- First application of the (accepted) convex-geometry lemma at θ = 1/2.
  have hθ₁pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hθ₁le : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rcases exists_essOverlapDilate_constant 3 (hθ := hθ₁pos) (hθ1 := hθ₁le) with ⟨C₁, hC₁, hprop₁⟩
  have hC₁pos : (0 : ℝ) < C₁ := lt_of_lt_of_le zero_lt_one hC₁
  have hC₁nn : (0 : ℝ) ≤ C₁ := le_of_lt hC₁pos
  let θ₂ : ℝ := ((C₁ : ℝ)⁻¹) ^ 3
  have hθ₂nn : 0 ≤ θ₂ := by dsimp [θ₂]; exact pow_nonneg (inv_nonneg.mpr hC₁nn) _
  have hθ₂pos : 0 < θ₂ := by dsimp [θ₂]; positivity
  have hθ₂le : θ₂ ≤ 1 := by
    dsimp [θ₂]
    exact pow_le_one₀ (inv_nonneg.mpr hC₁nn) ((inv_le_one₀ hC₁pos).mpr hC₁)
  rcases exists_essOverlapDilate_constant 3 (hθ := hθ₂pos) (hθ1 := hθ₂le) with ⟨C₂, hC₂, hprop₂⟩
  have hC₂nn : (0 : ℝ) ≤ C₂ := le_trans zero_le_one hC₂
  let C₂n : NNReal := ⟨C₂, hC₂nn⟩
  have hC₂n : (1 : NNReal) ≤ C₂n := by
    dsimp [C₂n]
    exact_mod_cast hC₂
  let Cc : NNReal := 2 * C₂n - 1
  have hCce : (1 : NNReal) ≤ Cc := by
    dsimp [Cc]
    have htw : (2 : NNReal) ≤ 2 * C₂n := by
      calc
        (2 : NNReal) = 2 * 1 := (mul_one _).symm
        _ ≤ 2 * C₂n := mul_le_mul_of_nonneg_left hC₂n (by norm_num : (0 : NNReal) ≤ 2)
    have h1le : (1 : NNReal) ≤ 2 * C₂n := le_trans (by norm_num) htw
    rw [le_tsub_iff_right h1le]
    rw [show (1 + 1 : NNReal) = 2 by norm_num]
    exact htw
  refine ⟨Cc, hCce, ?_⟩
  intro P Q hvol hpos hnot
  -- Unpack `¬ IsEssentiallyDistinct` to a strict intersection-volume inequality.
  have hnot' : ¬ (volume ((P.carrier : Set E₃) ∩ (Q.carrier : Set E₃)) ≤
      (1 / 2 : ENNReal) * max (volume (P.carrier : Set E₃)) (volume (Q.carrier : Set E₃))) := by
    simpa [_root_.IsEssentiallyDistinct] using hnot
  have hlt : (1 / 2 : ENNReal) * max (volume (P.carrier : Set E₃)) (volume (Q.carrier : Set E₃))
      < volume ((P.carrier : Set E₃) ∩ (Q.carrier : Set E₃)) := lt_of_not_ge hnot'
  have hlt' : (1 / 2 : ENNReal) * volume (P.carrier : Set E₃)
      < volume ((P.carrier : Set E₃) ∩ (Q.carrier : Set E₃)) := by
    simpa [max_eq_left (le_of_eq hvol.symm)] using hlt
  have hMvol : 0 < volume ((P.carrier : Set E₃) ∩ (Q.carrier : Set E₃)) := by
    have hp : (0 : ENNReal) < (1 / 2 : ENNReal) := by norm_num
    have hprod : (0 : ENNReal) < (1 / 2 : ENNReal) * volume (P.carrier : Set E₃) := by
      positivity
    exact lt_trans hprod hlt'
  have hMne : ((P.carrier : Set E₃) ∩ (Q.carrier : Set E₃)).Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero (ne_of_gt hMvol)
  let M : ConvexSpaceBody E₃ :=
    ConvexSpaceBody.inter P.toConvexSpaceBody Q.toConvexSpaceBody hMne
  have hMvol' : 0 < volume (M.carrier : Set E₃) := by simpa [M] using hMvol
  have hMP : (M.carrier : Set E₃) ⊆ (P.carrier : Set E₃) := by
    simp [M, ConvexSpaceBody.inter]
  have hMQ : (M.carrier : Set E₃) ⊆ (Q.carrier : Set E₃) := by
    simp [M, ConvexSpaceBody.inter]
  have hofHalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  rcases hprop₁ M hMvol' with ⟨z, hzM, hzprop⟩
  have hzPvol : ENNReal.ofReal (1 / 2 : ℝ) * volume (P.carrier : Set E₃)
      ≤ volume (M.carrier : Set E₃) := by
    simpa [hofHalf, M] using (le_of_lt hlt')
  have hzQvol : ENNReal.ofReal (1 / 2 : ℝ) * volume (Q.carrier : Set E₃)
      ≤ volume (M.carrier : Set E₃) := by
    simpa [hofHalf, M, hvol] using (le_of_lt hlt')
  have hzpropP : (P.carrier : Set E₃) ⊆ AffineMap.homothety z C₁ '' (M.carrier : Set E₃) := by
    apply hzprop P.toConvexSpaceBody
    · exact hMP
    · exact hzPvol
  let R : ConvexSpaceBody E₃ := M.homothety z C₁
  have hPR : (P.carrier : Set E₃) ⊆ (R.carrier : Set E₃) := by
    simpa [R, ConvexSpaceBody.homothety, ConvexSpaceBody.affineImage] using hzpropP
  have hzpropQ : (Q.carrier : Set E₃) ⊆ AffineMap.homothety z C₁ '' (M.carrier : Set E₃) := by
    apply hzprop Q.toConvexSpaceBody
    · exact hMQ
    · exact hzQvol
  have hQR : (Q.carrier : Set E₃) ⊆ (R.carrier : Set E₃) := by
    simpa [R, ConvexSpaceBody.homothety, ConvexSpaceBody.affineImage] using hzpropQ
  have hfin : Module.finrank ℝ E₃ = 3 := by norm_num
  have hRvol : volume (R.carrier : Set E₃)
      = ENNReal.ofReal ((C₁ : ℝ) ^ 3) * volume (M.carrier : Set E₃) := by
    change volume ((M.homothety z C₁).carrier : Set E₃)
      = ENNReal.ofReal (C₁ ^ 3) * volume (M.carrier : Set E₃)
    rw [ConvexSpaceBody.volume_homothety (M : ConvexSpaceBody E₃) z C₁]
    congr 1
    · congr
      rw [hfin]
      exact abs_of_nonneg (pow_nonneg hC₁nn _)
  have hθ₂c13 : θ₂ * ((C₁ : ℝ) ^ 3) = 1 := by
    dsimp [θ₂]
    rw [← mul_pow]
    simp [inv_mul_cancel₀ (ne_of_gt hC₁pos)]
  have hθ₂vol : ENNReal.ofReal θ₂ * volume (R.carrier : Set E₃)
      ≤ volume (P.carrier : Set E₃) := by
    calc
      ENNReal.ofReal θ₂ * volume (R.carrier : Set E₃)
          = ENNReal.ofReal θ₂ * (ENNReal.ofReal ((C₁ : ℝ) ^ 3) * volume (M.carrier : Set E₃)) := by
            rw [hRvol]
      _ = (ENNReal.ofReal θ₂ * ENNReal.ofReal ((C₁ : ℝ) ^ 3)) * volume (M.carrier : Set E₃) := by
            rw [← mul_assoc]
      _ = ENNReal.ofReal (θ₂ * (C₁ : ℝ) ^ 3) * volume (M.carrier : Set E₃) := by
            rw [← ENNReal.ofReal_mul hθ₂nn]
      _ = volume (M.carrier : Set E₃) := by
            rw [hθ₂c13]
            simp
      _ ≤ volume (P.carrier : Set E₃) := by
            exact measure_mono (μ := (volume : Measure E₃)) hMP
  rcases hprop₂ P.toConvexSpaceBody hpos with ⟨zP, hzP, hzPprop⟩
  have hRhom : (R.carrier : Set E₃) ⊆ AffineMap.homothety zP C₂ '' (P.carrier : Set E₃) := by
    apply hzPprop (R : ConvexSpaceBody E₃)
    · exact hPR
    · exact hθ₂vol
  have hQdil : (Q.carrier : Set E₃) ⊆ ((P.dilation Cc).carrier : Set E₃) := by
    calc
      (Q.carrier : Set E₃) ⊆ (R.carrier : Set E₃) := hQR
      _ ⊆ AffineMap.homothety zP (C₂n : ℝ) '' (P.carrier : Set E₃) := by
        rw [show (C₂n : ℝ) = C₂ by rfl]
        exact hRhom
      _ ⊆ ((P.dilation Cc).carrier : Set E₃) := by
        have hsub := PrismNDim.homothety_image_subset_dilation
          P hzP (lam := C₂n) (hlam := hC₂n)
        rwa [show (P.dilation (2 * C₂n - 1) : PrismNDim 3 E₃ E₃) = P.dilation Cc by rfl] at hsub
  exact hQdil

/-- **The clustering dilation constant** `C^{cl}`, an absolute constant.

It is obtained by choice from `Kakeya.VeryNotSticky.exists_isClusterDilationConstant`, no
value being available: the convex-geometry input
`Kakeya.exists_essOverlapDilate_constant` is accepted as an assumption and supplies its
constant existentially. Naming it is what lets `Kakeya.VeryNotSticky.plankClusterBound` and
`Kakeya.VeryNotSticky.plankSelectionConstant` be stated as functions of `C₀` alone, as
blueprint `def:ml2plankSelectionConstant` requires; carrying it as a free parameter instead
would leave `plankPresentation` with a constant it cannot pin down. -/
def clusterDilationConstant : NNReal :=
  Classical.choose exists_isClusterDilationConstant

/-- `Kakeya.VeryNotSticky.clusterDilationConstant` is a clustering dilation constant. -/
theorem isClusterDilationConstant_clusterDilationConstant :
    IsClusterDilationConstant clusterDilationConstant :=
  Classical.choose_spec exists_isClusterDilationConstant

/-! ### The selection constant -/

/-- **Constant in Lemma `lem:ml2plankpresentation`** (blueprint
`def:ml2plankSelectionConstant`, `C^{sel}_{lem:ml2plankpresentation}`).

`C^{sel}(C₀) = D_{lem:ml2plankClusterBound}(C₀) + 1`, where `D_{lem:ml2plankClusterBound}(C₀)`
is the degree bound of `Kakeya.VeryNotSticky.plankClusterBound` on the *clustering* relation
of the enclosing plank family: two indices are clustered when their planks fail to be
essentially distinct. It depends on `C₀`, on the ambient dimension — here fixed at `3` — and
on the absolute constant `Kakeya.VeryNotSticky.clusterDilationConstant`, and on nothing else:
not on `δ`, not on the exponent parameters of `Kakeya.VeryNotSticky.CaseParams`, not on the
ball `B`, not on the scales `a`, `b`, `r₁`, and not on the family. In particular it carries no
power of `δ`, so it is a multiplicative constant in the sense of the constant/exponent
distinction and is discharged where it is consumed rather than against an exponent budget.

The value is *not* provisional and must not be replaced by a polynomial in `C₀`: it is a tower
of exponentials in `C₀` (see `Kakeya.cardEssDistinctConvexInPrismConstant`), and anything
smaller than what `Kakeya.VeryNotSticky.plankSubfamilySelection` can supply would make
`Kakeya.VeryNotSticky.plankPresentation` false rather than merely unproved, a larger constant
giving a weaker refinement.

**Why this constant exists at all.** `Kakeya.VeryNotSticky.plankPresentation` used to assert
that the *enclosing* planks are pairwise essentially distinct. That assertion is **false**, for
every choice of the enclosing planks. Take `C₀²` pairwise disjoint boxes of half-widths
`(1/2, a'/C₀, 2a'/C₀²)` stacked along one axis so as to tile an interval of length `4a'`: they
are pairwise essentially distinct and have thicknesses comparable to `(1, b, a)` with constant
`C₀`, yet every enclosing plank of exact half-widths `(a', a', 1)` has extent `∼ a'` in the
stacking direction, so all `C₀²` planks are confined to a band of width `∼ 5a'` and at most
`O(1)` of them can be pairwise essentially distinct.

Enlarging a set does not preserve essential distinctness, and the enlargement is forced here by
`Plank` carrying *exact* thicknesses `![a, b, 1]`: a body whose thicknesses are merely
*comparable* to `(r₁, b, a)` — which is all (C4) supplies — is not a plank, so it has to be
enclosed in one. GWZ never performs that step; it uses the bodies themselves as planks up to
constants, and essential distinctness is then inherited. So this is a defect of the present
formalization and not of GWZ, whose Lemma 6.11 `Kakeya.findingTypicalAngleOfIntersection_perScale`
legitimately *assumes* an essentially distinct plank family.

The repair is to pass to a subfamily on which the planks *are* pairwise essentially distinct, at
the cost of a refinement factor. The clustering relation has degree at most `D(C₀)`: two planks
of equal volume overlapping in more than half of it lie in a common absolute dilate, inside
which only boundedly many pairwise essentially distinct bodies of volume
`≥ |P| / plankEnclosureConstant C₀` fit; and in any graph of degree at most `D` a greedy
selection in decreasing order of shaded mass keeps a `1/(D+1)` fraction of the total.

Note that the degree bound is a statement about *pairs*. It does **not** say that a point of
`ℝ³` lies in boundedly many of the planks — that is false for the same family, since pairwise
essential distinctness bounds pairwise intersections only and many sets can be pairwise
half-disjoint while sharing a common point. The selection is therefore run on the clustering
graph, and not on a pointwise multiplicity bound.

**Why it lives here.** The twelfth clause
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_selection` of Configuration `hyp:ml2scale`
(blueprint `typicalAngleSelectionThreshold`) asserts `C^{sel}(C₀) ≤ δ^{-exscal·η}`, the
threshold that `Kakeya.VeryNotSticky.plankSubfamilyMult` consumes; so this definition has to
sit upstream of `Kakeya.VeryNotSticky.CaseScale`, exactly as
`Kakeya.VeryNotSticky.plankEnclosureConstant` does for the tenth clause. -/
def plankSelectionConstant (C₀ : NNReal) : NNReal :=
  (cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) : NNReal) + 1

/-- The selection constant `C^{sel}(C₀) = D(C₀) + 1` is at least `1`. -/
lemma one_le_plankSelectionConstant (C₀ : NNReal) : 1 ≤ plankSelectionConstant C₀ :=
  le_add_self

/-! ### The cardinality data of the plank family, and the reduction threshold -/

/-- **Exponent in Lemma `lem:ml2plankcard`.**

The exponent in the polynomial cardinality bound `|𝒫| ≤ C (δ')^{-N}` of
`Kakeya.VeryNotSticky.plankCard`, named rather than written as a literal, following the
convention already used for `Kakeya.exists_bounded_prism_discretization.M` and
`Kakeya.exists_volume_bounded_prism_discretization.M`. It is exactly
`exists_bounded_prism_discretization.M 3 = 3⁴ + 3³ + 3 + 1 = 112`, the exponent in the number
of prisms in the discretization of a ball at scale `δ'` supplied by
`Kakeya.exists_finite_test_family_maxDensity_closedBall`.

There is no `+1`. An earlier version added one, to absorb the per-prism count
`Δ_max(𝒫)|K|/|P| ≲ Δ_max(𝒫)` under the assumption `Δ_max(𝒫) ≤ (δ')⁻¹`. That assumption is not
available: the only density bound the configuration supplies is (C4)'s
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering`, `Δ_max(𝕎_B) ≤ C_bias δ^{-2ϱ}`, and its
constant `C_bias` is itself allowed to depend on `δ`, so converting it into `(δ')⁻¹` is not a
fixed-scale threshold. `Kakeya.VeryNotSticky.plankCard` therefore carries the density bound as
an explicit factor `Δ` instead, and the exponent below counts only the cover.

The blueprint writes `(δ')^{-3}`, which is what one gets from an *optimal* discretization of
the unit ball by `a' × b' × 1` planks. The discretization actually available in this
development is much more wasteful, and the honest exponent is the one below; nothing
downstream cares, because `Kakeya.findingTypicalAngleOfIntersection_perScale` takes the exponent
as an arbitrary real `N` in its hypothesis `hcard`.

**Why it lives here.** The eleventh clause
`Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold` of Configuration `hyp:ml2scale`
names the cardinality data at which the plank-to-slab reduction is invoked, so this exponent
has to sit upstream of `Kakeya.VeryNotSticky.CaseScale`, exactly as
`Kakeya.VeryNotSticky.plankEnclosureConstant` does for the tenth clause. -/
def plankCardExponent : ℝ := exists_bounded_prism_discretization.M 3

/-- **Constant in Lemma `lem:ml2plankcard`.**

The absolute constant in the polynomial cardinality bound
`|𝒫| ≤ C Δ (δ')^{-plankCardExponent}` of `Kakeya.VeryNotSticky.plankCard`. It lives here for
the reason recorded on `Kakeya.VeryNotSticky.plankCardExponent`. -/
noncomputable def plankCardConstant : NNReal := 2 ^ 20

open Classical in
/-- **The ball-filling half of the plank-to-slab reduction, available at the scale `δ`**
(blueprint `def:ml2transverseFillThreshold` together with Items 1 and 5 of
`lemmaredplanktubeAtTypicalAngle`).

This is the fragment of `ShadedPlank.reduction_to_slab_atTypicalAngle` that the transverse
branch consumes — the refinement `(𝒫', Y')`, Item 1 (the almost-filling of a `θ b`-ball) and
Item 5 (the sub-polynomial bound on its constant) — read at the exponents at which the branch
invokes the reduction, `ε = η/256` and `ε' = η/2`, and *at one fixed scale* `δ`.

Isolating it as a predicate is what turns the eleventh clause of Configuration `hyp:ml2scale`
into an informative hypothesis. `ShadedPlank.reduction_to_slab_atTypicalAngle` produces its
smallness threshold `δ_*` existentially, after the exponents and the cardinality data
`(Ccard, D)` and before the scale; that threshold can therefore not be *named* in a structure
declared upstream of the reduction's call site, and the clause `cfg.δ ≤ thr.fill` an earlier
version carried said nothing at all, `Kakeya.VeryNotSticky.ScaleThresholds.fill` having no
defining property. Asserting the *conclusion* at the scale in question says exactly what the
by-choice threshold was meant to say, and `Kakeya.VeryNotSticky.exists_isReductionFillAvailable`
certifies that it does hold below a threshold fixed before the scale, so the clause is neither
vacuous nor unsatisfiable.

Only the items the branch reads are carried. Items 2, 3 and 4, the representative and slab
data and the five hoisted geometric constants play no part in
`Kakeya.VeryNotSticky.transverseFill`, and including them would make the clause harder to
arrange without making it more useful.

The refinement is carried twice: `(𝒫', Y')` refines `(𝒫, Y)` and it also refines `(𝒫, Y'')`,
mirroring the corresponding pair of clauses of
`ShadedPlank.reduction_to_slab_atTypicalAngle`.

The nonemptiness of `U(𝒫', Y')` is carried as well. Item 1 of the reduction fires only at a
point where `U(𝒫', Y')` meets a `θ b`-ball, and the two refinement clauses give no lower
bound on the output family (a refinement may drop every index), so without this clause
`s' = ∅` would satisfy the predicate vacuously and the guard in Item 1 could never be
discharged. It is a consequence of the fullness of the output, `(c_Lam · a^ε) λ(𝒫, Y) ≤
λ(𝒫', Y')`, together with the positivity of `λ(𝒫, Y)`, both of which the full reduction
`ShadedPlank.reduction_to_slab_atTypicalAngle` supplies; recording it here is what lets the
consumer fire Item 1. -/
def IsReductionFillAvailable (ω : Type*) (η : ℝ) (Ccard : NNReal) (D : ℝ) (δ : NNReal) : Prop :=
  ∀ (s : Finset ω) {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (Y : ω → ShadedPlank a b hab hb1)
    (θ : NNReal) (_hθ1 : θ ≤ 1) (C : NNReal)
    (Y'' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))),
    0 < δ → δ ≤ a → a < 1 →
    Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
    a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
    (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
    (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
    2 ≤ (δ : ENNReal) ^ (-η) →
    (s.card : NNReal) ≤ Ccard * δ ^ (-D) →
    a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-(η / 256)) →
    ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
    ShadedBody.HasCConstantMultiplicity s Y'' C →
    Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
      (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
    Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
  ∃ (s' : Finset ω) (Y' : ω → ShadedBody (EuclideanSpace ℝ (Fin 3))) (c1 : NNReal),
    0 < c1 ∧
    ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
    ShadedBody.IsRefinement s' Y' s Y'' ∧
    (ShadedBody.iUnionShade s' Y').Nonempty ∧
    (∀ x,
      ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : NNReal) : ℝ)).Nonempty →
      (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ (η / 256) *
          volume (Metric.closedBall x ((θ * b : NNReal) : ℝ)) ≤
        volume ((⋃ i ∈ s', (Y' i).shade) ∩
          Metric.closedBall x
            ((ShadedPlank.redPlankTube.ballDilation * θ * b : NNReal) : ℝ))) ∧
    c1⁻¹ ≤ δ ^ (-(η / 2))

/-- **The reduction is available below a threshold fixed before the scale** (blueprint
`def:ml2transverseFillThreshold`).

This is what makes the eleventh clause of Configuration `hyp:ml2scale` a genuine fixed-scale
threshold rather than an assumption about the scale it is applied at: the threshold `δ_*`
depends on the exponent `η` and on the cardinality data `(Ccard, D)` only, all of which are
fixed before `δ`. It is `ShadedPlank.reduction_to_slab_atTypicalAngle` read at `ε = η/256` and
`ε' = η/2`, whose exponent gap `128ε ≤ ε'` is then an equality, with the items the transverse
branch does not read discarded. -/
theorem exists_isReductionFillAvailable (ω : Type*) {η : ℝ} (hη : 0 < η) (Ccard : NNReal)
    (D : ℝ) :
    ∃ δthr : NNReal, 0 < δthr ∧ δthr ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δthr → IsReductionFillAvailable ω η Ccard D δ := by
  have hεpos : 0 < η / 256 := by positivity
  have hε'pos : 0 < η / 2 := by positivity
  have hgap : 128 * (η / 256) ≤ η / 2 := le_of_eq (by ring)
  rcases ShadedPlank.reduction_to_slab_atTypicalAngle
      (η := η) (ε := η / 256) (ε' := η / 2) hη hεpos hε'pos hgap Ccard D with
    ⟨δthr, hδthrpos, hδthr1, hred⟩
  refine ⟨δthr, hδthrpos, hδthr1, ?_⟩
  intro δ hδpos hδle
  unfold IsReductionFillAvailable
  intro s a b hab hb1 Y θ hθ1 C Y'' hδpos0 hδa ha1 hwin hfull hmulti_a hmulti_δ h2 hcard h_ab
    h1leC hCle hcref hcm htyp hmaxAbsP
  have hred3 := hred (ι := ω) s (δ := δ) (a := a) (b := b) (hab := hab) (hb1 := hb1) Y θ hθ1 C Y''
      hδpos0 hδa ha1 hδle hwin hfull hmulti_a hmulti_δ h2 hcard h_ab h1leC hCle
      hcref hcm htyp hmaxAbsP
  rcases hred3 with ⟨s', Y', c1, hc1, href, href2, hfull', hitem1, hitem5⟩
  -- the output union is nonempty, from the fullness of the output and the input
  have hapos : 0 < a := lt_of_lt_of_le hδpos0 hδa
  have hfullpos : (0 : NNReal) < ShadedBody.fullness s' Y' := by
    have haeps : (0 : NNReal) < a ^ (η / 256) := NNReal.rpow_pos hapos
    have haeta : (0 : NNReal) < a ^ η := NNReal.rpow_pos hapos
    have hprod : (0 : NNReal) < c1 * (a ^ (η / 256)) * a ^ η :=
      mul_pos (mul_pos hc1 haeps) haeta
    have hle : c1 * (a ^ (η / 256)) * a ^ η ≤ ShadedBody.fullness s' Y' := by
      calc
        c1 * (a ^ (η / 256)) * a ^ η
            = (c1 * (a ^ (η / 256))) * a ^ η := by ring
        _ ≤ (c1 * (a ^ (η / 256))) * ShadedBody.fullness s (ShadedPlank.bodies Y) := by
                exact mul_le_mul_right hfull (c1 * (a ^ (η / 256)))
        _ ≤ ShadedBody.fullness s' Y' := hfull'
    exact lt_of_lt_of_le hprod hle
  have hfullE : (0 : ENNReal) < (ShadedBody.fullness s' Y' : ENNReal) :=
    ENNReal.coe_pos.mpr hfullpos
  have hsumne : (∑ i ∈ s', volume (Y' i).shade) ≠ 0 := by
    rw [ShadedBody.fullness_def s' Y'] at hfullE
    exact (ENNReal.div_pos_iff.mp hfullE).1
  have hneu : (ShadedBody.iUnionShade s' Y').Nonempty := by
    rcases Finset.exists_ne_zero_of_sum_ne_zero (s := s') (f := fun i => volume (Y' i).shade)
        hsumne with ⟨j, hj, hjne⟩
    have hvolj : (0 : ENNReal) < volume (Y' j).shade := pos_iff_ne_zero.mpr hjne
    have hjne' : volume (Y' j).shade ≠ 0 := ne_of_gt hvolj
    have hjNonempty : (Y' j).shade.Nonempty := MeasureTheory.nonempty_of_measure_ne_zero hjne'
    rcases hjNonempty with ⟨p, hp⟩
    exact ⟨p, Finset.subset_set_biUnion_of_mem (s := s') (f := fun i => (Y' i).shade) hj hp⟩
  refine ⟨s', Y', c1, hc1, href, href2, hneu, ?_, hitem5⟩
  intro x hx
  simpa using hitem1 x hx

end Kakeya.VeryNotSticky

end
