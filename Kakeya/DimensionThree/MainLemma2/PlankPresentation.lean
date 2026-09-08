/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody.Counting
public import Kakeya.GreedyIndependentSet
public import Kakeya.DimensionThree.MainLemma2.PlankRescaling
public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Slab.Multiplicity
public import Kakeya.DimensionThree.Volume

/-!
# The plank presentation: enclosure, selection and dimensions

This file records the statements that the plank presentation of the non-slab case (blueprint
`lem:ml2plankpresentation`, Lean `Kakeya.VeryNotSticky.plankPresentation`) is assembled from,
apart from the transport across the rescaling `L_B`, which is
`Kakeya.DimensionThree.MainLemma2.PlankRescaling`. Three groups:

* **The geometric core.** A rescaled factoring body is enclosed in a plank of *exact*
  half-widths `a' × b' × 1` that still fits inside the Section 6 window
  (`Kakeya.VeryNotSticky.plankWindowEnclosure`). Enclosure alone gives only the crude radius
  `1 + 2√3 ≈ 4.47 > 4`; recentring the box at the coordinate-extent midpoint of the body is
  what buys the window (`Kakeya.extentMidpoint`,
  `Kakeya.VeryNotSticky.plankRecentredWindow`).

* **The subfamily selection.** The enclosing planks are **not** pairwise essentially distinct,
  and no choice of them makes them so; what is true is that the failure is sparse. The
  clustering relation — two indices are clustered when their planks fail to be essentially
  distinct — has bounded degree (`Kakeya.VeryNotSticky.plankClusterBound`), and a greedy
  selection in a bounded-degree graph (`Kakeya.exists_pairwise_not_of_degree_le`) keeps a fixed
  fraction of any nonnegative weight. Together they give the subfamily
  (`Kakeya.VeryNotSticky.plankSubfamilySelection`,
  `Kakeya.VeryNotSticky.plankFamilyEnclosure`).

* **The bookkeeping.** The arithmetic fixing the dimensions (the
  `Kakeya.VeryNotSticky.plankDimensions_*` lemmas), the hypothesis package of the enclosure
  (the `Kakeya.VeryNotSticky.plankRescaledFamily_*` lemmas), the volume comparison
  (`Kakeya.VeryNotSticky.plankEnclosureVolume`), the density comparison
  (`Kakeya.VeryNotSticky.plankDensity`) and the multiplicity of the selected subfamily
  (`Kakeya.VeryNotSticky.plankSubfamilyMult`).

**On the two named constants.** The clustering dilation constant of blueprint
`lem:ml2plankClusterDilate` is obtained existentially, because the convex-geometry input it
rests on (`Kakeya.exists_essOverlapDilate_constant`) is itself accepted as an assumption with
an existential constant; but it is an *absolute* constant, so it is named once and for all as
`Kakeya.VeryNotSticky.clusterDilationConstant` rather than threaded through the statements as
a parameter. The selection factor `C^{sel}` of blueprint `def:ml2plankSelectionConstant` is
then the honest `D_{lem:ml2plankClusterBound}(C₀) + 1`
(`Kakeya.VeryNotSticky.plankSelectionConstant`), which is what
`Kakeya.VeryNotSticky.plankSubfamilySelection` can actually supply; the selection statements
carry it as a lower bound on a parameter `Csel`, any larger value serving.

All scales (`a`, `b`, `r₁`, `δ`, `C₀`, `a'`, `b'`) live in `ℝ≥0`, matching
`Kakeya.VeryNotSticky.plankPresentation` and `Kakeya.VeryNotSticky.VeryNotSticky`, so that the
assembly is not spent on coercions.
-/

@[expose] public section

open Finset MeasureTheory Metric Set ShadedBody
open scoped NNReal Pointwise Real

noncomputable section

/-- Shorthand for the ambient space of the non-slab case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

namespace Kakeya

/-! ### The coordinate extent of a set, and recentring a prism at its midpoint -/

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The largest value of the coordinate functional `x ↦ ⟨x, b i⟩` on `K`. For `K` nonempty and
compact the supremum is attained (`Kakeya.isGreatest_extentMax`); otherwise the value is
junk. -/
def extentMax (K : Set E) (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) : ℝ :=
  sSup ((fun x => b.repr x i) '' K)

/-- The smallest value of the coordinate functional `x ↦ ⟨x, b i⟩` on `K`. -/
def extentMin (K : Set E) (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) : ℝ :=
  sInf ((fun x => b.repr x i) '' K)

/-- **The coordinate-extent midpoint of `K` in the frame `b`**: the point whose `i`-th
coordinate is the midpoint of the extent of `K` in the direction `b i`. Recentring an
enclosing box at this point keeps it a superset of `K` and pulls it towards the origin, which
is what buys the Section 6 window in `Kakeya.VeryNotSticky.plankRecentredWindow`. -/
def extentMidpoint (K : Set E) (b : OrthonormalBasis (Fin n) ℝ E) : E :=
  ∑ i, ((extentMax K b i + extentMin K b i) / 2) • b i

variable {S : Type*} [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- **Recentre a prism**: the prism with the same orthonormal frame and the same half-widths,
about a new centre. -/
def _root_.PrismNDim.recentre (Q : PrismNDim n E S) (c : S) : PrismNDim n E S :=
  PrismNDim.mk' c Q.basis Q.thicknesses

/-- **The coordinate maximum is attained** (blueprint `lem:ml2plankExtentSpread`).

A continuous functional on a nonempty compact set attains its supremum
(`IsCompact.exists_isMaxOn`). -/
theorem isGreatest_extentMax {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    IsGreatest ((fun x => b.repr x i) '' K) (extentMax K b i) := by
  have hcont : Continuous (fun x : E => b.repr x i) := by
    fun_prop
  unfold extentMax
  refine IsCompact.isGreatest_sSup (s := (fun x : E => b.repr x i) '' K) ?_ ?_
  · exact hK.image hcont
  · exact hKne.image (fun x : E => b.repr x i)

/-- **The coordinate minimum is attained** (blueprint `lem:ml2plankExtentSpread`). -/
theorem isLeast_extentMin {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    IsLeast ((fun x => b.repr x i) '' K) (extentMin K b i) := by
  have hcont : Continuous (fun x : E => b.repr x i) := by
    fun_prop
  unfold extentMin
  refine IsCompact.isLeast_sInf (s := (fun x : E => b.repr x i) '' K) ?_ ?_
  · exact hK.image hcont
  · exact hKne.image (fun x : E => b.repr x i)

/-- **The coordinate extent is nondegenerate** (blueprint `lem:ml2plankExtentSpread`).

Both extrema are values of the functional at points of the nonempty set `K`. -/
theorem extentMin_le_extentMax {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (b : OrthonormalBasis (Fin n) ℝ E) (i : Fin n) :
    extentMin K b i ≤ extentMax K b i := by
  obtain ⟨x, hx⟩ := id hKne
  exact le_trans
    ((isLeast_extentMin hK hKne b i).2 ⟨x, hx, rfl⟩)
    ((isGreatest_extentMax hK hKne b i).2 ⟨x, hx, rfl⟩)

/-- **The coordinate extent of a set inside a prism is at most twice the half-width**
(blueprint `lem:ml2plankExtentSpread`). -/
theorem extent_spread {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (Q : PrismNDim n E E) (hKQ : K ⊆ (Q.carrier : Set E)) (i : Fin n) :
    extentMax K Q.basis i - extentMin K Q.basis i ≤ 2 * (Q.thicknesses i : ℝ) := by
  rcases (isGreatest_extentMax hK hKne Q.basis i).1 with ⟨xm, hxm, hxmax⟩
  rcases (isLeast_extentMin hK hKne Q.basis i).1 with ⟨xn, hxn, hxmin⟩
  have hmem : ∀ x : E, x ∈ K →
      |Q.basis.repr (x -ᵥ Q.center) i| ≤ (Q.thicknesses i : ℝ) := by
    intro x hx
    exact (Q.mem_carrier_iff x).1 (hKQ hx) i
  have hxm_coord : Q.basis.repr (xm -ᵥ Q.center) i
      = Q.basis.repr xm i - Q.basis.repr Q.center i := by
    calc
      Q.basis.repr (xm -ᵥ Q.center) i = Q.basis.repr (xm - Q.center) i := by simp [vsub_eq_sub]
      _ = Q.basis.repr xm i - Q.basis.repr Q.center i := by
        rw [map_sub (Q.basis.repr) xm Q.center]
        simp
  have hmax_le : extentMax K Q.basis i
      ≤ Q.basis.repr Q.center i + (Q.thicknesses i : ℝ) := by
    have habs : |Q.basis.repr xm i - Q.basis.repr Q.center i| ≤ (Q.thicknesses i : ℝ) := by
      simpa [hxm_coord] using hmem xm hxm
    rw [← hxmax]
    linarith [(abs_le.mp habs).2]
  have hxn_coord : Q.basis.repr (xn -ᵥ Q.center) i
      = Q.basis.repr xn i - Q.basis.repr Q.center i := by
    calc
      Q.basis.repr (xn -ᵥ Q.center) i = Q.basis.repr (xn - Q.center) i := by simp [vsub_eq_sub]
      _ = Q.basis.repr xn i - Q.basis.repr Q.center i := by
        rw [map_sub (Q.basis.repr) xn Q.center]
        simp
  have hmin_ge : Q.basis.repr Q.center i - (Q.thicknesses i : ℝ)
      ≤ extentMin K Q.basis i := by
    have habs : |Q.basis.repr xn i - Q.basis.repr Q.center i| ≤ (Q.thicknesses i : ℝ) := by
      simpa [hxn_coord] using hmem xn hxn
    rw [← hxmin]
    linarith [(abs_le.mp habs).1]
  linarith

/-- **Recentring a prism at the coordinate-extent midpoint** (blueprint
`lem:ml2plankExtentMidpoint`).

The recentred prism still contains `K`: in each direction the half-extent of `K` about the
extent midpoint is at most half the extent, hence at most the half-width. -/
theorem subset_recentre_extentMidpoint {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (Q : PrismNDim n E E) (hKQ : K ⊆ (Q.carrier : Set E)) :
    K ⊆ ((Q.recentre (extentMidpoint K Q.basis)).carrier : Set E) := by
  intro x hx
  let P : PrismNDim n E E :=
    PrismNDim.mk' (extentMidpoint K Q.basis) Q.basis Q.thicknesses
  change x ∈ (P : PrismNDim n E E).carrier
  refine (P.mem_carrier_iff x).mpr ?_
  intro i
  have hγ : Q.basis.repr (extentMidpoint K Q.basis) i
      = (extentMax K Q.basis i + extentMin K Q.basis i) / 2 := by
    rw [Q.basis.repr_apply_apply]
    unfold extentMidpoint
    rw [inner_sum]
    simp only [inner_smul_right]
    simp only [Q.basis.inner_eq_ite]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji.symm]
    · intro himem
      exact (himem (Finset.mem_univ i)).elim
  have hxmax : Q.basis.repr x i ≤ extentMax K Q.basis i :=
    (isGreatest_extentMax hK hKne Q.basis i).2 ⟨x, hx, rfl⟩
  have hxmin : extentMin K Q.basis i ≤ Q.basis.repr x i :=
    (isLeast_extentMin hK hKne Q.basis i).2 ⟨x, hx, rfl⟩
  have hspread : (extentMax K Q.basis i - extentMin K Q.basis i) / 2
      ≤ (Q.thicknesses i : ℝ) := by
    have h := extent_spread hK hKne Q hKQ i
    nlinarith
  have hcoord : Q.basis.repr (x -ᵥ extentMidpoint K Q.basis) i
      = Q.basis.repr x i - (extentMax K Q.basis i + extentMin K Q.basis i) / 2 := by
    calc
      Q.basis.repr (x -ᵥ extentMidpoint K Q.basis) i
          = Q.basis.repr (x - extentMidpoint K Q.basis) i := by simp [vsub_eq_sub]
      _ = Q.basis.repr x i - Q.basis.repr (extentMidpoint K Q.basis) i := by
            have hlin : Q.basis.repr (x - extentMidpoint K Q.basis)
                = Q.basis.repr x - Q.basis.repr (extentMidpoint K Q.basis) := by
              exact map_sub (Q.basis.repr) x (extentMidpoint K Q.basis)
            rw [hlin]
            simp
      _ = Q.basis.repr x i - (extentMax K Q.basis i + extentMin K Q.basis i) / 2 := by
            rw [hγ]
  change |Q.basis.repr (x -ᵥ extentMidpoint K Q.basis) i| ≤ (Q.thicknesses i : ℝ)
  rw [hcoord]
  have hmid : |Q.basis.repr x i - (extentMax K Q.basis i + extentMin K Q.basis i) / 2|
      ≤ (extentMax K Q.basis i - extentMin K Q.basis i) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hxmin, hxmax]
  exact hmid.trans hspread

/-- **A set of bounded coordinate spread lies in the box of half-widths `w` centred at its
extent midpoint** (blueprint `lem:ml2plankExtentMidpoint`, prescribed-frame form).

The companion of `Kakeya.subset_recentre_extentMidpoint` for a *prescribed* frame `b`. There an
enclosing box is given and is recentred; here only the coordinate spread of `K` in the frame is
known, and the box is produced. This is the form the prescribed-frame plank enclosure needs:
the frame handed to `Kakeya.VeryNotSticky.plankWindowEnclosure` is the frame of a *different*
body carried across a homothety, so no enclosing box on it is available beforehand. -/
theorem subset_extentMidpoint_prism_of_spread {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (b : OrthonormalBasis (Fin n) ℝ E) (w : Fin n → NNReal)
    (hspread : ∀ x ∈ K, ∀ y ∈ K, ∀ i, |b.repr (x - y) i| ≤ 2 * (w i : ℝ)) :
    K ⊆ ((PrismNDim.mk' (extentMidpoint K b) b w : PrismNDim n E E).carrier : Set E) := by
  have hsp : ∀ i, extentMax K b i - extentMin K b i ≤ 2 * (w i : ℝ) := by
    intro i
    rcases (isGreatest_extentMax hK hKne b i).1 with ⟨xm, hxm, hxmax⟩
    rcases (isLeast_extentMin hK hKne b i).1 with ⟨xn, hxn, hxmin⟩
    have habs : |b.repr (xm - xn) i| ≤ 2 * (w i : ℝ) := hspread xm hxm xn hxn i
    calc
      extentMax K b i - extentMin K b i = b.repr xm i - b.repr xn i := by
        rw [← hxmax, ← hxmin]
      _ = b.repr (xm - xn) i := by
        rw [map_sub (b.repr) xm xn]
        simp
      _ ≤ |b.repr (xm - xn) i| := le_abs_self _
      _ ≤ 2 * (w i : ℝ) := habs
  intro x hx
  let P : PrismNDim n E E :=
    PrismNDim.mk' (extentMidpoint K b) b w
  change x ∈ (P : PrismNDim n E E).carrier
  refine (P.mem_carrier_iff x).mpr ?_
  intro i
  have hγ : b.repr (extentMidpoint K b) i
      = (extentMax K b i + extentMin K b i) / 2 := by
    rw [b.repr_apply_apply]
    unfold extentMidpoint
    rw [inner_sum]
    simp only [inner_smul_right]
    simp only [b.inner_eq_ite]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji.symm]
    · intro himem
      exact (himem (Finset.mem_univ i)).elim
  have hxmax : b.repr x i ≤ extentMax K b i :=
    (isGreatest_extentMax hK hKne b i).2 ⟨x, hx, rfl⟩
  have hxmin : extentMin K b i ≤ b.repr x i :=
    (isLeast_extentMin hK hKne b i).2 ⟨x, hx, rfl⟩
  have hspread' : (extentMax K b i - extentMin K b i) / 2
      ≤ (w i : ℝ) := by
    have h := hsp i
    nlinarith
  have hcoord : b.repr (x -ᵥ extentMidpoint K b) i
      = b.repr x i - (extentMax K b i + extentMin K b i) / 2 := by
    calc
      b.repr (x -ᵥ extentMidpoint K b) i
          = b.repr (x - extentMidpoint K b) i := by simp [vsub_eq_sub]
      _ = b.repr x i - b.repr (extentMidpoint K b) i := by
            have hlin : b.repr (x - extentMidpoint K b)
                = b.repr x - b.repr (extentMidpoint K b) := by
              exact map_sub (b.repr) x (extentMidpoint K b)
            rw [hlin]
            simp
      _ = b.repr x i - (extentMax K b i + extentMin K b i) / 2 := by
            rw [hγ]
  change |b.repr (x -ᵥ extentMidpoint K b) i| ≤ (w i : ℝ)
  rw [hcoord]
  have hmid : |b.repr x i - (extentMax K b i + extentMin K b i) / 2|
      ≤ (extentMax K b i - extentMin K b i) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hxmin, hxmax]
  exact hmid.trans hspread'

/-- **Each coordinate of the extent midpoint of a set in the unit ball is at most `1`**
(blueprint `lem:ml2plankExtentCentreBound`).

Cauchy–Schwarz applied to a unit frame vector. -/
theorem abs_extentMidpoint_coord_le {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (b : OrthonormalBasis (Fin n) ℝ E) (hK1 : K ⊆ closedBall (0 : E) 1) (i : Fin n) :
    |(extentMax K b i + extentMin K b i) / 2| ≤ 1 := by
  have hcoord : ∀ x ∈ K, |b.repr x i| ≤ 1 := by
    intro x hx
    calc
      |b.repr x i| ≤ ‖b i‖ * ‖x‖ := by
        rw [b.repr_apply_apply]
        exact abs_real_inner_le_norm (b i) x
      _ = ‖x‖ := by simp [b.norm_eq_one]
      _ ≤ 1 := by
        exact mem_closedBall_zero_iff.mp (hK1 hx)
  have hmax : |extentMax K b i| ≤ 1 := by
    rcases (isGreatest_extentMax hK hKne b i).1 with ⟨x, hx, hxmax⟩
    simpa [← hxmax] using hcoord x hx
  have hmin : |extentMin K b i| ≤ 1 := by
    rcases (isLeast_extentMin hK hKne b i).1 with ⟨x, hx, hxmin⟩
    simpa [← hxmin] using hcoord x hx
  rw [abs_le]
  constructor
  · have h1 := (abs_le.mp hmax).1
    have h2 := (abs_le.mp hmin).1
    nlinarith
  · have h1 := (abs_le.mp hmax).2
    have h2 := (abs_le.mp hmin).2
    nlinarith

/-- **The extent midpoint of a set in the unit ball has norm at most `√n`** (blueprint
`lem:ml2plankExtentCentreBound`).

Parseval applied to `Kakeya.abs_extentMidpoint_coord_le`. -/
theorem norm_extentMidpoint_le {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (b : OrthonormalBasis (Fin n) ℝ E) (hK1 : K ⊆ closedBall (0 : E) 1) :
    ‖extentMidpoint K b‖ ≤ Real.sqrt n := by
  have hcoord_sq : ∀ i : Fin n, (inner ℝ (b i) (extentMidpoint K b) : ℝ) ^ 2 ≤ 1 := by
    intro i
    have hcoord : inner ℝ (b i) (extentMidpoint K b) = (extentMax K b i + extentMin K b i) / 2 := by
      unfold extentMidpoint
      rw [inner_sum]
      simp only [inner_smul_right]
      simp only [b.inner_eq_ite]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [hji.symm]
      · intro himem
        exact (himem (Finset.mem_univ i)).elim
    have habs := abs_extentMidpoint_coord_le hK hKne b hK1 i
    have hcabs : |inner ℝ (b i) (extentMidpoint K b)| ≤ 1 := by
      simpa [hcoord] using habs
    rcases abs_le.mp hcabs with ⟨hl, hu⟩
    nlinarith
  have hsq : ‖extentMidpoint K b‖ ^ 2 ≤ (n : ℝ) := by
    calc
      ‖extentMidpoint K b‖ ^ 2 = ∑ i : Fin n, (inner ℝ (b i) (extentMidpoint K b) : ℝ) ^ 2 := by
        rw [← b.sum_sq_inner_right]
      _ ≤ ∑ i : Fin n, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun i _ => hcoord_sq i)
      _ = (n : ℝ) := by
        simp
  exact (Real.le_sqrt (norm_nonneg _) (by exact_mod_cast Nat.zero_le n)).2 hsq

end Kakeya

namespace Kakeya.VeryNotSticky

open Kakeya

/-! ### The localization radius -/

/-- **The localization radius of the plank presentation** (blueprint
`def:ml2plankBallRadius`, `R_{lem:ml2plankpresentation}`).

The planks produced by `Kakeya.VeryNotSticky.plankPresentation` are *not* contained in the
closed unit ball, and asking for that in the conclusion would make the lemma false. The
rescaled body `L_B(W)` does lie in `B̄(0,1)`, because `W ⊆ B̄(ctr, r₁)` by (C4); but the plank
is a *superset* of `L_B(W)`, obtained by enclosing it in an exact `a' × b' × 1` box, and it
may stick out of the unit ball.

**The radius is the Section 6 window, and this is forced.** The one consumer of the
localization clause that is not internal to the non-slab files is
`ShadedPlank.reduction_to_slab` (GWZ Lemma 6.13), whose hypothesis `Plank.IsWindowedFamily`
asks the planks to lie in `B̄(0, Plank.windowRadius)` with `Plank.windowRadius = 4`. A
localization at any *larger* radius would not discharge it, so the definition below is
`Plank.windowRadius` itself rather than an independently chosen constant, and the localization
clause of `plankPresentation` is stated as `Plank.IsWindowedFamily` directly.

**Why radius `4` is reachable.** `Prism3D.exists_superset_of_hasThicknesses` returns the box
of half-widths `(a', b', 1)` centred at `Metric.outerPrism.center`, about which nothing better
than `|c| ≤ 1 + √3` is known, giving only the crude bound `1 + 2√3 ≈ 4.47`. The enclosing
plank is however not unique, and the conclusion is existential: recentring it, in the same
orthonormal frame, at the midpoint `c` of the extent of `L_B(W)` still gives a box of
half-widths `(a', b', 1)` containing `L_B(W)`, and `‖c‖ ≤ √3` while the recentred box lies in
`B̄(c, √3)`. Hence it lies in `B̄(0, 2√3)`, and `2√3 < 4`; this is
`Kakeya.VeryNotSticky.plankRecentredWindow`.

Nothing downstream is weakened by the enlargement from the unit ball.
`Kakeya.VeryNotSticky.plankCard` is stated at this radius and gets its cover from
`Kakeya.exists_finite_test_family_maxDensity_closedBall`, the general-radius form of the
discretization, whose cardinality bound is `C R^M r^{-M}`: a fixed radius `R = 4` changes the
constant `Kakeya.VeryNotSticky.plankCardConstant` by the fixed factor `4^M` and leaves the
exponent `Kakeya.VeryNotSticky.plankCardExponent` untouched. -/
noncomputable def plankBallRadius : NNReal :=
  ⟨Plank.windowRadius, by rw [Plank.windowRadius]; positivity⟩

/-! ### Enclosing a rescaled body in a windowed plank -/

/-- **A prism recentred at the extent midpoint has radius at most `2√3`** (blueprint
`lem:ml2plankRecentredWindow`).

The extent midpoint `c` of `K ⊆ B̄(0,1)` has `‖c‖ ≤ √3` by `Kakeya.norm_extentMidpoint_le`,
and a prism of half-widths at most `1` lies in `B̄(c, √3)` by the *Euclidean* radius bound
`PrismNDim.carrier_subset_closedBall_euclidean`. The `ℓ¹` bound
`PrismNDim.carrier_subset_closedBall` would give only `3 + √3 > 4`. -/
theorem recentre_extentMidpoint_subset_closedBall {K : Set E₃} (hK : IsCompact K)
    (hKne : K.Nonempty) (hK1 : K ⊆ closedBall (0 : E₃) 1) (Q : PrismNDim 3 E₃ E₃)
    (hw : ∀ i, (Q.thicknesses i : ℝ) ≤ 1) (_hKQ : K ⊆ (Q.carrier : Set E₃)) :
    ((Q.recentre (extentMidpoint K Q.basis)).carrier : Set E₃) ⊆
      closedBall (0 : E₃) (2 * Real.sqrt 3) := by
  intro x hx
  let c : E₃ := extentMidpoint K Q.basis
  let P : PrismNDim 3 E₃ E₃ := Q.recentre c
  have hcP : P.center = c := by
    simpa [P, PrismNDim.recentre] using
      (PrismNDim.center_mk' c Q.basis Q.thicknesses :
        (PrismNDim.mk' c Q.basis Q.thicknesses).center = c)
  have hthickP : P.thicknesses = Q.thicknesses := by
    simpa [P, PrismNDim.recentre] using
      (PrismNDim.thicknesses_mk' c Q.basis Q.thicknesses :
        (PrismNDim.mk' c Q.basis Q.thicknesses).thicknesses = Q.thicknesses)
  have hsq : ∀ i : Fin 3, (Q.thicknesses i : ℝ) ^ 2 ≤ 1 := by
    intro i
    have hw0 : 0 ≤ (Q.thicknesses i : ℝ) := NNReal.coe_nonneg _
    have hp : (Q.thicknesses i : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ hw0 (hw i) 2
    simpa using hp
  have hsum : (∑ i : Fin 3, (Q.thicknesses i : ℝ) ^ 2) ≤ 3 := by
    calc
      (∑ i : Fin 3, (Q.thicknesses i : ℝ) ^ 2) ≤ ∑ _ : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hsq i)
      _ = 3 := by simp
  have hPeuc : (P.carrier : Set E₃) ⊆
      closedBall c (Real.sqrt (∑ i : Fin 3, (Q.thicknesses i : ℝ) ^ 2)) := by
    simpa [hthickP, hcP] using
      (P.carrier_subset_closedBall_euclidean : (P.carrier : Set E₃) ⊆
        closedBall P.center (Real.sqrt (∑ i : Fin 3, (P.thicknesses i : ℝ) ^ 2)))
  have hnormc : ‖c‖ ≤ Real.sqrt 3 := by
    simpa [c] using
      (norm_extentMidpoint_le hK hKne Q.basis hK1 :
        ‖extentMidpoint K Q.basis‖ ≤ Real.sqrt 3)
  have hxc : dist x c ≤ Real.sqrt 3 := by
    calc
      dist x c ≤ Real.sqrt (∑ i : Fin 3, (Q.thicknesses i : ℝ) ^ 2) := mem_closedBall.mp (hPeuc hx)
      _ ≤ Real.sqrt 3 := by
        exact Real.sqrt_le_sqrt hsum
  have hdist_c0 : dist c 0 ≤ Real.sqrt 3 := by
    rwa [dist_eq_norm, sub_zero]
  have hx0 : dist x 0 ≤ 2 * Real.sqrt 3 := by
    calc
      dist x 0 ≤ dist x c + dist c 0 := dist_triangle x c 0
      _ ≤ Real.sqrt 3 + Real.sqrt 3 := add_le_add hxc hdist_c0
      _ = 2 * Real.sqrt 3 := by ring
  rw [Metric.mem_closedBall]
  exact hx0

/-- **A prism recentred at the extent midpoint fits in the plank window** (blueprint
`lem:ml2plankRecentredWindow`).

This is the step that buys the window, and it is the only reason the enclosing box is
recentred at all: `2√3 < 4 = plankBallRadius`, by
`Kakeya.VeryNotSticky.recentre_extentMidpoint_subset_closedBall`. That the recentred prism
still contains `K` is `Kakeya.subset_recentre_extentMidpoint`. -/
theorem plankRecentredWindow {K : Set E₃} (hK : IsCompact K) (hKne : K.Nonempty)
    (hK1 : K ⊆ closedBall (0 : E₃) 1) (Q : PrismNDim 3 E₃ E₃)
    (hw : ∀ i, (Q.thicknesses i : ℝ) ≤ 1) (hKQ : K ⊆ (Q.carrier : Set E₃)) :
    ((Q.recentre (extentMidpoint K Q.basis)).carrier : Set E₃) ⊆
      closedBall (0 : E₃) (plankBallRadius : ℝ) := by
  have hsub : ((Q.recentre (extentMidpoint K Q.basis)).carrier : Set E₃) ⊆
      closedBall (0 : E₃) (2 * Real.sqrt 3) :=
    recentre_extentMidpoint_subset_closedBall hK hKne hK1 Q hw hKQ
  have hlt : Real.sqrt 3 < 2 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).mpr (by norm_num : (3 : ℝ) < 2 ^ 2)
  have hle : 2 * Real.sqrt 3 ≤ (plankBallRadius : ℝ) := by
    change 2 * Real.sqrt 3 ≤ Plank.windowRadius
    rw [Plank.windowRadius]
    nlinarith
  exact hsub.trans (closedBall_subset_closedBall hle)

/-- **Renormalising the long entry of a thickness triple** (blueprint
`lem:ml2plankModifiedTriple`).

A bounded `K ⊆ B̄(0,1)` whose affine thicknesses are comparable, with constant `C₀`, to
`(1, t₁, t₂)` is also comparable, with the same constant, to `(C₀⁻¹, t₁, t₂)`.

The point of the renormalisation is that `Prism3D.exists_superset_of_hasThicknesses` asks for
`C₀ t₀ ≤ c'` on the long axis, which `t₀ = 1` does not satisfy at `c' = 1` when `C₀ > 1`,
whereas `t₀ = C₀⁻¹` does, with equality. -/
theorem hasThicknesses_modifiedTriple {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {t₁ t₂ : ℝ}
    (_ht₁ : 0 ≤ t₁) (_ht₂ : 0 ≤ t₂) {K : Set E₃} (hK : Bornology.IsBounded K)
    (hK1 : K ⊆ closedBall (0 : E₃) 1) (h : HasThicknesses K C₀ ![1, t₁, t₂]) :
    HasThicknesses K C₀ ![(C₀ : ℝ)⁻¹, t₁, t₂] := by
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le zero_lt_one hC₀'
  intro k
  fin_cases k
  · constructor
    · -- lower bound at rank 0
      have hle1 : (C₀ : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hC₀pos).mpr hC₀'
      have hmul : (C₀ : ℝ)⁻¹ * (C₀ : ℝ)⁻¹ ≤ (C₀ : ℝ)⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hle1 (inv_nonneg.mpr (le_of_lt hC₀pos))
      calc
        (C₀ : ℝ)⁻¹ * (C₀ : ℝ)⁻¹ ≤ (C₀ : ℝ)⁻¹ * 1 := hmul
        _ = (C₀ : ℝ)⁻¹ := by ring
        _ ≤ Metric.thickness ℝ K 0 := by simpa using (h 0).1
    · -- upper bound at rank 0
      have hE : ENNReal.ofReal (Metric.thickness ℝ K 0) ≤ (1 : ENNReal) := by
        rw [← Metric.ethickness_thickness' hK 0]
        exact Metric.ethickness_le_of_subset_closedBall (1 : NNReal) hK1 0
      have h1 : Metric.thickness ℝ K 0 ≤ 1 := by
        have hnn : 0 ≤ (1 : ℝ) := by norm_num
        apply (ENNReal.ofReal_le_ofReal_iff hnn).mp
        simpa using hE
      calc
        Metric.thickness ℝ K 0 ≤ 1 := h1
        _ = (C₀ : ℝ) * (C₀ : ℝ)⁻¹ := by rw [mul_inv_cancel₀ (ne_of_gt hC₀pos)]
  · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using (h 1)
  · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using (h 2)

/-- **Admissible plank dimensions** for the scales `(a, b, r₁)` and the comparison constant
`C₀`.

A pair `(a', b')` of half-widths is admissible when it makes an `a' × b' × 1` prism a `Plank`
(`0 < a' ≤ b' ≤ 1`) and dominates the transported thicknesses `(a/r₁, b/r₁)` of a rescaled
factoring body by the factor `C₀` of (C4). These five clauses are what the enclosing step
`Kakeya.VeryNotSticky.plankWindowEnclosure` consumes and nothing else, and they always travel
together; the presentation instantiates them at `a' = C₀ a / r₁`, `b' = C₀ b / r₁`, where the
last two hold with equality (blueprint `lem:ml2plankDimensions`). -/
structure IsAdmissiblePlankDimensions (C₀ a b r₁ a' b' : NNReal) : Prop where
  /-- the short half-width is positive, so the plank has positive volume -/
  short_pos : 0 < a'
  /-- the half-widths are ordered, as the type `Plank` demands -/
  short_le_long : a' ≤ b'
  /-- the middle half-width does not exceed the long one, which is `1` -/
  long_le_one : b' ≤ 1
  /-- the short half-width dominates the short transported thickness, with the factor `C₀` -/
  le_short : C₀ * (a / r₁) ≤ a'
  /-- the middle half-width dominates the middle transported thickness, with the factor `C₀` -/
  le_long : C₀ * (b / r₁) ≤ b'

/-- **Enclosing a rescaled body in a windowed plank, on a prescribed frame** (blueprint
`lem:ml2plankWindowEnclosure`).

This is the geometric core of the presentation. Two things are the point: the containment in
the *window*, and the identification of the plank's frame.

*The window.* An enclosing box of exact half-widths `(a', b', 1)` need not lie in
`B̄(0, plankBallRadius)`; centred at the centre of the outer prism of `K`, about which nothing
better than `‖c‖ ≤ 1 + √3` is known, one gets only the useless `1 + 2√3 ≈ 4.47 > 4`. The
enclosing box is however not unique and the conclusion is existential: centring it at the
coordinate-extent midpoint of `K` (`Kakeya.VeryNotSticky.plankRecentredWindow`) keeps it a
superset and buys the window.

*The frame.* The frame `e` is **prescribed by the caller** and returned in the conclusion,
`P.basis = e`. This is what the earlier version could not do, and what the whole tangential
chain turns on: that version built its box on `Metric.outerPrism.basis` of `K`, a frame
obtained by choice as a cluster point in `Metric.outerPrism.exists_limit`, which is therefore
not nameable downstream, is not equivariant under the rescaling `L_B`, and is not even rigid
for a body two of whose affine thicknesses are comparable. Consequently no consumer could
relate `P.basis 0` to the normal `Kakeya.NonSlab.bodyNormal` of the body being enclosed, and
`Kakeya.VeryNotSticky.TypicalAngleData.hangle` — the only form in which
`Kakeya.VeryNotSticky.tangentialSlabFibreCount` uses typicality — was unreachable. Since `L_B`
is a homothety and does not rotate, the caller may hand over the frame of the *unrescaled*
body, and the identification is then exact and lossless.

Accordingly the hypothesis on `K` is no longer `Kakeya.HasThicknesses` but the coordinate
spread of `K` in the prescribed frame, in the two short directions; the long direction needs
no hypothesis, `K ⊆ B̄(0,1)` bounding its spread by `2` already. The scales `a`, `b`, `r₁`,
`C₀` survive only inside `Kakeya.VeryNotSticky.IsAdmissiblePlankDimensions`, which is what
fixes the type of the plank; its positivity clause `0 < a'` is not used here, being carried for
`Kakeya.VeryNotSticky.plankFamilyEnclosure`, whose selection step needs the planks to have
positive volume. -/
theorem plankWindowEnclosure {C₀ a b r₁ : NNReal} (_hC₀ : 1 ≤ C₀) (_hr₁ : 0 < r₁) (_hab : a ≤ b)
    {a' b' : NNReal} (hdim : IsAdmissiblePlankDimensions C₀ a b r₁ a' b')
    {K : Set E₃} (hK : IsCompact K) (hKne : K.Nonempty) (hK1 : K ⊆ closedBall (0 : E₃) 1)
    (e : OrthonormalBasis (Fin 3) ℝ E₃)
    (hspread : ∀ x ∈ K, ∀ u ∈ K,
      |e.repr (x - u) 0| ≤ 2 * (a' : ℝ) ∧ |e.repr (x - u) 1| ≤ 2 * (b' : ℝ)) :
    ∃ P : Plank a' b' hdim.short_le_long hdim.long_le_one, K ⊆ (P.carrier : Set E₃) ∧
      (P.carrier : Set E₃) ⊆ closedBall (0 : E₃) (plankBallRadius : ℝ) ∧ P.basis = e := by
  classical
  set c : E₃ := Kakeya.extentMidpoint K e with hc
  set Q : PrismNDim 3 E₃ E₃ := PrismNDim.mk' c e ![a', b', (1 : NNReal)] with hQ
  have hQb : Q.basis = e := PrismNDim.basis_mk' _ _ _
  have hQc : Q.center = c := PrismNDim.center_mk' _ _ _
  have hQt : Q.thicknesses = ![a', b', (1 : NNReal)] := PrismNDim.thicknesses_mk' _ _ _
  -- (1) K ⊆ Q
  have hKQ : K ⊆ (Q.carrier : Set E₃) := by
    rw [hQ]
    exact subset_extentMidpoint_prism_of_spread hK hKne e ![a', b', (1 : NNReal)] (by
      intro x hx y hy i
      fin_cases i
      · exact (hspread x hx y hy).1
      · exact (hspread x hx y hy).2
      · have hcoord : |e.repr (x - y) 2| ≤ 2 := by
          calc
            |e.repr (x - y) 2| ≤ ‖e 2‖ * ‖x - y‖ := by
              rw [e.repr_apply_apply]
              exact abs_real_inner_le_norm (e 2) (x - y)
            _ = ‖x - y‖ := by simp [e.norm_eq_one]
            _ ≤ 2 := by
              have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hK1 hx)
              have hynorm : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp (hK1 hy)
              have hnormadd : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
              linarith
        simpa using hcoord)
  -- (2) half-widths at most one
  have hw : ∀ i, (Q.thicknesses i : ℝ) ≤ 1 := by
    intro i
    rw [hQt]
    fin_cases i
    · exact_mod_cast hdim.short_le_long.trans hdim.long_le_one
    · exact_mod_cast hdim.long_le_one
    · norm_num
  -- (3) window
  have hwin : (Q.carrier : Set E₃) ⊆ closedBall (0 : E₃) (plankBallRadius : ℝ) := by
    have hsub : ((Q.recentre (extentMidpoint K Q.basis)).carrier : Set E₃) ⊆
        closedBall (0 : E₃) (plankBallRadius : ℝ) :=
      plankRecentredWindow hK hKne hK1 Q hw hKQ
    have hrecentre : Q.recentre (extentMidpoint K Q.basis) = Q := by
      dsimp [PrismNDim.recentre]
      rw [hQb, hQt, hQ]
    rwa [hrecentre] at hsub
  exact ⟨Prism3D.mk Q hQt, hKQ, hwin, hQb⟩

/-! ### Bounded clustering and the selection of an essentially distinct subfamily -/

/-- **The clustering relation has bounded degree** (blueprint `lem:ml2plankClusterBound`,
`D_{lem:ml2plankClusterBound}(C₀)`).

All the planks of the family have the common volume `8 a' b' > 0`, so clustered planks lie in
the single dilate `C^{cl} · P i`, inside which the bodies `K j` — pairwise essentially
distinct, of volume at least `|P| / C_{lem:ml2plankpresentation}(C₀)` — are counted by
`Kakeya.card_le_of_pairwise_essDistinct_in_prism`.

The bound depends on `C₀`, on `Kakeya.VeryNotSticky.clusterDilationConstant` and on the
ambient dimension alone: not on `δ`, not on the exponent parameters, not on the ball `B`, not
on the dimensions `a'`, `b'` and not on the family.

Note what is *not* claimed. Bounded degree is a statement about pairs, and it does not say
that a fixed point of `ℝ³` lies in boundedly many of the planks: many sets can be pairwise
half-disjoint while sharing a common point. The selection below is therefore run on the
clustering *graph* and not on a pointwise multiplicity bound. -/
theorem plankClusterBound {C₀ : NNReal} (_hC₀ : 1 ≤ C₀)
    {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    {ι : Type*} (s : Finset ι) (P : ι → Plank a' b' hab' hb1') (K : ι → ConvexSpaceBody E₃)
    (hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier)
    (hKvol : ∀ j ∈ s, 8 * (a' : ENNReal) * b'
      ≤ (plankEnclosureConstant C₀ : ENNReal) * volume ((K j).carrier : Set E₃))
    (hed : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct ((K i).carrier : Set E₃) ((K j).carrier : Set E₃)) :
    ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
          ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)}.ncard
        ≤ cardEssDistinctConvexInPrismConstant 3
            (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) := by
  classical
  let cl : NNReal := clusterDilationConstant
  have hcl : IsClusterDilationConstant cl := isClusterDilationConstant_clusterDilationConstant
  have hcl1 : (1 : NNReal) ≤ cl := hcl.one_le
  have hcl1' : (1 : ℝ) ≤ (cl : ℝ) := by exact_mod_cast hcl1
  have hclpos : (0 : NNReal) < cl := lt_of_lt_of_le zero_lt_one hcl1
  have hclpos' : (0 : ℝ) < (cl : ℝ) := by exact_mod_cast hclpos
  have hcl3pos : (0 : ℝ) < (cl : ℝ) ^ 3 := by positivity
  have hcl2ge0 : (0 : ℝ) ≤ (cl : ℝ) ^ 2 := by positivity
  have hcl2one : (1 : ℝ) ≤ (cl : ℝ) ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (cl : ℝ) * (cl : ℝ) := mul_le_mul hcl1' hcl1' (by norm_num) (le_of_lt hclpos')
      _ = (cl : ℝ) ^ 2 := by ring
  have hcl3one : (1 : ℝ) ≤ (cl : ℝ) ^ 3 := by
    calc
      (1 : ℝ) ≤ (cl : ℝ) ^ 2 := hcl2one
      _ = (cl : ℝ) ^ 2 * 1 := by rw [mul_one]
      _ ≤ (cl : ℝ) ^ 2 * (cl : ℝ) := mul_le_mul_of_nonneg_left hcl1' hcl2ge0
      _ = (cl : ℝ) ^ 3 := by ring
  let pe : NNReal := plankEnclosureConstant C₀
  have hpe1 : (1 : NNReal) ≤ pe := one_le_plankEnclosureConstant C₀
  have hpe1' : (1 : ℝ) ≤ (pe : ℝ) := by exact_mod_cast hpe1
  have hpepos' : (0 : ℝ) < (pe : ℝ) := lt_of_lt_of_le zero_lt_one hpe1'
  have hpepos : (0 : NNReal) < pe := lt_of_lt_of_le zero_lt_one hpe1
  let α : ℝ := ((cl : ℝ) ^ 3 * (pe : ℝ))⁻¹
  have hprodpos : (0 : ℝ) < (cl : ℝ) ^ 3 * (pe : ℝ) := by positivity
  have hprod1 : (1 : ℝ) ≤ (cl : ℝ) ^ 3 * (pe : ℝ) := by
    simpa using (mul_le_mul hcl3one hpe1' (by norm_num) (le_of_lt hcl3pos))
  have hαpos : 0 < α := by
    dsimp [α]
    exact inv_pos.mpr hprodpos
  have hα1 : α ≤ 1 := by
    dsimp [α]
    exact (inv_le_one₀ hprodpos).mpr hprod1
  have hαreal : α * (cl : ℝ) ^ 3 = (pe : ℝ)⁻¹ := by
    dsimp [α]
    have hcl3_ne0 : (cl : ℝ) ^ 3 ≠ 0 := by positivity
    rw [mul_comm, mul_inv, ← mul_assoc, mul_inv_cancel₀ hcl3_ne0, one_mul]
  have hclEN : (cl : ENNReal) = ENNReal.ofReal (cl : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have hpeEN : (pe : ENNReal) = ENNReal.ofReal (pe : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
  have hαcl : ENNReal.ofReal α * (cl : ENNReal) ^ 3 = (pe : ENNReal)⁻¹ := by
    rw [hclEN, ← ENNReal.ofReal_pow (by exact_mod_cast (le_of_lt hclpos'))]
    rw [← ENNReal.ofReal_mul (le_of_lt hαpos)]
    rw [hαreal]
    rw [hpeEN]
    exact ENNReal.ofReal_inv_of_pos hpepos'
  have hpe_nz : (pe : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hpepos)
  have hpe_top : (pe : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdivEN : ∀ j ∈ s, (8 * (a' : ENNReal) * b') / (pe : ENNReal) ≤
      volume ((K j).carrier : Set E₃) := by
    intro j hjS
    rw [ENNReal.div_le_iff hpe_nz hpe_top]
    rw [mul_comm (volume ((K j).carrier : Set E₃)) (pe : ENNReal)]
    exact hKvol j hjS
  intro i hi
  let J : Finset ι := s.filter (fun j => j ≠ i ∧
    ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃))
  have hJdef : ∀ j, j ∈ J ↔ j ∈ s ∧ j ≠ i ∧
      ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃) := by
    intro j
    simp [J]
  have hJs : ∀ j, j ∈ (J : Set ι) → j ∈ (s : Set ι) := fun j hjJ =>
    Finset.mem_coe.mpr (((hJdef j).mp (Finset.mem_coe.mp hjJ)).1)
  let R : PrismNDim 3 E₃ E₃ := (P i).toPrismNDim.dilation cl
  have hsubset_dilation : ∀ j ∈ J, ((P j).carrier : Set E₃) ⊆ (R.carrier : Set E₃) := by
    intro j hjJ
    have hnot : ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃) :=
      ((hJdef j).mp hjJ).2.2
    have hvolEQ : volume ((P j).carrier : Set E₃) = volume ((P i).carrier : Set E₃) := by
      simp [Prism3D.volume_carrier (P j), Prism3D.volume_carrier (P i)]
    have hvolpos : 0 < volume ((P i).carrier : Set E₃) := by
      simpa using (Prism3D.volume_pos_of_pos (P i) ha')
    have hsub :=
      hcl.subset_dilation ((P i).toPrismNDim) ((P j).toPrismNDim) hvolEQ.symm hvolpos hnot
    simpa [R] using hsub
  have hKR : ∀ j ∈ J, ((K j).carrier : Set E₃) ⊆ (R.carrier : Set E₃) := by
    intro j hjJ
    exact (hKP j ((hJdef j).mp hjJ).1).trans (hsubset_dilation j hjJ)
  have hvolR : volume (R.carrier : Set E₃) =
      (cl : ENNReal) ^ 3 * (8 * (a' : ENNReal) * b') := by
    have hfin : Module.finrank ℝ E₃ = 3 := by norm_num
    have hRth : ∀ j : Fin 3, (R.thicknesses j : ENNReal) =
        (cl : ENNReal) * ((P i).toPrismNDim.thicknesses j : ENNReal) := by
      intro j
      simp [R, PrismNDim.dilation, PrismNDim.thicknesses_mk']
    have hprod : (∏ k : Fin 3, (R.thicknesses k : ENNReal)) =
        (cl : ENNReal) ^ 3 * ∏ k, (((P i).toPrismNDim.thicknesses k) : ENNReal) := by
      simp_rw [hRth]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp
    calc
      volume (R.carrier : Set E₃) = 2 ^ Module.finrank ℝ E₃ * ∏ k, (R.thicknesses k : ENNReal) := by
        rw [PrismNDim.volume_carrier]
      _ = 2 ^ 3 * ∏ k, (R.thicknesses k : ENNReal) := by rw [hfin]
      _ = 2 ^ 3 * ((cl : ENNReal) ^ 3 * ∏ k, ((P i).toPrismNDim.thicknesses k : ENNReal)) := by
        rw [hprod]
      _ = (cl : ENNReal) ^ 3 * (2 ^ 3 * ∏ k, ((P i).toPrismNDim.thicknesses k : ENNReal)) := by
        apply mul_left_comm
      _ = (cl : ENNReal) ^ 3 * volume ((P i).toPrismNDim.carrier : Set E₃) := by
        congr 1
        rw [PrismNDim.volume_carrier]
        rw [hfin]
      _ = (cl : ENNReal) ^ 3 * (8 * (a' : ENNReal) * b') := by
        rw [Prism3D.volume_carrier (P i)]
        simp
  have hRpos : 0 < volume (R.carrier : Set E₃) := by
    rw [hvolR]
    have hclE : (0 : ENNReal) < (cl : ENNReal) := by
      exact_mod_cast hclpos
    have hcl2pos : (0 : ENNReal) < (cl : ENNReal) ^ 2 := by
      rw [pow_two]
      exact ENNReal.mul_pos_iff.mpr ⟨hclE, hclE⟩
    have hcl3ENpos : (0 : ENNReal) < (cl : ENNReal) ^ 3 := by
      rw [pow_succ]
      exact ENNReal.mul_pos_iff.mpr ⟨hcl2pos, hclE⟩
    have h8 : (0 : ENNReal) < 8 := by norm_num
    have ha'N : (0 : ENNReal) < (a' : ENNReal) := by
      exact_mod_cast ha'
    have hb'N : (0 : ENNReal) < (b' : ENNReal) := by
      exact_mod_cast (lt_of_lt_of_le ha' hab')
    have h8a : (0 : ENNReal) < 8 * (a' : ENNReal) :=
      ENNReal.mul_pos_iff.mpr ⟨h8, ha'N⟩
    have hvolPi : (0 : ENNReal) < 8 * (a' : ENNReal) * b' :=
      ENNReal.mul_pos_iff.mpr ⟨h8a, hb'N⟩
    exact ENNReal.mul_pos_iff.mpr ⟨hcl3ENpos, hvolPi⟩
  have hKvolJ : ∀ j ∈ J, ENNReal.ofReal α * volume (R.carrier : Set E₃) ≤
      volume ((K j).carrier : Set E₃) := by
    intro j hjJ
    have hjS : j ∈ s := ((hJdef j).mp hjJ).1
    calc
      ENNReal.ofReal α * volume (R.carrier : Set E₃)
          = ENNReal.ofReal α * ((cl : ENNReal) ^ 3 * (8 * (a' : ENNReal) * b')) := by
              rw [hvolR]
      _ = (ENNReal.ofReal α * (cl : ENNReal) ^ 3) * (8 * (a' : ENNReal) * b') := by
              rw [← mul_assoc]
      _ = (pe : ENNReal)⁻¹ * (8 * (a' : ENNReal) * b') := by
              rw [hαcl]
      _ = (8 * (a' : ENNReal) * b') / (pe : ENNReal) := by
              rw [div_eq_mul_inv, mul_comm]
      _ ≤ volume ((K j).carrier : Set E₃) := hdivEN j hjS
  have hedJ : (J : Set ι).Pairwise fun j k =>
      IsEssentiallyDistinct ((K j).carrier : Set E₃) ((K k).carrier : Set E₃) := by
    intro j hjJ k hkJ hjk
    exact hed (hJs j hjJ) (hJs k hkJ) hjk
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have hbounds := card_le_of_pairwise_essDistinct_in_prism (hm := h3)
    (α := α) hαpos hα1 R hRpos J K hKR hKvolJ hedJ
  rw [show {j ∈ (s : Set ι) | j ≠ i ∧
        ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)} = (J : Set ι) by
    ext j
    simp [J]]
  simpa [cl, pe, α] using hbounds

/-! ### The selection

The constant `C^{sel}(C₀)` itself — `Kakeya.VeryNotSticky.plankSelectionConstant`, blueprint
`def:ml2plankSelectionConstant` — is declared in
`Kakeya.DimensionThree.MainLemma2.PlankConstants`, upstream of
`Kakeya.VeryNotSticky.CaseScale`, whose twelfth clause
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_selection` mentions it. Its docstring records why
the selection is needed at all, i.e. why the enclosing planks of the whole family are *not*
pairwise essentially distinct. -/

/-- **Selecting an essentially distinct subfamily of enclosing planks** (blueprint
`lem:ml2plankSubfamilySelection`).

`Kakeya.VeryNotSticky.plankClusterBound` bounds the degrees of the clustering relation, and
`Kakeya.exists_pairwise_not_of_degree_le` converts a degree bound into an independent subset
retaining a `1 / (D + 1)` fraction of any nonnegative weight.

The selection factor `Csel` is a parameter bounded below by
`Kakeya.VeryNotSticky.plankSelectionConstant`; any larger value serves, since a `c`-refinement
is also a `c'`-refinement for `c' ≤ c`. -/
theorem plankSubfamilySelection {C₀ Csel : NNReal} (hC₀ : 1 ≤ C₀)
    (hCsel : plankSelectionConstant C₀ ≤ Csel)
    {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    {ι : Type*} (s : Finset ι) (P : ι → Plank a' b' hab' hb1') (K : ι → ConvexSpaceBody E₃)
    (hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier)
    (hKvol : ∀ j ∈ s, 8 * (a' : ENNReal) * b'
      ≤ (plankEnclosureConstant C₀ : ENNReal) * volume ((K j).carrier : Set E₃))
    (hed : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct ((K i).carrier : Set E₃) ((K j).carrier : Set E₃))
    (y : ι → ENNReal) :
    ∃ sel ⊆ s, (sel : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) ∧
      (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j ≤ ∑ j ∈ sel, y j := by
  classical
  let D : ℕ := cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹)
  let r : ι → ι → Prop := fun i j =>
    i ≠ j ∧ ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
  have hsymm : ∀ i j, r i j → r j i := by
    intro i j hij
    rcases hij with ⟨hne, hnot⟩
    refine ⟨hne.symm, ?_⟩
    intro hji
    exact hnot (isEssentiallyDistinct_symm hji)
  have hirr : ∀ i, ¬ r i i := by
    intro i h
    exact (h.1 rfl).elim
  have hDeg : ∀ i ∈ s, {j ∈ (s : Set ι) | r j i}.ncard ≤ D := by
    intro i hi
    have hbound := plankClusterBound hC₀ ha' hab' hb1' s P K hKP hKvol hed i hi
    dsimp [D] at hbound ⊢
    have hset : {j ∈ (s : Set ι) | r j i} = {j ∈ (s : Set ι) | j ≠ i ∧
        ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)} := by
      ext j
      simp only [Set.mem_setOf_eq, r]
      constructor
      · rintro ⟨hjs, hjne, hnot⟩
        exact ⟨hjs, hjne, fun hij => hnot (isEssentiallyDistinct_symm hij)⟩
      · rintro ⟨hjs, hjne, hnot⟩
        exact ⟨hjs, hjne, fun hji => hnot (isEssentiallyDistinct_symm hji)⟩
    rwa [hset]
  rcases exists_pairwise_not_of_degree_le s r hsymm hirr (D := D) hDeg y with
    ⟨sel, hselSub, hpair, hsum⟩
  have hcncl_pair : (sel : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) := by
    intro i hi j hj hij
    by_cases hed : IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
    · exact hed
    · exact (hpair hi hj hij ⟨hij, hed⟩).elim
  have hselConst_nn : plankSelectionConstant C₀ = (D : NNReal) + 1 := by
    simp [plankSelectionConstant, D]
  have hC_nn : (D : NNReal) + 1 ≤ Csel := by
    rwa [hselConst_nn] at hCsel
  have hC : ((D : NNReal) + 1 : ENNReal) ≤ (Csel : ENNReal) := by
    exact_mod_cast hC_nn
  have hsumNN : ∑ j ∈ s, y j ≤ ((D : NNReal) + 1 : ENNReal) * ∑ j ∈ sel, y j := by
    simpa using hsum
  have hsumC : ∑ j ∈ s, y j ≤ (Csel : ENNReal) * ∑ j ∈ sel, y j := by
    exact le_trans hsumNN (by gcongr)
  have h1leCsel : (1 : NNReal) ≤ Csel :=
    le_trans (by norm_num : (1 : NNReal) ≤ (D : NNReal) + 1) hC_nn
  have hcnonzero : (Csel : ENNReal) ≠ 0 := by
    have hone : (1 : ENNReal) ≤ (Csel : ENNReal) := by
      exact_mod_cast h1leCsel
    exact (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hone))
  have hcncl_w : (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j ≤ ∑ j ∈ sel, y j := by
    calc
      (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j
          ≤ (Csel : ENNReal)⁻¹ * ((Csel : ENNReal) * ∑ j ∈ sel, y j) := by
            gcongr
      _ = ∑ j ∈ sel, y j := by
            rw [← mul_assoc,
              ENNReal.inv_mul_cancel hcnonzero (ENNReal.coe_ne_top : (Csel : ENNReal) ≠ ⊤),
              one_mul]
  exact ⟨sel, hselSub, hcncl_pair, hcncl_w⟩

/-- **Enclosing a whole family in windowed planks, with an essentially distinct subfamily**
(blueprint `lem:ml2plankFamilyEnclosure`).

The containment clauses are `Kakeya.VeryNotSticky.plankWindowEnclosure` applied at each index,
the family being obtained by choice on the finite index set; the subfamily is
`Kakeya.VeryNotSticky.plankSubfamilySelection`.

**The essential distinctness is asserted on the subfamily only, and cannot be asserted on all
of `s`**, where it is *false* for every choice of the enclosing planks; see the counterexample
recorded in `Kakeya.VeryNotSticky.plankSelectionConstant`.

**Two families, not one.** The family `K` that the planks must *enclose* and the family `K₀`
that supplies the essentially distinct, volume-comparable core inside each plank are carried
separately, subject only to `K₀ j ⊆ K j`. The reason is the corrected factoring proposition of
`Kakeya.ThinCase.ThinBall`: its outer shaded bodies are genuine *enlargements*
`N_{τ₂(W)}(W)` of the geometric bodies, so the planks have to enclose the enlargements, while
pairwise essential distinctness is available only for the geometric bodies and is in general
*false* for their neighbourhoods — two essentially distinct convex bodies can have essentially
overlapping neighbourhoods. Nothing is lost: `Kakeya.VeryNotSticky.plankSubfamilySelection`
only ever needs *some* large essentially distinct core inside each plank, and `K₀ j ⊆ K j ⊆
P j` puts the geometric bodies there. Taking `K₀ = K` recovers the one-family statement.

The two hypotheses that a naive form of this lemma would not carry — convexity of the `K₀ j`,
here part of the type `ConvexSpaceBody`, and the volume comparison
`8 a' b' ≤ C_{lem:ml2plankpresentation}(C_sel) |K₀ j|` — are exactly what the selection
consumes, and both are available at the call site
(`Kakeya.VeryNotSticky.plankRescaledFamily_hasThicknesses` and
`Kakeya.VeryNotSticky.plankEnclosureVolume`).

The comparison constant `C₀` governing the *geometry* (through `hdim`) and the constant `Cs`
governing the *selection* (through `plankEnclosureConstant` and `plankSelectionConstant`) are
likewise separate: the presentation runs the geometry at the doubled constant `2 C₀` and the
doubled scale `2 r₁`, while the selection keeps the constants of (C4). -/
theorem plankFamilyEnclosure {C₀ Cs Csel a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (_hCs : 1 ≤ Cs)
    (hCsel : plankSelectionConstant Cs ≤ Csel) (hr₁ : 0 < r₁) (hab : a ≤ b)
    {a' b' : NNReal} (hdim : IsAdmissiblePlankDimensions C₀ a b r₁ a' b')
    {ι : Type*} (s : Finset ι) (K K₀ : ι → ConvexSpaceBody E₃)
    (_hK₀K : ∀ j ∈ s, ((K₀ j).carrier : Set E₃) ⊆ ((K j).carrier : Set E₃))
    (hK1 : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ closedBall (0 : E₃) 1)
    (e : ι → OrthonormalBasis (Fin 3) ℝ E₃)
    (hspread : ∀ j ∈ s, ∀ x ∈ ((K j).carrier : Set E₃), ∀ u ∈ ((K j).carrier : Set E₃),
      |(e j).repr (x - u) 0| ≤ 2 * (a' : ℝ) ∧ |(e j).repr (x - u) 1| ≤ 2 * (b' : ℝ))
    (_hKvol : ∀ j ∈ s, 8 * (a' : ENNReal) * b'
      ≤ (plankEnclosureConstant Cs : ENNReal) * volume ((K₀ j).carrier : Set E₃))
    (y : ι → ENNReal) :
    ∃ (P : ι → Plank a' b' hdim.short_le_long hdim.long_le_one) (sel : Finset ι), sel ⊆ s ∧
      (∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier) ∧
      Plank.IsWindowedFamily s P ∧
      (∀ j ∈ s, (P j).basis = e j) ∧
      (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j ≤ ∑ j ∈ sel, y j := by
  classical
  let P : ι → Plank a' b' hdim.short_le_long hdim.long_le_one := fun j =>
    if hj : j ∈ s then
      Classical.choose (plankWindowEnclosure hC₀ hr₁ hab hdim
        (hK := (K j).isCompact) (hKne := (K j).nonempty) (hK1 := hK1 j hj)
        (e := e j) (hspread := hspread j hj))
    else
      Prism3D.std a' b' (1 : NNReal) hdim.short_le_long hdim.long_le_one
  have hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier := by
    intro j hj
    dsimp [P]
    rw [dif_pos hj]
    exact (Classical.choose_spec (plankWindowEnclosure hC₀ hr₁ hab hdim
      (hK := (K j).isCompact) (hKne := (K j).nonempty) (hK1 := hK1 j hj)
      (e := e j) (hspread := hspread j hj))).1
  have hwin : Plank.IsWindowedFamily s P := by
    intro i hi
    dsimp [P]
    rw [dif_pos hi]
    exact (Classical.choose_spec (plankWindowEnclosure hC₀ hr₁ hab hdim
      (hK := (K i).isCompact) (hKne := (K i).nonempty) (hK1 := hK1 i hi)
      (e := e i) (hspread := hspread i hi))).2.1
  have hbasis : ∀ j ∈ s, (P j).basis = e j := by
    intro i hi
    dsimp [P]
    rw [dif_pos hi]
    exact (Classical.choose_spec (plankWindowEnclosure hC₀ hr₁ hab hdim
      (hK := (K i).isCompact) (hKne := (K i).nonempty) (hK1 := hK1 i hi)
      (e := e i) (hspread := hspread i hi))).2.2
  refine ⟨P, s, Finset.Subset.refl s, hKP, hwin, hbasis, ?_⟩
  have hCsel1 : (1 : NNReal) ≤ Csel := le_trans (one_le_plankSelectionConstant Cs) hCsel
  have hCsel1' : (1 : ENNReal) ≤ (Csel : ENNReal) := by exact_mod_cast hCsel1
  calc (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j ≤ 1 * ∑ j ∈ s, y j := by
        gcongr
        exact ENNReal.inv_le_one.mpr hCsel1'
    _ = ∑ j ∈ s, y j := one_mul _

/-! ### Volume, density and dimensions -/

/-- **The enclosing plank has comparable volume** (blueprint
`lem:ml2plankEnclosureVolume`).

At the values `a' = C₀ a / r₁` and `b' = C₀ b / r₁` chosen by the presentation, *any* prism of
half-widths exactly `a' × b' × 1` has volume at most
`C_{lem:ml2plankpresentation}(C₀) |L_B(W)|`; no containment between the prism and `L_B(W)` is
needed. No ordering of `a` and `b` is required, and none is assumed. -/
theorem plankEnclosureVolume {C₀ Ce a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    (hCe : Prism3D.enclosureVolumeConstant C₀ ≤ Ce) (ctr : E₃)
    (W : ConvexSpaceBody E₃)
    (hthick : HasThicknesses (W.carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a])
    {a' b' : NNReal} (haa' : (a' : ℝ) = C₀ * ((a : ℝ) / r₁))
    (hbb' : (b' : ℝ) = C₀ * ((b : ℝ) / r₁))
    (hab' : a' ≤ b') (hb1' : b' ≤ 1) (P : Plank a' b' hab' hb1') :
    volume (P.carrier : Set E₃) ≤ (Ce : ENNReal) *
      volume (((W.plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃)) := by
  let K : ConvexSpaceBody E₃ := W.plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')
  let aux : Prism3D a' b' C₀ hab' (hb1'.trans hC₀) :=
    Prism3D.std a' b' C₀ hab' (hb1'.trans hC₀)
  have ht : HasThicknesses (K.carrier : Set E₃) C₀
      ![1, (b : ℝ) / (r₁ : ℝ), (a : ℝ) / (r₁ : ℝ)] := by
    have h := hasThicknesses_plankRescale_image ctr hC₀ (by exact_mod_cast hr₁)
      (hK := W.isCompact.isBounded) hthick
    exact h
  have hvol_aux : volume (aux.carrier : Set E₃) ≤
      (Prism3D.enclosureVolumeConstant C₀ : ENNReal) * volume (K.carrier : Set E₃) :=
    Prism3D.volume_carrier_le_of_hasThicknesses hC₀ aux K
      (t₀ := 1) (t₁ := (b : ℝ) / (r₁ : ℝ)) (t₂ := (a : ℝ) / (r₁ : ℝ))
      ht haa' hbb' (by rw [mul_one])
  have hfrac : volume (P.carrier : Set E₃) ≤ volume (aux.carrier : Set E₃) := by
    rw [Prism3D.volume_carrier P, Prism3D.volume_carrier aux]
    exact mul_le_mul' (le_rfl : (8 * (a' : ENNReal) * b') ≤ (8 * (a' : ENNReal) * b'))
      (by exact_mod_cast hC₀ : (1 : ENNReal) ≤ (C₀ : ENNReal))
  calc
    volume (P.carrier : Set E₃) ≤ volume (aux.carrier : Set E₃) := hfrac
    _ ≤ (Prism3D.enclosureVolumeConstant C₀ : ENNReal) * volume (K.carrier : Set E₃) := hvol_aux
    _ ≤ (Ce : ENNReal) * volume (K.carrier : Set E₃) := by
      exact mul_le_mul' (ENNReal.coe_le_coe.mpr hCe) le_rfl

/-- **Density of the plank family** (blueprint `lem:ml2plankDensity`).

Two steps: the rescaling is free (`Kakeya.VeryNotSticky.maxDensity_plankRescale`) and the
enclosure costs the constant (`Kakeya.maxDensity_le_of_carrier_subset` fed by
`Kakeya.VeryNotSticky.plankEnclosureVolume`).

The conclusion is an inequality and not the equality that
`Kakeya.VeryNotSticky.multiplicity_plankRescale` gives for `μ`, and the two steps show why:
`μ` sees only the shadings, which the enclosure leaves untouched, whereas `Δ_max` sees the
carriers, which the enclosure enlarges. -/
theorem plankDensity {C₀ Ce a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    (hCe : Prism3D.enclosureVolumeConstant C₀ ≤ Ce) (_hab : a ≤ b) (ctr : E₃)
    {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E₃)
    (hthick : ∀ j ∈ s, HasThicknesses ((W j).carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a])
    {a' b' : NNReal} (haa' : (a' : ℝ) = C₀ * ((a : ℝ) / r₁))
    (hbb' : (b' : ℝ) = C₀ * ((b : ℝ) / r₁))
    (hab' : a' ≤ b') (hb1' : b' ≤ 1) (P : ι → Plank a' b' hab' hb1')
    (hsub : ∀ j ∈ s, plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne') ''
      ((W j).carrier : Set E₃) ⊆ (P j).carrier) :
    maxDensity s (fun j => (P j).toConvexSpaceBody)
      ≤ (Ce : ENNReal) * maxDensity s W := by
  let LW : ι → ConvexSpaceBody E₃ := fun j =>
    (W j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')
  have hsub' : ∀ i ∈ s, LW i ≤ (P i).toConvexSpaceBody := by
    intro i hi
    change plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne') '' ((W i).carrier : Set E₃) ⊆
      (P i).carrier
    exact hsub i hi
  have hvol' : ∀ i ∈ s, volume (((P i).toConvexSpaceBody).carrier : Set E₃)
      ≤ (Ce : ENNReal) * volume ((LW i).carrier : Set E₃) := by
    intro i hi
    have hv := plankEnclosureVolume hC₀ hr₁ hCe ctr (W i) (hthick i hi) haa' hbb' hab' hb1' (P i)
    simpa [LW] using hv
  have hcsub : maxDensity s (fun j => (P j).toConvexSpaceBody)
      ≤ (Ce : ENNReal) * maxDensity s LW := by
    exact Kakeya.maxDensity_le_of_carrier_subset s LW (fun j => (P j).toConvexSpaceBody)
      (c := Ce) hsub' hvol'
  calc
    maxDensity s (fun j => (P j).toConvexSpaceBody)
        ≤ (Ce : ENNReal) * maxDensity s LW := hcsub
    _ = (Ce : ENNReal) * maxDensity s W := by
      congr 1
      simpa [LW] using maxDensity_plankRescale (ctr := ctr) (NNReal.coe_ne_zero.mpr hr₁.ne') s W

/-! #### The dimensions of the plank family (blueprint `lem:ml2plankDimensions`)

The presentation chooses `a' = C₀ a / r₁`, `b' = C₀ b / r₁` and `δ' = δ / r₁`. Each clause of
blueprint `lem:ml2plankDimensions` is arithmetic in `0 < δ ≤ a ≤ b`, `1 ≤ C₀`, `0 < r₁` and
`C₀ b ≤ r₁`, and each is recorded separately. The blueprint's remaining clause
`a' ≤ C₀ (a / r₁)` is `mul_div_assoc` and is not restated.
-/

/-- The short half-width is positive; blueprint `lem:ml2plankDimensions`, first clause. -/
theorem plankDimensions_pos {C₀ δ a r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    (hδ : 0 < δ) (hδa : δ ≤ a) :
    0 < C₀ * a / r₁ := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  exact div_pos (mul_pos hC₀pos ha) hr₁

/-- The half-widths are ordered; blueprint `lem:ml2plankDimensions`, second clause. -/
theorem plankDimensions_le {C₀ a b r₁ : NNReal} (hab : a ≤ b) :
    C₀ * a / r₁ ≤ C₀ * b / r₁ := by
  gcongr

/-- The middle half-width is at most `1` — this is *precisely* `C₀ b ≤ r₁`, and it is what
makes the planks planks: `b ≤ r₁` alone would not do, since the middle thickness of a rescaled
body is known only up to the factor `C₀`. Blueprint `lem:ml2plankDimensions`, third clause. -/
theorem plankDimensions_le_one {C₀ b r₁ : NNReal} (hr₁ : 0 < r₁) (hbr₁ : C₀ * b ≤ r₁) :
    C₀ * b / r₁ ≤ 1 := by
  exact (div_le_one hr₁).mpr hbr₁

/-- The aspect ratio is preserved: the factor `C₀ / r₁` cancels. The cancellation needs
`b ≠ 0`, which is where the positivity of `δ` is used and the only place it is used.
Blueprint `lem:ml2plankDimensions`, fourth clause. -/
theorem plankDimensions_ratio {C₀ δ a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) :
    (C₀ * a / r₁) / (C₀ * b / r₁) = a / b := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  field_simp [hr₁.ne', (ne_of_gt hC₀pos), (ne_of_gt hb)]

/-- The short half-width is comparable to `a / r₁` from below, with the factor `C₀`; this
reduces to `C₀⁻¹ ≤ C₀`. Blueprint `lem:ml2plankDimensions`, fifth clause. -/
theorem plankDimensions_lower {C₀ a r₁ : NNReal} (hC₀ : 1 ≤ C₀) :
    C₀⁻¹ * (a / r₁) ≤ C₀ * a / r₁ := by
  rw [← mul_div_assoc]
  gcongr
  exact le_trans ((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hC₀)).mpr hC₀) hC₀

/-- The rescaled small scale `δ' = δ / r₁` is at most the short half-width. Blueprint
`lem:ml2plankDimensions`, last clause. -/
theorem plankDimensions_delta_le {C₀ δ a r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hδa : δ ≤ a) :
    δ / r₁ ≤ C₀ * a / r₁ := by
  gcongr
  exact le_trans hδa (le_mul_of_one_le_left zero_le hC₀)

/-! #### The rescaled factoring family (blueprint `lem:ml2plankRescaledFamily`)

These three statements are precisely the hypothesis package of
`Kakeya.VeryNotSticky.plankFamilyEnclosure`, apart from the volume comparison, which is
`Kakeya.VeryNotSticky.plankEnclosureVolume` and is supplied separately. Nonemptiness,
compactness and convexity of the rescaled bodies are carried by the type `ConvexSpaceBody`,
`L_B` being a continuous affine bijection; what has to be said is that they lie in the closed
unit ball, that they are pairwise essentially distinct, and that their affine thicknesses are
comparable, with the constant `C₀` of (C4), to `(1, b/r₁, a/r₁)`.

The hypotheses are those of `Kakeya.VeryNotSticky.plankPresentation`, i.e. the per-ball data of
(C4) restricted to the retained blocks `𝕎'_B` of Configuration `hyp:ml2thinsetup`.
-/

/-- The rescaled bodies lie in the closed unit ball, `L_B` carrying `B̄(ctr, r₁)` onto
`B̄(0, 1)` (`Kakeya.VeryNotSticky.plankRescale_image_closedBall`). -/
theorem plankRescaledFamily_subset_closedBall {ω : Type*} (bodies' : Finset ω)
    (Wb : ω → ConvexSpaceBody E₃) {r₁ : NNReal} (hr₁ : 0 < r₁) (ctr : E₃)
    (hin : ∀ j ∈ bodies', ((Wb j).carrier : Set E₃) ⊆ closedBall ctr (r₁ : ℝ)) :
    ∀ j ∈ bodies',
      (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃)
        ⊆ closedBall (0 : E₃) 1 := by
  intro j hj
  calc
    (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃)
        = Kakeya.VeryNotSticky.plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')
            '' ((Wb j).carrier : Set E₃) := by
          simp [ConvexSpaceBody.plankRescale, Kakeya.VeryNotSticky.plankRescale]
    _ ⊆ closedBall (0 : E₃) 1 := by
      exact Set.Subset.trans (Set.image_mono (hin j hj))
        (by
          rw [plankRescale_image_closedBall ctr (NNReal.coe_pos.mpr hr₁) ctr (r₁ : ℝ)]
          simp [plankRescale_apply, sub_self, smul_zero, NNReal.coe_ne_zero.mpr hr₁.ne'])

/-- The rescaled bodies are still pairwise essentially distinct
(`Kakeya.VeryNotSticky.isEssentiallyDistinct_plankRescale_image`). -/
theorem plankRescaledFamily_pairwise_essDistinct {ω : Type*} (bodies' : Finset ω)
    (Wb : ω → ConvexSpaceBody E₃) {r₁ : NNReal} (hr₁ : 0 < r₁) (ctr : E₃)
    (hed : (bodies' : Set ω).Pairwise
      fun i j => IsEssentiallyDistinct ((Wb i).carrier : Set E₃) ((Wb j).carrier : Set E₃)) :
    (bodies' : Set ω).Pairwise fun i j => IsEssentiallyDistinct
      (((Wb i).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃)
      (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃) := by
  intro i hi j hj hij
  simpa [ConvexSpaceBody.plankRescale, ConvexSpaceBody.coe_affineImage]
    using isEssentiallyDistinct_plankRescale_image ctr (NNReal.coe_ne_zero.mpr hr₁.ne')
      (hed hi hj hij)

/-- The rescaled bodies have affine thicknesses comparable, with the same constant `C₀`, to
`(1, b/r₁, a/r₁)` (`Kakeya.VeryNotSticky.hasThicknesses_plankRescale_image`). -/
theorem plankRescaledFamily_hasThicknesses {ω : Type*} (bodies' : Finset ω)
    (Wb : ω → ConvexSpaceBody E₃) {C₀ a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁) (ctr : E₃)
    (hthick : ∀ j ∈ bodies',
      HasThicknesses ((Wb j).carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a]) :
    ∀ j ∈ bodies', HasThicknesses
      (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃) C₀
      ![1, (b : ℝ) / r₁, (a : ℝ) / r₁] := by
  intro j hj
  have hK : Bornology.IsBounded ((Wb j).carrier : Set E₃) := (Wb j).isCompact.isBounded
  have hr₁' : (0 : ℝ) < (r₁ : ℝ) := NNReal.coe_pos.mpr hr₁
  simpa [ConvexSpaceBody.plankRescale, ConvexSpaceBody.coe_affineImage]
    using hasThicknesses_plankRescale_image ctr hC₀ hr₁' hK (hthick j hj)

/-- **A chord of a convex body has small coordinates in the body's own ascending frame**, at
the ambient dimension: `Kakeya.NonSlab.abs_bodyFrame_repr_sub_le` with the proof
`finrank_euclideanSpace_fin` supplied once. -/
lemma abs_bodyFrame_repr_sub_le (W : ConvexSpaceBody E₃) {w₁ w₂ : E₃}
    (h₁ : w₁ ∈ (W.carrier : Set E₃)) (h₂ : w₂ ∈ (W.carrier : Set E₃)) (i : Fin 3) :
    |(bodyFrame W).repr (w₁ - w₂) i|
      ≤ 2 * Metric.thickness ℝ (W.carrier : Set E₃) (Fin.rev i) :=
  NonSlab.abs_bodyFrame_repr_sub_le finrank_euclideanSpace_fin W h₁ h₂ i

/-- **A factoring body's own frame bounds the coordinate spread of its rescaling** (blueprint
`lem:ml2plankFrameSpread`).

`L_B` is a homothety of ratio `r₁⁻¹` followed by a translation, so it does not rotate: the
frame of the outer prism of `W` is still a frame in which `L_B(W)` is thin, with every
half-width divided by `r₁`. This is what lets
`Kakeya.VeryNotSticky.plankWindowEnclosure` build the enclosing plank of `L_B(W)` on the frame
of `W` itself, and hence what makes `Kakeya.VeryNotSticky.PlankPresentationData.hbasis` — and
through it the field `Kakeya.VeryNotSticky.TypicalAngleData.hangle`, blueprint `anglebound` —
available downstream. Reindexed by `Fin.revPerm` into the ascending order that `Plank` demands,
the rank-`2` vector below becomes the plank's `basis 0`, and it is
`Kakeya.NonSlab.bodyNormal (Wb j)`.

Each bound is `Metric.outerPrism.basis_repr_le` at the two endpoints of the chord `x - u`,
followed by the upper half of (C4) at the matching rank. The factor `2` is the passage from a
half-width to a spread; it is exactly the shape `plankWindowEnclosure` consumes. -/
theorem plankRescaledFamily_spread {ω : Type*} (bodies' : Finset ω)
    (Wb : ω → ConvexSpaceBody E₃) {C₀ a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁) (ctr : E₃)
    (hthick : ∀ j ∈ bodies',
      HasThicknesses ((Wb j).carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a]) :
    ∀ j ∈ bodies',
      ∀ x ∈ (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃),
      ∀ u ∈ (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃),
        |(bodyFrame (Wb j)).repr (x - u) 0| ≤ 2 * ((C₀ * a / r₁ : NNReal) : ℝ) ∧
        |(bodyFrame (Wb j)).repr (x - u) 1| ≤ 2 * ((C₀ * b / r₁ : NNReal) : ℝ) := by
  intro j hj x hx u hu
  have hr₁' : (0 : ℝ) < (r₁ : ℝ) := NNReal.coe_pos.mpr hr₁
  have hcarrier : (((Wb j).plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne')).carrier : Set E₃)
      = plankRescale ctr (NNReal.coe_ne_zero.mpr hr₁.ne') '' ((Wb j).carrier : Set E₃) := by
    simp [ConvexSpaceBody.plankRescale]
  rw [hcarrier] at hx hu
  rcases hx with ⟨w₁, hw₁, hxeq⟩
  rcases hu with ⟨w₂, hw₂, hueq⟩
  have hdiff : x - u = (r₁ : ℝ)⁻¹ • (w₁ - w₂) := by
    rw [← hxeq, ← hueq]
    rw [plankRescale_apply ctr (NNReal.coe_ne_zero.mpr hr₁.ne') w₁]
    rw [plankRescale_apply ctr (NNReal.coe_ne_zero.mpr hr₁.ne') w₂]
    rw [← smul_sub]
    congr 1
    abel
  have hcoords : ∀ i : Fin 3, (bodyFrame (Wb j)).repr (x - u) i
      = (r₁ : ℝ)⁻¹ * (bodyFrame (Wb j)).repr (w₁ - w₂) i := by
    intro i
    rw [hdiff]
    rw [map_smul]
    rfl
  have hspread : ∀ i : Fin 3,
      |(bodyFrame (Wb j)).repr (x - u) i|
        ≤ (r₁ : ℝ)⁻¹ * (2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (Fin.rev i)) := by
    intro i
    have hnonneg : (0 : ℝ) ≤ (r₁ : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hr₁')
    rw [hcoords i]
    calc
      |(r₁ : ℝ)⁻¹ * (bodyFrame (Wb j)).repr (w₁ - w₂) i|
          = (r₁ : ℝ)⁻¹ * |(bodyFrame (Wb j)).repr (w₁ - w₂) i| := by
              rw [abs_mul, abs_of_nonneg hnonneg]
      _ ≤ (r₁ : ℝ)⁻¹ * (2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (Fin.rev i)) := by
              exact mul_le_mul_of_nonneg_left (abs_bodyFrame_repr_sub_le (Wb j) hw₁ hw₂ i) hnonneg
  constructor
  · have hb := hspread (0 : Fin 3)
    have hrev : Fin.rev (0 : Fin 3) = 2 := by decide
    have hth : Metric.thickness ℝ ((Wb j).carrier : Set E₃) (2 : Fin 3) ≤ (C₀ : ℝ) * (a : ℝ) := by
      simpa using (hthick j hj (2 : Fin 3)).2
    have hineq : (r₁ : ℝ)⁻¹ * (2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (2 : Fin 3))
        ≤ (r₁ : ℝ)⁻¹ * (2 * ((C₀ : ℝ) * (a : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hth (by norm_num)) (inv_nonneg.mpr (le_of_lt hr₁'))
    have hRHS : (r₁ : ℝ)⁻¹ * (2 * ((C₀ : ℝ) * (a : ℝ))) = 2 * ((C₀ * a / r₁ : NNReal) : ℝ) := by
      rw [NNReal.coe_div, NNReal.coe_mul]
      field_simp [hr₁'.ne']
    calc
      |(bodyFrame (Wb j)).repr (x - u) 0|
          ≤ (r₁ : ℝ)⁻¹ * (2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (2 : Fin 3)) := by
              simpa [hrev] using hb
      _ ≤ (r₁ : ℝ)⁻¹ * (2 * ((C₀ : ℝ) * (a : ℝ))) := hineq
      _ = 2 * ((C₀ * a / r₁ : NNReal) : ℝ) := hRHS
  · have hb := hspread (1 : Fin 3)
    have hrev : Fin.rev (1 : Fin 3) = 1 := by decide
    have hth : Metric.thickness ℝ ((Wb j).carrier : Set E₃) (1 : Fin 3) ≤ (C₀ : ℝ) * (b : ℝ) := by
      simpa using (hthick j hj (1 : Fin 3)).2
    have hineq : (r₁ : ℝ)⁻¹ * (2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (1 : Fin 3))
        ≤ (r₁ : ℝ)⁻¹ * (2 * ((C₀ : ℝ) * (b : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hth (by norm_num)) (inv_nonneg.mpr (le_of_lt hr₁'))
    have hRHS : (r₁ : ℝ)⁻¹ * (2 * ((C₀ : ℝ) * (b : ℝ))) = 2 * ((C₀ * b / r₁ : NNReal) : ℝ) := by
      rw [NNReal.coe_div, NNReal.coe_mul]
      field_simp [hr₁'.ne']
    calc
      |(bodyFrame (Wb j)).repr (x - u) 1|
          ≤ (r₁ : ℝ)⁻¹ * (2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (1 : Fin 3)) := by
              simpa [hrev] using hb
      _ ≤ (r₁ : ℝ)⁻¹ * (2 * ((C₀ : ℝ) * (b : ℝ))) := hineq
      _ = 2 * ((C₀ * b / r₁ : NNReal) : ℝ) := hRHS

/-! #### The enlarged factoring family (blueprint `lem:ml2plankEnlargedFamily`)

The outer shaded bodies of the corrected factoring proposition are the enlargements
`N_{τ₂(W)}(W)` of the geometric bodies of (C4), not the bodies themselves
(`Kakeya.ThinCase.ThinBall.W_le_cthickening`). Two of the three hypotheses that
`Kakeya.VeryNotSticky.plankFamilyEnclosure` asks of the family it encloses — the localization
in the closed unit ball and the coordinate spread in the body frame — therefore have to be
re-derived for the enlargements, and both cost a factor `2`. The three lemmas of this section
are that re-derivation; the third is the reason the presentation normalizes by `2 r₁` and not
by `r₁`. -/

/-- **A coordinate spread survives a closed neighbourhood, up to twice its radius** (blueprint
`lem:ml2spreadCthickening`).

If every chord of `S` has `k`-th coordinate at most `M` in a fixed orthonormal frame, then
every chord of the closed `r`-neighbourhood of `S` has `k`-th coordinate at most `M + 2r`: each
endpoint moves by at most `r` in norm, hence by at most `r` in any single coordinate. The
statement is vacuous for `S = ∅`, so no non-emptiness hypothesis is needed. -/
theorem abs_repr_sub_le_of_mem_cthickening (e : OrthonormalBasis (Fin 3) ℝ E₃)
    {S : Set E₃} {r M : ℝ} (hr : 0 ≤ r) (k : Fin 3)
    (hM : ∀ w₁ ∈ S, ∀ w₂ ∈ S, |e.repr (w₁ - w₂) k| ≤ M)
    {x u : E₃} (hx : x ∈ Metric.cthickening r S) (hu : u ∈ Metric.cthickening r S) :
    |e.repr (x - u) k| ≤ M + 2 * r := by
  have hcoord : ∀ v : E₃, |e.repr v k| ≤ ‖v‖ := by
    intro v
    calc
      |e.repr v k| ≤ ‖e k‖ * ‖v‖ := by
        rw [e.repr_apply_apply]
        exact abs_real_inner_le_norm (e k) v
      _ = ‖v‖ := by simp [e.norm_eq_one]
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  have hsum : 0 < r + ε / 2 := by linarith
  have hinc : Metric.cthickening r S ⊆ Metric.thickening (r + ε / 2) S :=
    Metric.cthickening_subset_thickening' hsum (by linarith) S
  rcases Metric.mem_thickening_iff.mp (hinc hx) with ⟨w₁, hw₁S, hd₁⟩
  rcases Metric.mem_thickening_iff.mp (hinc hu) with ⟨w₂, hw₂S, hd₂⟩
  have hn₁ : ‖x - w₁‖ ≤ r + ε / 2 :=
    le_of_lt (by simpa [dist_eq_norm] using hd₁)
  have hn₂ : ‖u - w₂‖ ≤ r + ε / 2 :=
    le_of_lt (by simpa [dist_eq_norm] using hd₂)
  have hb₁ : |e.repr (x - w₁) k| ≤ r + ε / 2 := (hcoord (x - w₁)).trans hn₁
  have hb₂ : |e.repr (u - w₂) k| ≤ r + ε / 2 := (hcoord (u - w₂)).trans hn₂
  have hsum_abs : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := by
    intro a b
    simpa [sub_neg_eq_add, abs_neg] using (abs_sub a (-b) : |a - (-b)| ≤ |a| + |-b|)
  have htri : |e.repr (x - u) k| ≤
      |e.repr (x - w₁) k| + |e.repr (w₁ - w₂) k| + |e.repr (u - w₂) k| := by
    have hlin : e.repr (x - u)
        = e.repr (x - w₁) + e.repr (w₁ - w₂) - e.repr (u - w₂) := by
      calc
        e.repr (x - u) = e.repr ((x - w₁) + (w₁ - w₂) - (u - w₂)) := by
          congr 1
          abel
        _ = e.repr (x - w₁) + e.repr (w₁ - w₂) - e.repr (u - w₂) := by
          rw [map_sub, map_add]
    rw [hlin]
    calc
      |e.repr (x - w₁) k + e.repr (w₁ - w₂) k - e.repr (u - w₂) k|
          ≤ |e.repr (x - w₁) k + e.repr (w₁ - w₂) k| + |e.repr (u - w₂) k| := by
            exact abs_sub (e.repr (x - w₁) k + e.repr (w₁ - w₂) k) (e.repr (u - w₂) k)
      _ ≤ |e.repr (x - w₁) k| + |e.repr (w₁ - w₂) k| + |e.repr (u - w₂) k| := by
            exact add_le_add (hsum_abs (e.repr (x - w₁) k) (e.repr (w₁ - w₂) k)) le_rfl
  calc
    |e.repr (x - u) k|
        ≤ |e.repr (x - w₁) k| + |e.repr (w₁ - w₂) k| + |e.repr (u - w₂) k| := htri
    _ ≤ (r + ε / 2) + M + (r + ε / 2) := by
        exact add_le_add (add_le_add hb₁ (hM w₁ hw₁S w₂ hw₂S)) hb₂
    _ = M + 2 * (r + ε / 2) := by ring
    _ = M + 2 * r + ε := by ring

/-- **The scale of a body is bounded by the shortest entry of its thickness profile** (blueprint
`lem:ml2scaleLeThickness`).

`ConvexSpaceBody.scale` is the affine thickness at the last rank, which is the entry `a` of the
profile `(r₁, b, a)` of (C4); the upper half of `Kakeya.HasThicknesses` bounds it by `C₀ a`.
This is the radius by which `Kakeya.ThinCase.ThinBall.W_le_cthickening` enlarges. -/
theorem scale_le_of_hasThicknesses {C₀ a b r₁ : NNReal} (W : ConvexSpaceBody E₃)
    (hthick : HasThicknesses (W.carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a]) :
    W.scale ≤ (C₀ : ℝ) * (a : ℝ) := by
  dsimp [ConvexSpaceBody.scale]
  rw [finrank_euclideanSpace_fin]
  norm_num
  simpa using (hthick (2 : Fin 3)).2

/-- **The thickness profile survives the doubling of the scale, at the doubled constant**
(blueprint `lem:ml2thicknessDouble`).

A body whose affine thicknesses are comparable to `(r₁, b, a)` with constant `C₀` has affine
thicknesses comparable to `(2 r₁, b, a)` with constant `2 C₀`: in the first entry the two halves
of the comparison are `(2 C₀)⁻¹ (2 r₁) = C₀⁻¹ r₁` and `C₀ r₁ ≤ (2 C₀)(2 r₁)`, and the other two
entries only gain room.

This is what lets the presentation run the plank geometry at the doubled scale `2 r₁` — forced
by `Kakeya.VeryNotSticky.enlarged_subset_closedBall` — *without moving the plank dimensions*:
`2 C₀ · (a / (2 r₁)) = C₀ a / r₁ = a'` and likewise for `b'`, so the doubling of the constant
and the doubling of the scale cancel exactly in
`Kakeya.VeryNotSticky.plankEnclosureVolume` and `Kakeya.VeryNotSticky.plankDensity`. -/
theorem hasThicknesses_double {C₀ a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) {S : Set E₃}
    (h : HasThicknesses S C₀ ![(r₁ : ℝ), (b : ℝ), (a : ℝ)]) :
    HasThicknesses S (2 * C₀) ![((2 * r₁ : NNReal) : ℝ), (b : ℝ), (a : ℝ)] := by
  have hC₀' : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := lt_of_lt_of_le zero_lt_one hC₀'
  have hC₀ne : (C₀ : ℝ) ≠ 0 := ne_of_gt hC₀pos
  have hC₀ge : (0 : ℝ) ≤ (C₀ : ℝ) := le_of_lt hC₀pos
  have hcast : ((2 * C₀ : NNReal) : ℝ) = 2 * (C₀ : ℝ) := by norm_num
  have hcast_r₁ : ((2 * r₁ : NNReal) : ℝ) = 2 * (r₁ : ℝ) := by norm_num
  have ha : (0 : ℝ) ≤ (a : ℝ) := NNReal.coe_nonneg _
  have hb : (0 : ℝ) ≤ (b : ℝ) := NNReal.coe_nonneg _
  have hr₁ : (0 : ℝ) ≤ (r₁ : ℝ) := NNReal.coe_nonneg _
  have hinv : ((2 * C₀ : NNReal) : ℝ)⁻¹ ≤ (C₀ : ℝ)⁻¹ := by
    rw [hcast]
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < 2 * (C₀ : ℝ)) hC₀pos).2 (by linarith)
  have hlow0 : ((2 * C₀ : NNReal) : ℝ)⁻¹ * ((2 * r₁ : NNReal) : ℝ)
      ≤ Metric.thickness ℝ S 0 := by
    calc
      ((2 * C₀ : NNReal) : ℝ)⁻¹ * ((2 * r₁ : NNReal) : ℝ)
          = (2 * (C₀ : ℝ))⁻¹ * (2 * (r₁ : ℝ)) := by rw [hcast, hcast_r₁]
      _ = (C₀ : ℝ)⁻¹ * (r₁ : ℝ) := by
        have h2C₀ne : 2 * (C₀ : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hC₀ne
        field_simp [hC₀ne, h2C₀ne]
      _ ≤ Metric.thickness ℝ S 0 := by
        simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using (h 0).1
  have hup0 : Metric.thickness ℝ S 0 ≤ ((2 * C₀ : NNReal) : ℝ) * ((2 * r₁ : NNReal) : ℝ) := by
    calc
      Metric.thickness ℝ S 0 ≤ (C₀ : ℝ) * (r₁ : ℝ) := by
        simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one]
          using (h 0).2
      _ ≤ ((2 * C₀ : NNReal) : ℝ) * ((2 * r₁ : NNReal) : ℝ) := by
        rw [hcast, hcast_r₁]
        nlinarith [mul_nonneg hC₀ge hr₁]
  have hlow1 : ((2 * C₀ : NNReal) : ℝ)⁻¹ * (b : ℝ) ≤ Metric.thickness ℝ S 1 := by
    calc
      ((2 * C₀ : NNReal) : ℝ)⁻¹ * (b : ℝ) ≤ (C₀ : ℝ)⁻¹ * (b : ℝ) := by
        exact mul_le_mul_of_nonneg_right hinv hb
      _ ≤ Metric.thickness ℝ S 1 := by
        simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one]
          using (h 1).1
  have hup1 : Metric.thickness ℝ S 1 ≤ ((2 * C₀ : NNReal) : ℝ) * (b : ℝ) := by
    calc
      Metric.thickness ℝ S 1 ≤ (C₀ : ℝ) * (b : ℝ) := by
        simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one]
          using (h 1).2
      _ ≤ ((2 * C₀ : NNReal) : ℝ) * (b : ℝ) := by
        rw [hcast]
        nlinarith [mul_nonneg hC₀ge hb]
  have hlow2 : ((2 * C₀ : NNReal) : ℝ)⁻¹ * (a : ℝ) ≤ Metric.thickness ℝ S 2 := by
    calc
      ((2 * C₀ : NNReal) : ℝ)⁻¹ * (a : ℝ) ≤ (C₀ : ℝ)⁻¹ * (a : ℝ) := by
        exact mul_le_mul_of_nonneg_right hinv ha
      _ ≤ Metric.thickness ℝ S 2 := by
        simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one]
          using (h 2).1
  have hup2 : Metric.thickness ℝ S 2 ≤ ((2 * C₀ : NNReal) : ℝ) * (a : ℝ) := by
    calc
      Metric.thickness ℝ S 2 ≤ (C₀ : ℝ) * (a : ℝ) := by
        simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one]
          using (h 2).2
      _ ≤ ((2 * C₀ : NNReal) : ℝ) * (a : ℝ) := by
        rw [hcast]
        nlinarith [mul_nonneg hC₀ge ha]
  intro k
  fin_cases k
  · constructor
    · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using hlow0
    · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using hup0
  · constructor
    · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using hlow1
    · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using hup1
  · constructor
    · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using hlow2
    · simpa [Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one] using hup2

/-- **The doubled geometric constant is still absorbed by the enclosure constant of (C4)**:
`C_{lem:prism3DEnclosureVolume}(2 C₀) ≤ C_{lem:ml2plankpresentation}(C₀)`.

`48 (2 C₀)^6 = 3072 C₀^6 ≤ 2^20 C₀^6 ≤ max 1 (2^20 C₀^6)`. This is why the two-family split of
`Kakeya.VeryNotSticky.plankFamilyEnclosure` can run its geometry at `2 C₀` while its selection
keeps the constants of (C4): no downstream constant and no downstream exponent moves. -/
theorem enclosureVolumeConstant_two_le_plankEnclosureConstant (C₀ : NNReal) :
    Prism3D.enclosureVolumeConstant (2 * C₀) ≤ plankEnclosureConstant C₀ := by
  unfold Prism3D.enclosureVolumeConstant plankEnclosureConstant
  refine le_trans ?_ (le_max_right _ _)
  rw [mul_pow]
  calc
    48 * (2 ^ 6 * C₀ ^ 6) = (48 * 2 ^ 6) * C₀ ^ 6 := by ring
    _ ≤ 2 ^ 20 * C₀ ^ 6 := by
      gcongr
      norm_num

/-- **The enlarged bodies are localized in the doubled ball** (blueprint
`lem:ml2plankEnlargedBall`).

A body of `𝕎'_B` lies in `B̄(ctr, r₁)` by (C4) and its enlargement is by at most `C₀ a`, so the
enlargement lies in `B̄(ctr, r₁ + C₀ a)`; and `C₀ a ≤ C₀ b ≤ r₁` by the obligation (O1)
`C₀ b ≤ r₁`, so `B̄(ctr, 2 r₁)` contains it. This is the whole reason the plank presentation
normalizes by `2 r₁`: the enlargements do *not* fit in `B̄(ctr, r₁)`, and the long half-width of
a `Kakeya.Plank` is fixed at `1`, so no choice of the plank dimensions could compensate. -/
theorem enlarged_subset_closedBall {C₀ a r₁ ρ : NNReal} {ctr : E₃} {W V : ConvexSpaceBody E₃}
    (hin : (W.carrier : Set E₃) ⊆ closedBall ctr (r₁ : ℝ))
    (hV : (V.carrier : Set E₃) ⊆ Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) (W.carrier : Set E₃))
    (hsum : r₁ + C₀ * a ≤ ρ) :
    (V.carrier : Set E₃) ⊆ closedBall ctr (ρ : ℝ) := by
  have hs0 : 0 ≤ (C₀ : ℝ) * (a : ℝ) := by positivity
  have hr0 : 0 ≤ (r₁ : ℝ) := NNReal.coe_nonneg r₁
  have hle : (C₀ : ℝ) * (a : ℝ) + (r₁ : ℝ) ≤ (ρ : ℝ) := by
    have hle' : (r₁ : ℝ) + (C₀ : ℝ) * (a : ℝ) ≤ (ρ : ℝ) := by
      exact_mod_cast hsum
    linarith
  calc
    (V.carrier : Set E₃) ⊆ Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) (W.carrier : Set E₃) := hV
    _ ⊆ Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) (closedBall ctr (r₁ : ℝ)) := by
      exact Metric.cthickening_subset_of_subset ((C₀ : ℝ) * (a : ℝ)) hin
    _ ⊆ closedBall ctr ((C₀ : ℝ) * (a : ℝ) + (r₁ : ℝ)) := by
      rw [cthickening_closedBall hs0 hr0 ctr]
    _ ⊆ closedBall ctr (ρ : ℝ) := closedBall_subset_closedBall hle

/-- **The enlarged rescaled family has the same coordinate spread** (blueprint
`lem:ml2plankEnlargedSpread`).

At the normalization `ρ ≥ 2 r₁` the enlargement is invisible in the plank dimensions: the
geometric body has spread `≤ 2 C₀ a` in the frame direction `0` and the enlargement adds
`2 C₀ a`, so the enlarged body has spread `≤ 4 C₀ a`, which after division by `ρ ≥ 2 r₁` is at
most `2 (C₀ a / r₁) = 2 a'`. The same computation in direction `1` uses `a ≤ b` to absorb the
enlargement into `2 b'`. The half-widths `a' = C₀ a / r₁` and `b' = C₀ b / r₁` of the
presentation are therefore *unchanged* by the passage to the enlarged bodies. -/
theorem plankRescaledFamilyEnlarged_spread {ω : Type*} (bodies' : Finset ω)
    (Wb V : ω → ConvexSpaceBody E₃) {C₀ a b r₁ ρ : NNReal} (hC₀ : 1 ≤ C₀) (hab : a ≤ b)
    (hr₁ : 0 < r₁) (hρ : 0 < ρ) (hρ2 : 2 * r₁ ≤ ρ) (ctr : E₃)
    (hthick : ∀ j ∈ bodies',
      HasThicknesses ((Wb j).carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a])
    (hV : ∀ j ∈ bodies', ((V j).carrier : Set E₃) ⊆
      Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) ((Wb j).carrier : Set E₃)) :
    ∀ j ∈ bodies',
      ∀ x ∈ (((V j).plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne')).carrier : Set E₃),
      ∀ u ∈ (((V j).plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne')).carrier : Set E₃),
        |(bodyFrame (Wb j)).repr (x - u) 0| ≤ 2 * ((C₀ * a / r₁ : NNReal) : ℝ) ∧
        |(bodyFrame (Wb j)).repr (x - u) 1| ≤ 2 * ((C₀ * b / r₁ : NNReal) : ℝ) := by
  intro j hj x hx u hu
  have hr₁' : (0 : ℝ) < (r₁ : ℝ) := NNReal.coe_pos.mpr hr₁
  have hρ' : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  have hρ2' : 2 * (r₁ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ2
  have h2r₁' : (0 : ℝ) < 2 * (r₁ : ℝ) := by positivity
  have hinv : (ρ : ℝ)⁻¹ ≤ (2 * (r₁ : ℝ))⁻¹ := by
    exact (inv_le_inv₀ hρ' h2r₁').2 hρ2'
  have hC₀a_nonneg : (0 : ℝ) ≤ (C₀ : ℝ) * (a : ℝ) := by positivity
  have hcarrier : (((V j).plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne')).carrier : Set E₃)
      = plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne') '' ((V j).carrier : Set E₃) := by
    simp [ConvexSpaceBody.plankRescale]
  rw [hcarrier] at hx hu
  rcases hx with ⟨w₁, hw₁, hxeq⟩
  rcases hu with ⟨w₂, hw₂, hueq⟩
  have hdiff : x - u = (ρ : ℝ)⁻¹ • (w₁ - w₂) := by
    rw [← hxeq, ← hueq]
    rw [plankRescale_apply ctr (NNReal.coe_ne_zero.mpr hρ.ne') w₁]
    rw [plankRescale_apply ctr (NNReal.coe_ne_zero.mpr hρ.ne') w₂]
    rw [← smul_sub]
    congr 1
    abel
  have hcoords : ∀ i : Fin 3, (bodyFrame (Wb j)).repr (x - u) i
      = (ρ : ℝ)⁻¹ * (bodyFrame (Wb j)).repr (w₁ - w₂) i := by
    intro i
    rw [hdiff]
    rw [map_smul]
    rfl
  have hM0 : ∀ w₁' ∈ ((Wb j).carrier : Set E₃), ∀ w₂' ∈ ((Wb j).carrier : Set E₃),
      |(bodyFrame (Wb j)).repr (w₁' - w₂') 0| ≤ 2 * ((C₀ : ℝ) * (a : ℝ)) := by
    intro w₁' hw₁' w₂' hw₂'
    have hrev : Fin.rev (0 : Fin 3) = 2 := by decide
    have hth : Metric.thickness ℝ ((Wb j).carrier : Set E₃) (2 : Fin 3) ≤ (C₀ : ℝ) * (a : ℝ) := by
      simpa using (hthick j hj (2 : Fin 3)).2
    calc
      |(bodyFrame (Wb j)).repr (w₁' - w₂') 0|
          ≤ 2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (Fin.rev 0) :=
              abs_bodyFrame_repr_sub_le (Wb j) hw₁' hw₂' 0
      _ = 2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (2 : Fin 3) := by rw [hrev]
      _ ≤ 2 * ((C₀ : ℝ) * (a : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hth (by norm_num)
  have hM1 : ∀ w₁' ∈ ((Wb j).carrier : Set E₃), ∀ w₂' ∈ ((Wb j).carrier : Set E₃),
      |(bodyFrame (Wb j)).repr (w₁' - w₂') 1| ≤ 2 * ((C₀ : ℝ) * (b : ℝ)) := by
    intro w₁' hw₁' w₂' hw₂'
    have hrev : Fin.rev (1 : Fin 3) = 1 := by decide
    have hth : Metric.thickness ℝ ((Wb j).carrier : Set E₃) (1 : Fin 3) ≤ (C₀ : ℝ) * (b : ℝ) := by
      simpa using (hthick j hj (1 : Fin 3)).2
    calc
      |(bodyFrame (Wb j)).repr (w₁' - w₂') 1|
          ≤ 2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (Fin.rev 1) :=
              abs_bodyFrame_repr_sub_le (Wb j) hw₁' hw₂' 1
      _ = 2 * Metric.thickness ℝ ((Wb j).carrier : Set E₃) (1 : Fin 3) := by rw [hrev]
      _ ≤ 2 * ((C₀ : ℝ) * (b : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hth (by norm_num)
  have hbnd0 : |(bodyFrame (Wb j)).repr (w₁ - w₂) 0| ≤ 4 * ((C₀ : ℝ) * (a : ℝ)) := by
    have h := abs_repr_sub_le_of_mem_cthickening (bodyFrame (Wb j))
      hC₀a_nonneg (0 : Fin 3) hM0 (hV j hj hw₁) (hV j hj hw₂)
    linarith
  have hbnd1 : |(bodyFrame (Wb j)).repr (w₁ - w₂) 1| ≤ 4 * ((C₀ : ℝ) * (b : ℝ)) := by
    have h := abs_repr_sub_le_of_mem_cthickening (bodyFrame (Wb j))
      hC₀a_nonneg (1 : Fin 3) hM1 (hV j hj hw₁) (hV j hj hw₂)
    have hle : (C₀ : ℝ) * (a : ℝ) ≤ (C₀ : ℝ) * (b : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hab : (a : ℝ) ≤ (b : ℝ))
        (NNReal.coe_nonneg C₀)
    linarith
  constructor
  · calc
      |(bodyFrame (Wb j)).repr (x - u) 0|
          = (ρ : ℝ)⁻¹ * |(bodyFrame (Wb j)).repr (w₁ - w₂) 0| := by
              rw [hcoords 0, abs_mul, abs_of_nonneg (inv_nonneg.mpr hρ'.le)]
      _ ≤ (ρ : ℝ)⁻¹ * (4 * ((C₀ : ℝ) * (a : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hbnd0 (inv_nonneg.mpr hρ'.le)
      _ ≤ (2 * (r₁ : ℝ))⁻¹ * (4 * ((C₀ : ℝ) * (a : ℝ))) := by
              exact mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = 2 * ((C₀ * a / r₁ : NNReal) : ℝ) := by
              rw [NNReal.coe_div, NNReal.coe_mul]
              field_simp [hr₁'.ne']
              ring
  · calc
      |(bodyFrame (Wb j)).repr (x - u) 1|
          = (ρ : ℝ)⁻¹ * |(bodyFrame (Wb j)).repr (w₁ - w₂) 1| := by
              rw [hcoords 1, abs_mul, abs_of_nonneg (inv_nonneg.mpr hρ'.le)]
      _ ≤ (ρ : ℝ)⁻¹ * (4 * ((C₀ : ℝ) * (b : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hbnd1 (inv_nonneg.mpr hρ'.le)
      _ ≤ (2 * (r₁ : ℝ))⁻¹ * (4 * ((C₀ : ℝ) * (b : ℝ))) := by
              exact mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = 2 * ((C₀ * b / r₁ : NNReal) : ℝ) := by
              rw [NNReal.coe_div, NNReal.coe_mul]
              field_simp [hr₁'.ne']
              ring

/-- **The enlarged rescaled family lies in the unit ball** (blueprint
`lem:ml2plankEnlargedRescaledBall`).

The family-level packaging of `Kakeya.VeryNotSticky.scale_le_of_hasThicknesses` and
`Kakeya.VeryNotSticky.enlarged_subset_closedBall`, in the two shapes the plank presentation
consumes: the containment of each enlarged carrier in the closed `C₀ a`-neighbourhood of the
geometric body — which is also the hypothesis `hV` of
`Kakeya.VeryNotSticky.plankRescaledFamilyEnlarged_spread` — and the localization of the
rescaled enlarged carriers in `B̄(0,1)`.

The hypothesis on `V` is the upper half of the enlargement sandwich of
`Kakeya.ThinCase.ThinBall`, stated at the body level so that no formula for `V` is needed. -/
theorem plankRescaledFamilyEnlarged_subset_closedBall {ω : Type*} (bodies' : Finset ω)
    (Wb V : ω → ConvexSpaceBody E₃) {C₀ a b r₁ ρ : NNReal}
    (_hr₁ : 0 < r₁) (hρ : 0 < ρ) (hρsum : r₁ + C₀ * a ≤ ρ) (ctr : E₃)
    (hin : ∀ j ∈ bodies', ((Wb j).carrier : Set E₃) ⊆ closedBall ctr (r₁ : ℝ))
    (hthick : ∀ j ∈ bodies', HasThicknesses ((Wb j).carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a])
    (hV : ∀ j ∈ bodies', V j ≤ (Wb j).cthickening (Wb j).scale) :
    (∀ j ∈ bodies', ((V j).carrier : Set E₃) ⊆
        Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) ((Wb j).carrier : Set E₃)) ∧
      ∀ j ∈ bodies',
        (((V j).plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne')).carrier : Set E₃)
          ⊆ closedBall (0 : E₃) 1 := by
  have hVCa : ∀ j ∈ bodies',
      ((V j).carrier : Set E₃) ⊆
        Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) ((Wb j).carrier : Set E₃) := by
    intro j hj
    calc
      ((V j).carrier : Set E₃)
          ⊆ (((Wb j).cthickening (Wb j).scale).carrier : Set E₃) := by
        exact SetLike.coe_subset_coe.mpr (hV j hj)
      _ ⊆ Metric.cthickening ((C₀ : ℝ) * (a : ℝ)) ((Wb j).carrier : Set E₃) := by
        exact Metric.cthickening_mono (scale_le_of_hasThicknesses (Wb j) (hthick j hj))
          (Wb j).carrier
  have hVρ : ∀ j ∈ bodies', ((V j).carrier : Set E₃) ⊆ closedBall ctr (ρ : ℝ) := by
    intro j hj
    exact enlarged_subset_closedBall (hin := hin j hj) (hV := hVCa j hj) (hsum := hρsum)
  constructor
  · exact hVCa
  · exact plankRescaledFamily_subset_closedBall (bodies' := bodies') (Wb := V) hρ ctr hVρ

/-- **The enclosing plank has comparable volume, at the doubled scale** (blueprint
`lem:ml2plankEnclosureVolumeDouble`).

`Kakeya.VeryNotSticky.plankEnclosureVolume` read at the doubled comparison constant `2 C₀` and
the doubled scale `2 r₁`, which is how the plank presentation must read it once the enlarged
carriers force the normalization `2 r₁`.

**Nothing moves.** The hypotheses `haa'`, `hbb'` are the *original* ones, at `C₀` and `r₁`,
because `2 C₀ · (a / (2 r₁)) = C₀ a / r₁`; and the constant in the conclusion is the
*original* `plankEnclosureConstant C₀`, because
`Kakeya.VeryNotSticky.enclosureVolumeConstant_two_le_plankEnclosureConstant` absorbs
`C_{lem:prism3DEnclosureVolume}(2 C₀) = 3072 C₀^6` into `max 1 (2^20 C₀^6)`. -/
theorem plankEnclosureVolume_double {C₀ a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    (hρ : (0 : NNReal) < 2 * r₁) (ctr : E₃) (W : ConvexSpaceBody E₃)
    (hthick : HasThicknesses (W.carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a])
    {a' b' : NNReal} (haa' : (a' : ℝ) = C₀ * ((a : ℝ) / r₁))
    (hbb' : (b' : ℝ) = C₀ * ((b : ℝ) / r₁))
    (hab' : a' ≤ b') (hb1' : b' ≤ 1) (P : Plank a' b' hab' hb1') :
    volume (P.carrier : Set E₃) ≤ (plankEnclosureConstant C₀ : ENNReal) *
      volume (((W.plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne')).carrier : Set E₃)) := by
  have h2C₀ : (1 : NNReal) ≤ 2 * C₀ := by
    have hC₀₁ : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
    have hC₀ge : (0 : ℝ) ≤ (C₀ : ℝ) := le_trans zero_le_one hC₀₁
    have h₂ : ((2 * C₀ : NNReal) : ℝ) = 2 * (C₀ : ℝ) := by norm_num
    have h2C₀R : (1 : ℝ) ≤ ((2 * C₀ : NNReal) : ℝ) := by
      rw [h₂]
      nlinarith
    exact_mod_cast h2C₀R
  have hCe : Prism3D.enclosureVolumeConstant (2 * C₀) ≤ plankEnclosureConstant C₀ :=
    enclosureVolumeConstant_two_le_plankEnclosureConstant C₀
  have hthick2 : HasThicknesses (W.carrier : Set E₃) (2 * C₀)
      ![((2 * r₁ : NNReal) : ℝ), (b : ℝ), (a : ℝ)] :=
    hasThicknesses_double hC₀ hthick
  have hr₁R : (0 : ℝ) < (r₁ : ℝ) := NNReal.coe_pos.mpr hr₁
  have hr₁ne : (r₁ : ℝ) ≠ 0 := hr₁R.ne'
  have haa2 : (a' : ℝ) = ((2 * C₀ : NNReal) : ℝ) * ((a : ℝ) / ((2 * r₁ : NNReal) : ℝ)) := by
    rw [haa']
    push_cast
    field_simp [hr₁ne]
  have hbb2 : (b' : ℝ) = ((2 * C₀ : NNReal) : ℝ) * ((b : ℝ) / ((2 * r₁ : NNReal) : ℝ)) := by
    rw [hbb']
    push_cast
    field_simp [hr₁ne]
  exact plankEnclosureVolume (C₀ := 2 * C₀) (a := a) (b := b) (r₁ := 2 * r₁)
    (Ce := plankEnclosureConstant C₀) h2C₀ hρ hCe ctr W hthick2 haa2 hbb2 hab' hb1' P

/-- **Density of the plank family, at the doubled scale** (blueprint
`lem:ml2plankDensityDouble`).

`Kakeya.VeryNotSticky.plankDensity` read at the doubled comparison constant `2 C₀` and the
doubled scale `2 r₁`, exactly as `Kakeya.VeryNotSticky.plankEnclosureVolume_double` reads the
volume comparison, and with the same two cancellations: the plank dimensions and the enclosure
constant are the original ones. This is what keeps the field
`Kakeya.VeryNotSticky.PlankPresentationData.hdens` stated at `plankEnclosureConstant C₀`, and
hence keeps every downstream exponent fixed. -/
theorem plankDensity_double {C₀ a b r₁ : NNReal} (hC₀ : 1 ≤ C₀) (hr₁ : 0 < r₁)
    (hρ : (0 : NNReal) < 2 * r₁) (_hab : a ≤ b) (ctr : E₃)
    {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E₃)
    (hthick : ∀ j ∈ s, HasThicknesses ((W j).carrier : Set E₃) C₀ ![(r₁ : ℝ), b, a])
    {a' b' : NNReal} (haa' : (a' : ℝ) = C₀ * ((a : ℝ) / r₁))
    (hbb' : (b' : ℝ) = C₀ * ((b : ℝ) / r₁))
    (hab' : a' ≤ b') (hb1' : b' ≤ 1) (P : ι → Plank a' b' hab' hb1')
    (hsub : ∀ j ∈ s, plankRescale ctr (NNReal.coe_ne_zero.mpr hρ.ne') ''
      ((W j).carrier : Set E₃) ⊆ (P j).carrier) :
    maxDensity s (fun j => (P j).toConvexSpaceBody)
      ≤ (plankEnclosureConstant C₀ : ENNReal) * maxDensity s W := by
  have h2C₀ : (1 : NNReal) ≤ 2 * C₀ := by
    exact le_trans (by norm_num : (1 : NNReal) ≤ 2) (by
      calc
        2 ≤ C₀ * 2 := le_mul_of_one_le_left (by norm_num : (0 : NNReal) ≤ 2) hC₀
        _ = 2 * C₀ := by rw [mul_comm])
  have hCe : Prism3D.enclosureVolumeConstant (2 * C₀) ≤ plankEnclosureConstant C₀ :=
    enclosureVolumeConstant_two_le_plankEnclosureConstant C₀
  have hthick2 : ∀ j ∈ s,
      HasThicknesses ((W j).carrier : Set E₃) (2 * C₀)
        ![((2 * r₁ : NNReal) : ℝ), (b : ℝ), (a : ℝ)] := fun j hj =>
    hasThicknesses_double hC₀ (hthick j hj)
  have hr₁R : (0 : ℝ) < (r₁ : ℝ) := NNReal.coe_pos.mpr hr₁
  have hr₁ne : (r₁ : ℝ) ≠ 0 := hr₁R.ne'
  have haa2 : (a' : ℝ) = ((2 * C₀ : NNReal) : ℝ) * ((a : ℝ) / ((2 * r₁ : NNReal) : ℝ)) := by
    rw [haa']
    push_cast
    field_simp [hr₁ne]
  have hbb2 : (b' : ℝ) = ((2 * C₀ : NNReal) : ℝ) * ((b : ℝ) / ((2 * r₁ : NNReal) : ℝ)) := by
    rw [hbb']
    push_cast
    field_simp [hr₁ne]
  exact plankDensity (C₀ := 2 * C₀) (a := a) (b := b) (r₁ := 2 * r₁)
    (Ce := plankEnclosureConstant C₀) h2C₀ hρ hCe _hab ctr s W hthick2 haa2 hbb2 hab' hb1' P hsub

/-- `r₁^η ≤ Csel⁻¹` in `ℝ`, from `r₁ = δ^exscal` and the threshold `Csel ≤ δ^(-(exscal·η))`.

This is the interface between `hr₁`, `hthr` and the multiplicative-`ℝ≥0` rpow comparison
that `plankSubfamilyMult` reduces to. All three quantities are positive (`δ`, `r₁`, `Csel`),
so the real `rpow` arithmetic is unproblematic. -/
private lemma plankSubfamilyMult_rpow_le {δ r₁ Csel : NNReal} {η exscal : ℝ}
    (hδ : 0 < δ) (hCsel : 1 ≤ Csel) (hr₁ : (r₁ : ℝ) = (δ : ℝ) ^ exscal)
    (_hr₁pos : 0 < r₁) (hthr : (Csel : ℝ) ≤ (δ : ℝ) ^ (-(exscal * η))) :
    (r₁ : ℝ) ^ η ≤ (Csel : ℝ)⁻¹ := by
  have hδge0 : (0 : ℝ) ≤ (δ : ℝ) := by positivity
  have hCselpos : (0 : ℝ) < (Csel : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast hCsel : (1 : ℝ) ≤ (Csel : ℝ))
  calc
    (r₁ : ℝ) ^ η = (δ : ℝ) ^ (exscal * η) := by
      rw [hr₁]
      rw [Real.rpow_mul hδge0 exscal η]
    _ = ((δ : ℝ) ^ (-(exscal * η)))⁻¹ := by
      rw [← Real.rpow_neg hδge0 (-(exscal * η))]
      congr 1
      rw [neg_neg]
    _ ≤ (Csel : ℝ)⁻¹ := by
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (δ : ℝ)) (-(exscal * η)))
        hCselpos).mpr hthr

/-- `(δ/r₁)^(-η) ≤ Csel⁻¹ * δ^(-η)` in `ℝ≥0` (multiplicative `rpow`).

The two `rpow`s are `NNReal.rpow` with real exponents. The proof reduces to `ℝ` via
`NNReal.coe_le_coe` and the `coe_rpow`/`coe_div`/`coe_mul` casts, then uses
`plankSubfamilyMult_rpow_le` together with `(a/b)^(-η) = a^(-η) * b^η` for positive `a, b`. -/
private lemma plankSubfamilyMult_nn {δ r₁ Csel : NNReal} {η exscal : ℝ}
    (hδ : 0 < δ) (hCsel : 1 ≤ Csel) (hr₁ : (r₁ : ℝ) = (δ : ℝ) ^ exscal)
    (hr₁pos : 0 < r₁) (hthr : (Csel : ℝ) ≤ (δ : ℝ) ^ (-(exscal * η))) :
    (δ / r₁ : NNReal) ^ (-η) ≤ Csel⁻¹ * (δ : NNReal) ^ (-η) := by
  rw [← NNReal.coe_le_coe]
  norm_cast
  have hδge0 : (0 : ℝ) ≤ (δ : ℝ) := by positivity
  have hr₁ge0 : (0 : ℝ) ≤ (r₁ : ℝ) := by positivity
  have hbη : (r₁ : ℝ) ^ η ≤ (Csel : ℝ)⁻¹ :=
    plankSubfamilyMult_rpow_le hδ hCsel hr₁ hr₁pos hthr
  calc
    ((δ : ℝ) / (r₁ : ℝ)) ^ (-η) = (δ : ℝ) ^ (-η) * (r₁ : ℝ) ^ η := by
      rw [div_eq_mul_inv]
      rw [Real.mul_rpow hδge0 (inv_nonneg.mpr hr₁ge0)]
      have hrr : ((r₁ : ℝ)⁻¹) ^ (-η) = (r₁ : ℝ) ^ η := by
        rw [Real.inv_rpow hr₁ge0 (-η)]
        rw [← Real.rpow_neg hr₁ge0 (-η), neg_neg]
      rw [hrr]
    _ ≤ ((Csel : ℝ)⁻¹) * (δ : ℝ) ^ (-η) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hbη (Real.rpow_nonneg hδge0 (-η))

/-- **The selected subfamily still has large multiplicity** (blueprint
`lem:ml2plankSubfamilyMult`).

Passing to the `(C^{sel})⁻¹`-refinement `(𝒮*, Y_𝒫)` of `(𝒫, Y_𝒫)` costs the factor `C^{sel}`
(`ShadedBody.IsCRefinement.mul_multiplicity_le`, which carries no positivity side condition, so
this step creates no new call on obligation (O2)), and the available slack between `δ'^{-η}`
and `δ^{-η}` is exactly `r₁^{-η} = δ^{-exscal η}`.

The threshold `C^{sel} ≤ δ^{-exscal η}` is a **genuine extra assumption**: "a fixed constant is
eventually beaten by a power of `δ`" is a smallness threshold on `δ` and not slack. It is a
fixed-scale condition of the same shape as the clauses of Configuration `hyp:ml2scale`, its
left-hand side being fixed once `C₀` is, hence before `δ`, and its right-hand side a positive
power of `δ`; and it is spent with nothing to spare, which is why its exponent is
`exscal · η`.

`hCsel : 1 ≤ Csel` is not a restriction: this statement is the abstract form of the blueprint
lemma, whose `Csel` is the concrete `Kakeya.VeryNotSticky.plankSelectionConstant C₀ = D + 1`,
and `one_le_plankSelectionConstant` discharges it. It cannot be dropped: for `Csel = 0` one has
`Csel⁻¹ = 0` in `NNReal`, so `href` holds vacuously (`sel = ∅` is admissible) while the
conclusion still demands positive multiplicity. -/
theorem plankSubfamilyMult {ι : Type*} {sel s : Finset ι} {YP : ι → ShadedBody E₃}
    {δ r₁ Csel : NNReal} {η exscal : ℝ} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (_hη : 0 < η)
    (hCsel : 1 ≤ Csel)
    (hr₁ : (r₁ : ℝ) = (δ : ℝ) ^ exscal) (hr₁pos : 0 < r₁)
    (hmul : (δ : ENNReal) ^ (-η) ≤ multiplicity s YP)
    (href : IsCRefinement sel YP s YP Csel⁻¹)
    (hthr : (Csel : ℝ) ≤ (δ : ℝ) ^ (-(exscal * η))) :
    ((δ / r₁ : NNReal) : ENNReal) ^ (-η) ≤ multiplicity sel YP := by
  have hmult : ((Csel⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (-η) ≤
      multiplicity sel YP := by
    calc
      ((Csel⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (-η)
          ≤ ((Csel⁻¹ : NNReal) : ENNReal) * multiplicity s YP := by
            exact mul_le_mul_right hmul ((Csel⁻¹ : NNReal) : ENNReal)
      _ ≤ multiplicity sel YP := href.mul_multiplicity_le
  have hineq : ((δ / r₁ : NNReal) : ENNReal) ^ (-η) ≤
      ((Csel⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (-η) := by
    have hδr : δ / r₁ ≠ 0 := by positivity
    have hδ0 : δ ≠ 0 := by positivity
    rw [← ENNReal.coe_rpow_of_ne_zero hδr (-η),
        ← ENNReal.coe_rpow_of_ne_zero hδ0 (-η)]
    rw [← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr (plankSubfamilyMult_nn hδ hCsel hr₁ hr₁pos hthr)
  exact le_trans hineq hmult

end Kakeya.VeryNotSticky

end
