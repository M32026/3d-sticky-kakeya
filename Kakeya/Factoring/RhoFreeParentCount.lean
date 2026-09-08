/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.ParentCountHypothesis

/-!
# No `ρ`-free outer-plank parent count exists under the hypotheses of GWZ Proposition 6.6(A)

The outer plank non-concentration step of `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`
runs through a count of the coarse parent labels that own a fine leaf inside one plank-shaped
test body.  With coarse essential distinctness that count is an absolute constant
(`Kakeya.edParentCount.card_assignedParents_le_of_subset_dilate`); coarse essential distinctness
is not available to Main Lemma 1, and from `Tube.HasBoundedOverlap` alone the count is
`Co · ρ ^ (-5)` (`Kakeya.card_assignedParents_le_of_boundedOverlap`), which no ledger entry of
Main Lemma 1 can absorb.

This file settles the remaining question: **is there a `ρ`-free count — a constant, or a polylog
in `1/ρ` — available from the hypothesis package that GWZ Proposition 6.6(A) actually carries?**

The answer is **no**, and the refutation uses the *whole* package, uniformity included.

## What is new here relative to `Kakeya.not_card_assignedParents_le_const_of_boundedOverlap_of_full`

That theorem refutes the constant count under "ship's 6.6(A) package minus only its uniformity
clause": nonemptiness, containment in `B₁`, leaf-scale essential distinctness, fullness at an
arbitrary threshold, a parent family, and `Tube.HasBoundedOverlap` at the sharpest constant `1`.
The uniformity clause was the one hypothesis left untested, and it was the only remaining
candidate for a hypothesis that might bound the count.

`Kakeya.nonempty_isFlatPrismUniform_of_card_le` closes that gap, and it does so structurally
rather than by a geometric construction: **every family of at most `C` injectively indexed
`σ`-tubes is `C`-uniform**, at every grid length, via the identity hierarchy — each member is its
own node at every grid scale, the node being the member's own tube rescaled to the grid radius.
Nestedness is automatic (the assignment is the identity), the nodes are nested because the grid
radius is antitone, `Kakeya.IsFlatPrismUniformTubeSet.boundedOverlap` holds because the counted
set is a subset of the index set, and every class, being a singleton, meets both branching
brackets at `branchingN = localN = 1`.

That is the whole reason uniformity cannot rescue the count.  The uniformity constant `Cunif` of
GWZ Proposition 6.6(A) is not a dimensional constant: it is quantified with the single constraint
`Cunif ≤ σ ^ (-η')`.  So any family with at most `σ ^ (-η')` members satisfies the uniformity
clause *for free*, and `σ ^ (-η') → ∞`.  Uniformity is therefore blind to configurations of
subpolynomial cardinality — and the axial pencil, rescaled to have `σ ^ (-η')` leaves, is such a
configuration.

## The configuration

`Kakeya.rhoFreeCex` re-parametrises the repository's axial pencil
(`Kakeya.ml1Boot.essDistinctCex.leaf`, fully shaded by `Kakeya.fullLeaf`) so that its leaf count
fits under the uniformity budget:

* `cnt n = 2 ^ n` leaves;
* coarse scale `par n = (1/2) ^ (n + 10)`, so that `cnt n = (par n)⁻¹ / 2 ^ 10`;
* leaf scale `lea η n = (1/2) ^ (lexp η n)` with `lexp η n = max (2 n + 12) ⌈n / η⌉`, which makes
  the pencil's transverse spread fit the coarse radius *and* makes `cnt n ≤ (lea η n) ^ (-η)`.

Every clause of `Kakeya.IsFlatPrismFamily` holds at `Cunif = cnt n`, the parent containment holds
at dilation `1` (each leaf sits in its own rescaled parent, ship's form of the hypothesis), every
one of the `cnt n` parent labels is occupied inside the `4`-dilate of a *single* coarse tube, and
the count is therefore `cnt n = (par n)⁻¹ / 2 ^ 10`.

## The verdict

* `Kakeya.not_card_assignedParents_le_const_of_isFlatPrismFamily`: no constant bounds the count,
  at any plank comparability constant `Cw ≥ 2`.
* `Kakeya.exists_isFlatPrismFamily_rhoInv_le_card_assignedParents`: the count is at least
  `ρ⁻¹ / 2 ^ 10` on the configurations above — the sharpest lower bound available, and it
  brackets the truth with `Kakeya.card_assignedParents_le_of_boundedOverlap`'s `ρ ^ (-5)`.

So GWZ Proposition 6.6(A) *as architected* cannot be run off a `ρ`-free outer-plank count: any
sound count under its hypotheses carries a positive power of `ρ`, and the parameter architecture
of Main Lemma 1 (blueprint `note:ml1RhoIsATypeIndex`) charges every constant against
`σ ^ (-eFund)` with `eFund ≤ ε' / 512`, which no positive power of `ρ` fits.  Closing 6.6(A)
requires a hypothesis strictly outside the present package, not a sharper estimate inside it.

## Leaf-scale essential distinctness does not help

The refutation keeps leaf-scale essential distinctness throughout — it is the `essDistinct` field
of `Kakeya.IsFlatPrismFamily` and the pencil satisfies it
(`Kakeya.ml1Boot.essDistinctCex.isEssentiallyDistinct_leaf`, the leaves being pairwise disjoint).
So the leaf-scale hypothesis that GWZ do supply (`section2.tex:1093--1139`: essential distinctness
"is required and supplied at the leaf scale `δ`, and never at the parent scale") is present in
every counterexample here and does not bound the parent count.  The asymmetry with
`Kakeya.flatPrismOccupiedParents_le_of_boundedOverlap`, which *is* constant, is entirely the
scale hypothesis `bSmall ≤ b ≤ D · ρ` of that lemma: it forces `1 ≤ Ctest · ρ`, i.e. it runs only
where the coarse scale is bounded below by a constant.  The outer plank step runs at arbitrary
`σ ≤ ρ ≤ 1` and has no such lower bound on `ρ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

section Uniformity

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every grid radius at an index `k ≤ N` is at least the leaf radius. -/
theorem le_gridScale_of_le {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {N k : ℕ} (hk : k ≤ N) :
    σ ≤ Tube.gridScale σ N k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hk0 : k = 0 := by omega
    subst hk0
    simpa [Tube.gridScale] using hσ1
  · calc σ = Tube.gridScale σ N N := (Tube.gridScale_self σ hN).symm
      _ ≤ Tube.gridScale σ N k := Tube.gridScale_antitone hσ0 hσ1 N hk

/-- **A family of at most `C` injectively indexed `σ`-tubes is `C`-uniform**, at every grid
length `N` and for every `C ≥ 1` above its cardinality.

The hierarchy is the identity one: every member is its own node at every grid scale, the node
being the member's own tube rescaled to the grid radius `ρ_k`.

* `le_tube_assign` is `Tube.le_rescale`, which applies because `σ ≤ ρ_k` for `k ≤ N`;
* `nested` is trivial, the assignment being the identity;
* `tube_nested` is `Tube.rescale_le_rescale_of_radius_le` along the antitone grid;
* `tube_injOn` is the hypothesis `hinj`, transported through `Tube.rescale`, which
  preserves the endpoints;
* `boundedOverlap` holds because the counted set is a *subset of the index set*, whose
  cardinality is `≤ C` by hypothesis — this is the only place `hcard` is used;
* `card_class_le` holds because every class is a singleton, at `branchingN = 1`.

The shading clauses of `Kakeya.IsFlatPrismUniform` are then immediate at `localN = 1`, the shade
classes being contained in the (singleton) cover classes.

This is the reason the uniformity clause of GWZ Proposition 6.6(A) cannot bound the outer-plank
parent count: `Cunif` there is constrained only by `Cunif ≤ σ ^ (-η')`, so every family of at most
`σ ^ (-η')` members is uniform for free. -/
theorem nonempty_isFlatPrismUniform_of_card_le {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedTube σ E) (N : ℕ) {C : NNReal} (hC : 1 ≤ C)
    (hcard : (s.card : NNReal) ≤ C)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (V i).toTube.x = (V j).toTube.x →
      (V i).toTube.y = (V j).toTube.y → i = j) :
    Nonempty (IsFlatPrismUniform s V N C) := by
  classical
  let gcs : Tube.GridCoverSystem s (fun i => (V i).toTube) N :=
    { indexSet := fun _ => s
      assign := fun _ i => i
      tube := fun k i => (V i).toTube.rescale (Tube.gridScale σ N k)
      assign_mem := by intro k hk i hi; exact hi
      le_tube_assign := by
        intro k hk i hi
        exact Tube.le_rescale (V i).toTube (le_gridScale_of_le hσ0 hσ1 hk)
      nested := by intro k hk i hi j hj h; exact h
      tube_nested := by
        intro k hk i hi
        exact Tube.rescale_le_rescale_of_radius_le (V i).toTube
          (Tube.gridScale_antitone hσ0 hσ1 N (Nat.le_succ k)) }
  let utu : IsFlatPrismUniformTubeSet s (fun i => (V i).toTube) N C :=
    { cover := gcs
      branchingN := fun _ => 1
      tube_injOn := by
        intro k hk a ha b hb hab
        have hx : (V a).toTube.x = (V b).toTube.x := by
          have := congrArg Tube.x hab
          simpa [gcs, Tube.rescale] using this
        have hy : (V a).toTube.y = (V b).toTube.y := by
          have := congrArg Tube.y hab
          simpa [gcs, Tube.rescale] using this
        exact hinj a ha b hb hx hy
      boundedOverlap := by
        intro k hk W
        refine le_trans ?_ hcard
        exact_mod_cast Finset.card_filter_le _ _
      card_class_le := by
        intro k hk j hj
        have hs1 : Tube.coverClass s (gcs.assign k) j ⊆ ({j} : Finset ι) := by
          intro i hi
          simp only [Tube.coverClass, Finset.mem_filter] at hi
          simpa using hi.2
        have hcd : ((Tube.coverClass s (gcs.assign k) j).card : NNReal) ≤ 1 := by
          exact_mod_cast (Finset.card_le_card hs1).trans (by simp)
        simpa using hcd.trans (by simpa using hC) }
  exact ⟨{ tubeUniform := utu
           branchingN := fun _ => 1
           localN := fun _ _ => 1
           card_shadeClass_le := by
             intro x hx k hk i hi hxi
             have hsub := ShadedTube.shadeClass_subset s V (utu.cover.assign k)
               (utu.cover.assign k i) x
             have hsub2 : Tube.coverClass s (utu.cover.assign k) (utu.cover.assign k i)
                 ⊆ ({i} : Finset ι) := by
               intro z hz
               simp only [Tube.coverClass, Finset.mem_filter] at hz
               simpa [utu, gcs] using hz.2
             have hle : ((ShadedTube.shadeClass s V (utu.cover.assign k)
                 (utu.cover.assign k i) x).card : NNReal) ≤ 1 := by
               exact_mod_cast (Finset.card_le_card (hsub.trans hsub2)).trans (by simp)
             simpa using hle.trans (by simpa using hC)
           le_branchingN := by intro x hx k hk; simpa using hC }⟩

end Uniformity

/-! ### The re-parametrised axial pencil

The repository's pencil `Kakeya.ml1Boot.essDistinctCex.leaf` is run at the scales
`σ = 2 ^ (-8n)`, `ρ = 2 ^ (-(2n+9))`, `M = 2 ^ (2n+1)`, which makes `M ≍ σ ^ (-1/4)`: too many
leaves to fit under a uniformity budget `Cunif ≤ σ ^ (-η')` with small `η'`.  The scales below
keep `M ≍ ρ ^ (-1)` — the property that makes the count large — while pushing `σ` down until
`M ≤ σ ^ (-η)`. -/

namespace rhoFreeCex

/-- The number of leaves, equivalently of occupied coarse parent labels, at stage `n`. -/
def cnt (n : ℕ) : ℕ := 2 ^ n

/-- The coarse scale at stage `n`.  It is `2 ^ (-10) / cnt n`, so the count is `≍ ρ⁻¹`. -/
def par (n : ℕ) : NNReal := (1 / 2) ^ (n + 10)

/-- The exponent of the leaf scale at stage `n`, at uniformity/fullness budget `η`.  The first
term makes the pencil's transverse spread fit the coarse radius; the second makes the leaf count
fit the uniformity budget `Cunif ≤ σ ^ (-η)`. -/
def lexp (η : ℝ) (n : ℕ) : ℕ := max (2 * n + 12) ⌈(n : ℝ) / η⌉₊

/-- The leaf scale at stage `n`. -/
def lea (η : ℝ) (n : ℕ) : NNReal := (1 / 2) ^ (lexp η n)

theorem cnt_pos (n : ℕ) : 0 < cnt n := by
  unfold cnt; positivity

theorem par_pos (n : ℕ) : 0 < par n := by
  unfold par; positivity

theorem lea_pos (η : ℝ) (n : ℕ) : 0 < lea η n := by
  unfold lea; positivity

theorem lexp_ge (η : ℝ) (n : ℕ) : 2 * n + 12 ≤ lexp η n := le_max_left _ _

theorem lea_le_par (η : ℝ) (n : ℕ) : lea η n ≤ par n := by
  unfold lea par
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (le_trans (by omega) (lexp_ge η n))

theorem par_coe (n : ℕ) : (par n : ℝ) = (1 / 2 : ℝ) ^ (n + 10) := by
  unfold par; push_cast; ring

theorem lea_coe (η : ℝ) (n : ℕ) : (lea η n : ℝ) = (1 / 2 : ℝ) ^ (lexp η n) := by
  unfold lea; push_cast; ring

theorem cnt_coe (n : ℕ) : ((cnt n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
  unfold cnt; push_cast; ring

theorem half_mul_two (k : ℕ) : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
  rw [div_pow, one_pow]
  field_simp

theorem par_le_inv128 (n : ℕ) : (par n : ℝ) ≤ 1 / 128 := by
  rw [par_coe]
  calc (1 / 2 : ℝ) ^ (n + 10) ≤ (1 / 2 : ℝ) ^ 7 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 128 := by norm_num

theorem par_le_one (n : ℕ) : par n ≤ 1 := by
  unfold par
  exact pow_le_one₀ (by positivity) (by norm_num)

/-- **The pencil's axial spread fits inside `1/12`**, so all its leaves stay in `B₁`. -/
theorem axial_bd (n : ℕ) : 7 * (par n : ℝ) * (cnt n : ℝ) ≤ 1 / 12 := by
  rw [par_coe, cnt_coe]
  have h : (1 / 2 : ℝ) ^ (n + 10) * (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ 10 := by
    rw [pow_add, mul_comm ((1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ 10), mul_assoc, half_mul_two, mul_one]
  calc 7 * (1 / 2 : ℝ) ^ (n + 10) * (2 : ℝ) ^ n
      = 7 * ((1 / 2 : ℝ) ^ (n + 10) * (2 : ℝ) ^ n) := by ring
    _ = 7 * (1 / 2 : ℝ) ^ 10 := by rw [h]
    _ ≤ 1 / 12 := by norm_num

/-- **The pencil's transverse spread fits inside the coarse radius.** -/
theorem trans_bd (η : ℝ) (n : ℕ) : 3 * (lea η n : ℝ) * (cnt n : ℝ) ≤ (par n : ℝ) := by
  rw [lea_coe, cnt_coe, par_coe]
  have h1 : (1 / 2 : ℝ) ^ (lexp η n) ≤ (1 / 2 : ℝ) ^ (2 * n + 12) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (lexp_ge η n)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  calc 3 * (1 / 2 : ℝ) ^ (lexp η n) * (2 : ℝ) ^ n
      ≤ 3 * (1 / 2 : ℝ) ^ (2 * n + 12) * (2 : ℝ) ^ n := by nlinarith [h1, hpos]
    _ = 3 * ((1 / 2 : ℝ) ^ (2 * n + 12) * (2 : ℝ) ^ n) := by ring
    _ ≤ (1 / 2 : ℝ) ^ (n + 10) := by
        have e : (1 / 2 : ℝ) ^ (2 * n + 12) * (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (n + 12) := by
          rw [show 2 * n + 12 = (n + 12) + n by ring, pow_add, mul_assoc, half_mul_two, mul_one]
        rw [e]
        have e2 : (1 / 2 : ℝ) ^ (n + 12) = (1 / 2 : ℝ) ^ (n + 10) * (1 / 2 : ℝ) ^ 2 := by
          rw [← pow_add]
        rw [e2]
        nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n + 10)]

theorem trans_bd_inv12 (η : ℝ) (n : ℕ) : 3 * (lea η n : ℝ) * (cnt n : ℝ) ≤ 1 / 12 :=
  (trans_bd η n).trans ((par_le_inv128 n).trans (by norm_num))

/-- **The leaf count fits under the uniformity budget** `Cunif ≤ σ ^ (-η)`. -/
theorem cnt_le_rpow_neg (η : ℝ) (hη : 0 < η) (n : ℕ) :
    ((cnt n : ℕ) : ENNReal) ≤ ((lea η n : NNReal) : ENNReal) ^ (-η) := by
  have hm : (n : ℝ) ≤ (lexp η n : ℝ) * η := by
    have hceil : ((n : ℝ) / η) ≤ (⌈(n : ℝ) / η⌉₊ : ℝ) := Nat.le_ceil _
    have hle : (⌈(n : ℝ) / η⌉₊ : ℝ) ≤ (lexp η n : ℝ) := by
      exact_mod_cast le_max_right (2 * n + 12) ⌈(n : ℝ) / η⌉₊
    have h1 : (n : ℝ) / η ≤ (lexp η n : ℝ) := hceil.trans hle
    calc (n : ℝ) = ((n : ℝ) / η) * η := by field_simp
      _ ≤ (lexp η n : ℝ) * η := by nlinarith
  have hcoe : ((lea η n : NNReal) : ENNReal) = ((2 : ENNReal) ^ (lexp η n))⁻¹ := by
    unfold lea
    push_cast
    rw [ENNReal.inv_pow]
    norm_num
  have h2 : ((2 : ENNReal) ^ (lexp η n))⁻¹ = (2 : ENNReal) ^ (-(lexp η n : ℝ)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_natCast]
  rw [hcoe, h2, ← ENNReal.rpow_mul]
  have hL : ((cnt n : ℕ) : ENNReal) = (2 : ENNReal) ^ ((n : ℝ)) := by
    rw [ENNReal.rpow_natCast]
    unfold cnt
    push_cast
    ring
  rw [hL]
  refine ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [show -(lexp η n : ℝ) * -η = (lexp η n : ℝ) * η by ring]
  exact hm

end rhoFreeCex


/-! ### The plank factorization hypothesis on a one-member fibre

GWZ Proposition 6.6(A) also asks, for every coarse label, a `2`-factorization of that label's
fibre by `a × b × 1` planks.  In the configuration below every fibre is a *singleton*, and a
`σ`-tube is a `σ × σ × 1` plank, so the hypothesis is satisfiable at `a = b = σ` and any
comparability constant `Cw ≥ 2`.  Nothing about the count changes; this section only removes the
last hypothesis of the package from the list of things the refutation does not carry. -/

section Singleton

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A one-member family of convex bodies is Katz--Tao at every constant `≥ 1`. -/
theorem isKatzTao_singleton {ι : Type*} (W : ι → ConvexSpaceBody E) (i : ι)
    {C : ENNReal} (hC : 1 ≤ C) : ConvexSpaceBody.IsKatzTao ({i} : Finset ι) W C := by
  classical
  rw [ConvexSpaceBody.isKatzTao_iff]
  intro K
  by_cases h : W i ≤ K
  · rw [show ({i} : Finset ι).filter (fun j => W j ≤ K) = {i} by simp [h]]
    simp only [Finset.sum_singleton]
    calc volume (W i).carrier ≤ volume K.carrier := measure_mono h
      _ = 1 * volume K.carrier := (one_mul _).symm
      _ ≤ C * volume K.carrier := by gcongr
  · rw [show ({i} : Finset ι).filter (fun j => W j ≤ K) = ∅ by simp [h]]
    simp

/-- The density of a one-member family in its own member is `1`. -/
theorem densityIn_singleton_self {ι : Type*} (W : ι → ConvexSpaceBody E) (i : ι)
    (hvol : 0 < volume (W i).carrier) (hvolt : volume (W i).carrier ≠ ⊤) :
    densityIn ({i} : Finset ι) W (W i) = 1 := by
  classical
  unfold densityIn
  rw [show ({i} : Finset ι).filter (fun j => W j ≤ W i) = {i} by simp]
  rw [Finset.sum_singleton, ENNReal.div_self hvol.ne' hvolt]

/-- **A one-member family factorizes at the constant `2`**, by the indiscrete partition. -/
theorem exists_factorization_singleton {ι : Type*} [DecidableEq ι] (W : ι → ConvexSpaceBody E)
    (i : ι) (hvol : 0 < volume (W i).carrier) (hvolt : volume (W i).carrier ≠ ⊤) :
    ∃ F : ConvexSpaceBody.Factorization ({i} : Finset ι) W 2,
      F.parts = {({i} : Finset ι)} := by
  classical
  have hne : ({i} : Finset ι) ≠ ⊥ := by simp
  have hparts : (Finpartition.indiscrete hne).parts = {({i} : Finset ι)} :=
    Finpartition.indiscrete_parts hne
  have hhull : ({i} : Finset ι).convexHull_biUnion W = W i :=
    Finset.convexHull_biUnion_singleton W i
  have hkt : ConvexSpaceBody.IsKatzTao (Finpartition.indiscrete hne).parts
      (fun t => t.convexHull_biUnion W) 2 := by
    rw [hparts]
    exact isKatzTao_singleton (ι := Finset ι) (fun t => t.convexHull_biUnion W)
      ({i} : Finset ι) (C := ((2 : NNReal) : ENNReal)) (by norm_num)
  have hmd : ∀ t ∈ (Finpartition.indiscrete hne).parts,
      maxDensity ({i} : Finset ι) W ≤ 2 * densityIn t W (t.convexHull_biUnion W) := by
    intro t ht
    rw [hparts, Finset.mem_singleton] at ht
    subst ht
    rw [hhull, densityIn_singleton_self W i hvol hvolt]
    calc maxDensity ({i} : Finset ι) W ≤ 1 :=
          isKatzTao_singleton (ι := ι) W i (C := (1 : ENNReal)) le_rfl
      _ ≤ 2 * 1 := by norm_num
  have hsd : ∀ t ∈ (Finpartition.indiscrete hne).parts,
      ∀ t' ∈ (Finpartition.indiscrete hne).parts,
      Metric.ethickness ℝ (t.convexHull_biUnion W).carrier ≤
        (2 : NNReal) • Metric.ethickness ℝ (t'.convexHull_biUnion W).carrier := by
    intro t ht t' ht'
    rw [hparts, Finset.mem_singleton] at ht ht'
    subst ht
    subst ht'
    have h2 : (1 : ENNReal) ≤ ((2 : NNReal) : ENNReal) := by norm_num
    rw [Pi.le_def]
    intro k
    rw [Pi.smul_apply, ENNReal.smul_def]
    exact le_of_eq_of_le (one_mul _).symm (mul_le_mul_left h2 _)
  exact ⟨{ toFinpartition := Finpartition.indiscrete hne
           isKatzTao := hkt
           maxDensity_le_mul := hmd
           simDims := hsd }, hparts⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A `σ`-tube in `ℝ³` is a `σ × σ × 1` plank**, at every comparability constant `Cw ≥ 2`.

`τ₀ ∈ [1/2, 1 + σ] ⊆ [Cw⁻¹, Cw]` and `τ₁ = τ₂ = σ`, the latter by squeezing
`Tube.le_ethickness_finrank_sub_one` against `Tube.ethickness_one_le` through the
antitonicity of `Metric.ethickness` in its rank. -/
theorem isPlankOfDimensions_tube (hdim : Module.finrank ℝ E = 3) {σ Cw : NNReal} (hσ1 : σ ≤ 1)
    (hCw : 2 ≤ Cw) (T : Tube σ E) : IsPlankOfDimensions Cw σ σ T.toConvexSpaceBody := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hlo : (1 : ENNReal) / 2 ≤ Metric.ethickness ℝ T.carrier 0 := T.le_ethickness_zero
  have hhi : Metric.ethickness ℝ T.carrier 0 ≤ 1 + (σ : ENNReal) := T.ethickness_zero_le
  have hrk : Module.finrank ℝ E - 1 = 2 := by omega
  have hlo2 : (σ : ENNReal) ≤ Metric.ethickness ℝ T.carrier 2 := by
    have h := T.le_ethickness_finrank_sub_one
    rwa [hrk] at h
  have hup1 : Metric.ethickness ℝ T.carrier 1 ≤ (σ : ENNReal) := T.ethickness_one_le
  have h21 : Metric.ethickness ℝ T.carrier 2 ≤ Metric.ethickness ℝ T.carrier 1 :=
    Metric.ethickness_antitone (by norm_num)
  have hτ2 : Metric.ethickness ℝ T.carrier 2 = (σ : ENNReal) :=
    le_antisymm (h21.trans hup1) hlo2
  have hτ1 : Metric.ethickness ℝ T.carrier 1 = (σ : ENNReal) :=
    le_antisymm hup1 (hτ2 ▸ h21)
  have hCwE : (2 : ENNReal) ≤ (Cw : ENNReal) := by exact_mod_cast hCw
  have hinv : (Cw : ENNReal)⁻¹ ≤ (2 : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr hCwE
  have hσE : (σ : ENNReal) ≤ 1 := by exact_mod_cast hσ1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine hinv.trans ?_
    simpa using hlo
  · refine le_trans hhi ?_
    refine le_trans (by gcongr : (1 : ENNReal) + (σ : ENNReal) ≤ 1 + 1) ?_
    rw [show (1 : ENNReal) + 1 = 2 by norm_num]
    exact hCwE
  · rw [hτ1]
    calc (Cw : ENNReal)⁻¹ * (σ : ENNReal) ≤ 1 * (σ : ENNReal) := by
          gcongr
          exact hinv.trans (by norm_num)
      _ = (σ : ENNReal) := one_mul _
  · rw [hτ1]
    calc (σ : ENNReal) = 1 * (σ : ENNReal) := (one_mul _).symm
      _ ≤ (Cw : ENNReal) * (σ : ENNReal) := by gcongr; exact le_trans (by norm_num) hCwE
  · rw [hτ2]
    calc (Cw : ENNReal)⁻¹ * (σ : ENNReal) ≤ 1 * (σ : ENNReal) := by
          gcongr
          exact hinv.trans (by norm_num)
      _ = (σ : ENNReal) := one_mul _
  · rw [hτ2]
    calc (σ : ENNReal) = 1 * (σ : ENNReal) := (one_mul _).symm
      _ ≤ (Cw : ENNReal) * (σ : ENNReal) := by gcongr; exact le_trans (by norm_num) hCwE

end Singleton


open ml1Boot.essDistinctCex in
/-- **The pencil's cores are pairwise distinct**: the `e₂`-coordinate of the `i`-th core is
`3 σ i`. -/
theorem essDistinctCex_base_inj {σ ρ : NNReal} (hσ0 : 0 < σ) {i j : ℕ}
    (h : base σ ρ i = base σ ρ j) : i = j := by
  have hσR : (0 : ℝ) < (σ : ℝ) := by exact_mod_cast hσ0
  have hcoord := congrArg (fun z => (inner ℝ z e₂ : ℝ)) h
  simp only [inner_base_e₂] at hcoord
  have h3 : (3 : ℝ) * (σ : ℝ) * (i : ℝ) = 3 * (σ : ℝ) * (j : ℝ) := by
    simpa [ml1Boot.essDistinctCex.trans] using hcoord
  have hne : (3 : ℝ) * (σ : ℝ) ≠ 0 := by positivity
  have hij : (i : ℝ) = (j : ℝ) := mul_left_cancel₀ hne h3
  exact_mod_cast hij

open ml1Boot.essDistinctCex in
/-- **The pencil's coarse parents are pairwise distinct tubes.**

They are *not* essentially distinct — they are the longitudinal stack of the blueprint's erratum
— but they are genuinely `≠`, so no counterexample below trades on duplicate parent labels. -/
theorem essDistinctCex_parent_inj {σ ρ : NNReal} (hσ0 : 0 < σ) {i j : ℕ}
    (h : parent σ ρ i = parent σ ρ j) : i = j :=
  essDistinctCex_base_inj hσ0 (congrArg Tube.x h)

open ml1Boot.essDistinctCex in
/-- **The counterexample configuration at stage `n`.**

Every clause of GWZ Proposition 6.6(A)'s hypothesis package on the family holds — nonemptiness,
one-sided uniformity at `Cunif = cnt n ≤ σ ^ (-η)`, containment in `B₁`, leaf-scale essential
distinctness, fullness (which is exactly `1`, the fully shaded pencil) — together with ship's
parent clauses at dilation `1`: every leaf lies in its *own* coarse parent tube.  Yet all
`cnt n` parent labels are occupied inside the `4`-dilate of the *single* coarse tube
`parent σ ρ 0`.

The count is `cnt n = ρ⁻¹ / 2 ^ 10`, and `σ ≤ (1/2) ^ n`, so the configurations occur at
arbitrarily small leaf scales. -/
theorem exists_isFlatPrismFamily_card_assignedParents_eq {η : ℝ} (hη : 0 < η)
    {Cw : NNReal} (hCw : 2 ≤ Cw) (n : ℕ) :
    ∃ (σ ρ Cunif : NNReal) (V : ℕ → ShadedTube σ (EuclideanSpace ℝ (Fin 3)))
      (Vρ : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
      (W : Tube ρ (EuclideanSpace ℝ (Fin 3))),
      0 < σ ∧ σ ≤ ρ ∧ ρ ≤ 1 ∧ (σ : ℝ) ≤ (1 / 2 : ℝ) ^ n ∧ (ρ : ℝ) ≤ (1 / 2 : ℝ) ^ n ∧
      1 ≤ Cunif ∧ (Cunif : ENNReal) ≤ (σ : ENNReal) ^ (-η) ∧
      IsFlatPrismFamily η Cunif (Finset.range (rhoFreeCex.cnt n)) V ∧
      (∀ i ∈ Finset.range (rhoFreeCex.cnt n), i ∈ Finset.range (rhoFreeCex.cnt n)) ∧
      (∀ i ∈ Finset.range (rhoFreeCex.cnt n),
        (V i).toConvexSpaceBody ≤ (Vρ i).toConvexSpaceBody) ∧
      (∀ i j : ℕ, i ≠ j → Vρ i ≠ Vρ j) ∧
      (∀ k ∈ Finset.range (rhoFreeCex.cnt n), ∃ F : ConvexSpaceBody.Factorization
          ((Finset.range (rhoFreeCex.cnt n)).filter fun i => i = k)
          (fun i => (V i).toConvexSpaceBody) 2,
        IsPlankFamilyOfDimensions Cw σ σ F.parts
          (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))) ∧
      ((Finset.range (rhoFreeCex.cnt n)).filter fun k => ∃ i ∈ Finset.range (rhoFreeCex.cnt n),
          i = k ∧ (V i).toConvexSpaceBody ≤ Tube.dilate W (4 : ℝ))
        = Finset.range (rhoFreeCex.cnt n) ∧
      (ρ : ℝ)⁻¹ = 2 ^ 10 * (rhoFreeCex.cnt n : ℝ) := by
  classical
  set σ : NNReal := rhoFreeCex.lea η n with hσdef
  set ρ : NNReal := rhoFreeCex.par n with hρdef
  set M : ℕ := rhoFreeCex.cnt n with hMdef
  have hσ0 : 0 < σ := rhoFreeCex.lea_pos η n
  have hρ0 : 0 < ρ := rhoFreeCex.par_pos n
  have hσρ : σ ≤ ρ := rhoFreeCex.lea_le_par η n
  have hρ1 : ρ ≤ 1 := rhoFreeCex.par_le_one n
  have hσ1 : σ ≤ 1 := hσρ.trans hρ1
  have hρ128 : (ρ : ℝ) ≤ 1 / 128 := rhoFreeCex.par_le_inv128 n
  have hax : 7 * (ρ : ℝ) * (M : ℝ) ≤ 1 / 12 := rhoFreeCex.axial_bd n
  have htr : 3 * (σ : ℝ) * (M : ℝ) ≤ (ρ : ℝ) := rhoFreeCex.trans_bd η n
  have htr12 : 3 * (σ : ℝ) * (M : ℝ) ≤ 1 / 12 := rhoFreeCex.trans_bd_inv12 η n
  have hM0 : 0 < M := rhoFreeCex.cnt_pos n
  refine ⟨σ, ρ, (M : NNReal), fullLeaf σ ρ, parent σ ρ, parent σ ρ 0,
    hσ0, hσρ, hρ1, ?_, ?_, ?_, ?_, ?_, fun i hi => hi, ?_, ?_, ?_, ?_, ?_⟩
  · -- `σ ≤ (1/2) ^ n`
    rw [hσdef, rhoFreeCex.lea_coe]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (le_trans (by omega) (rhoFreeCex.lexp_ge η n))
  · -- `ρ ≤ (1/2) ^ n`
    rw [hρdef, rhoFreeCex.par_coe]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  · -- `1 ≤ Cunif`
    exact_mod_cast hM0
  · -- `Cunif ≤ σ ^ (-η)`
    exact rhoFreeCex.cnt_le_rpow_neg η hη n
  · -- the family package
    refine ⟨⟨0, Finset.mem_range.mpr hM0⟩, ?_, ?_, ?_, ?_⟩
    · -- uniformity, at `Cunif = #s`
      refine nonempty_isFlatPrismUniform_of_card_le hσ0 hσ1 _ _ _ (by exact_mod_cast hM0) ?_ ?_
      · simp
      · intro i hi j hj hx hy
        exact essDistinctCex_base_inj hσ0 (hx : base σ ρ i = base σ ρ j)
    · -- containment in `B₁`
      intro i hi
      exact leaf_carrier_subset_ball hσρ hρ128 hax htr12
        (le_of_lt (Finset.mem_range.mp hi))
    · -- leaf-scale essential distinctness
      intro i _ j _ hij
      exact isEssentiallyDistinct_leaf hσ0 hij
    · -- fullness
      rw [fullness_fullLeaf_eq_one hσ0 hσ1 hM0]
      have : (σ : ENNReal) ^ η ≤ (1 : ENNReal) ^ η :=
        ENNReal.rpow_le_rpow (by exact_mod_cast hσ1) hη.le
      simpa using this
  · -- every leaf lies in its own coarse parent
    intro i hi
    exact Tube.le_rescale (leaf σ ρ i) hσρ
  · -- the coarse parents are pairwise distinct tubes
    intro i j hij hEq
    exact hij (essDistinctCex_parent_inj hσ0 hEq)
  · -- the plank factorization of every (singleton) fibre, at `a = b = σ`
    intro k hk
    have hfib : (Finset.range M).filter (fun i => i = k) = {k} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hk, h⟩⟩
    rw [hfib]
    have hvol := Tube.volume_pos_and_lt_top hσ0 hσ1 (leaf σ ρ k)
    obtain ⟨F, hFparts⟩ := exists_factorization_singleton
      (fun i => (fullLeaf σ ρ i).toConvexSpaceBody) k hvol.1 hvol.2.ne
    refine ⟨F, ?_⟩
    intro part hpart
    rw [hFparts, Finset.mem_singleton] at hpart
    subst hpart
    change IsPlankOfDimensions Cw σ σ
      (({k} : Finset ℕ).convexHull_biUnion fun i => (fullLeaf σ ρ i).toConvexSpaceBody)
    rw [Finset.convexHull_biUnion_singleton]
    exact isPlankOfDimensions_tube (finrank_euclideanSpace_fin) hσ1 hCw (leaf σ ρ k)
  · -- every parent label is occupied inside the `4`-dilate of one coarse tube
    ext k
    simp only [Finset.mem_filter]
    refine ⟨fun h => h.1, fun hk => ⟨hk, k, hk, rfl, ?_⟩⟩
    exact SetLike.coe_subset_coe.mpr
      (essDistinctCex_leaf_carrier_subset_parentZero_dilate hσρ hρ128 hax htr
        (le_of_lt (Finset.mem_range.mp hk)))
  · -- the count is `ρ⁻¹ / 2 ^ 10`
    rw [hρdef, rhoFreeCex.par_coe, hMdef, rhoFreeCex.cnt_coe]
    rw [pow_add]
    field_simp
    exact (rhoFreeCex.half_mul_two n).symm

/-- **(the decision) No constant bounds the outer-plank assigned-parent count under the full
hypothesis package of GWZ Proposition 6.6(A).**

The refuted statement is ship's 6.6(A) hypothesis package, verbatim and complete:

* the scale chain `σ ≤ ρ ≤ 1` (the plank scales `a`, `b` do not enter the count);
* the uniformity constant `Cunif` with `1 ≤ Cunif ≤ σ ^ (-η)`, the exact constraint 6.6(A)
  imposes on it;
* `Kakeya.IsFlatPrismFamily η Cunif s V` — nonempty, one-sidedly uniform, in `B₁`, **leaf-scale**
  pairwise essentially distinct, and full at level `σ ^ η`;
* ship's parent clauses `p i ∈ t` and `V i ≤ Vρ (p i)`, at dilation `1`;
* the plank factorization hypothesis: one `2`-factorization of every parent-map fibre by
  `a × b × 1` planks, at `σ ≤ a ≤ b ≤ ρ`, for every comparability constant `Cw ≥ 2`;

and the conclusion is the count of occupied parent labels inside a `4`-dilate of one coarse tube,
the shape to which the plank-shaped test body of the outer plank step reduces
(`Kakeya.edParentCount.card_assignedParents_le_of_subset_dilate`).

Unlike `Kakeya.not_card_assignedParents_le_const_of_boundedOverlap_of_full`, which had to leave
the uniformity clause out, this refutation carries it, by
`Kakeya.nonempty_isFlatPrismUniform_of_card_le`.  Nothing in the package is dropped or
weakened.

## The one thing the statement does *not* carry

The test body here is `Tube.dilate W 4` for a coarse tube `W`, not a literal
`((P.thickened θ).toPrismNDim.dilation C_NC).homothety 0 A` for a `Kakeya.Plank`.  That is the
body to which `Kakeya.edParentCount.card_assignedParents_le_homotheticDilatedThickenedPlank`
reduces the plank test body before counting — both known upper bounds on this count factor
through exactly this shape — so the refutation hits the quantity those bounds bound.  It is not,
however, a refutation phrased at the literal plank body, and this file does not claim one. -/
theorem not_card_assignedParents_le_const_of_isFlatPrismFamily (C Cw : NNReal) (hCw : 2 ≤ Cw)
    {η : ℝ} (hη : 0 < η) :
    ¬ ∀ (σ ρ : NNReal), 0 < σ → σ ≤ ρ → ρ ≤ 1 →
        ∀ Cunif : NNReal, 1 ≤ Cunif → (Cunif : ENNReal) ≤ (σ : ENNReal) ^ (-η) →
        ∀ a b : NNReal, σ ≤ a → a ≤ b → b ≤ ρ →
        ∀ (s t : Finset ℕ) (V : ℕ → ShadedTube σ (EuclideanSpace ℝ (Fin 3)))
          (Vρ : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (p : ℕ → ℕ)
          (W : Tube ρ (EuclideanSpace ℝ (Fin 3))),
          IsFlatPrismFamily η Cunif s V →
          (∀ i ∈ s, p i ∈ t) →
          (∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody) →
          (∀ k ∈ t, ∃ F : ConvexSpaceBody.Factorization (s.filter fun i => p i = k)
                (fun i => (V i).toConvexSpaceBody) 2,
              IsPlankFamilyOfDimensions Cw a b F.parts
                (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))) →
          ((t.filter fun k => ∃ i ∈ s, p i = k ∧
              (V i).toConvexSpaceBody ≤ Tube.dilate W (4 : ℝ)).card : ENNReal)
            ≤ (C : ENNReal) := by
  classical
  intro hbound
  obtain ⟨m, hm⟩ := exists_nat_gt (C : ℝ)
  obtain ⟨σ, ρ, Cunif, V, Vρ, W, hσ0, hσρ, hρ1, _hσsmall, _hρsmall, hCunif1, hCunif, hfam,
    _hmaps, hle, _hinj, hplank, hfilter, _hcount⟩ :=
    exists_isFlatPrismFamily_card_assignedParents_eq hη hCw m
  have hkey := hbound σ ρ hσ0 hσρ hρ1 Cunif hCunif1 hCunif σ σ le_rfl le_rfl hσρ
    (Finset.range (rhoFreeCex.cnt m)) (Finset.range (rhoFreeCex.cnt m)) V Vρ (fun i => i) W
    hfam (fun i hi => hi) hle hplank
  rw [hfilter, Finset.card_range] at hkey
  have hMC : (C : ℝ) < (rhoFreeCex.cnt m : ℝ) := by
    have h1 : (m : ℝ) < (rhoFreeCex.cnt m : ℝ) := by
      have : m < rhoFreeCex.cnt m := by
        simpa [rhoFreeCex.cnt] using (Nat.lt_two_pow_self : m < 2 ^ m)
      exact_mod_cast this
    linarith
  have hMC' : (C : ENNReal) < ((rhoFreeCex.cnt m : ℕ) : ENNReal) := by
    have hlt : (C : NNReal) < ((rhoFreeCex.cnt m : ℕ) : NNReal) := by
      rw [← NNReal.coe_lt_coe]
      simpa using hMC
    exact_mod_cast hlt
  exact absurd hkey (not_le.mpr hMC')

/-- **The sharpest lower bound: the outer-plank assigned-parent count is `≍ ρ⁻¹` under the full
hypothesis package of GWZ Proposition 6.6(A).**

For every `n` there is a configuration satisfying the entire package, at a coarse scale
`ρ ≤ (1/2) ^ n`, whose occupied-parent count is exactly `ρ⁻¹ / 2 ^ 10`.

Together with `Kakeya.card_assignedParents_le_of_boundedOverlap`, which gives
`Co · parentCount.C · ρ ^ (-5)` from bounded overlap, this brackets the truth between `ρ ^ (-1)`
and `ρ ^ (-5)`.  In particular no bound of the form `C`, or `C · (log (1/ρ)) ^ d`, or any
`o(ρ ^ (-1))` bound whatsoever, is available: on this family such a bound would have to dominate
`ρ⁻¹ / 2 ^ 10` at arbitrarily small `ρ`. -/
theorem exists_isFlatPrismFamily_rhoInv_le_card_assignedParents {η : ℝ} (hη : 0 < η)
    {Cw : NNReal} (hCw : 2 ≤ Cw) (n : ℕ) :
    ∃ (σ ρ Cunif : NNReal) (V : ℕ → ShadedTube σ (EuclideanSpace ℝ (Fin 3)))
      (Vρ : ℕ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
      (W : Tube ρ (EuclideanSpace ℝ (Fin 3))) (s : Finset ℕ),
      0 < σ ∧ σ ≤ ρ ∧ (ρ : ℝ) ≤ (1 / 2 : ℝ) ^ n ∧ ρ ≤ 1 ∧
      1 ≤ Cunif ∧ (Cunif : ENNReal) ≤ (σ : ENNReal) ^ (-η) ∧
      IsFlatPrismFamily η Cunif s V ∧
      (∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ i).toConvexSpaceBody) ∧
      (∀ i j : ℕ, i ≠ j → Vρ i ≠ Vρ j) ∧
      (∀ k ∈ s, ∃ F : ConvexSpaceBody.Factorization (s.filter fun i => i = k)
          (fun i => (V i).toConvexSpaceBody) 2,
        IsPlankFamilyOfDimensions Cw σ σ F.parts
          (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))) ∧
      (ρ : ℝ)⁻¹ ≤ 2 ^ 10 *
        ((s.filter fun k => ∃ i ∈ s, i = k ∧
          (V i).toConvexSpaceBody ≤ Tube.dilate W (4 : ℝ)).card : ℝ) := by
  classical
  obtain ⟨σ, ρ, Cunif, V, Vρ, W, hσ0, hσρ, hρ1, _hσsmall, hρsmall, hCunif1, hCunif, hfam,
    _hmaps, hle, hinj, hplank, hfilter, hcount⟩ :=
    exists_isFlatPrismFamily_card_assignedParents_eq hη hCw n
  refine ⟨σ, ρ, Cunif, V, Vρ, W, Finset.range (rhoFreeCex.cnt n), hσ0, hσρ, hρsmall, hρ1,
    hCunif1, hCunif, hfam, hle, hinj, hplank, ?_⟩
  rw [hfilter, Finset.card_range, hcount]


end Kakeya
