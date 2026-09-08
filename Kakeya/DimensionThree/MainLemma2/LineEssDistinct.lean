/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.IntersectionVolume
public import Kakeya.Tube.Dilate
public import Kakeya.Uniform
public import Kakeya.GreedyIndependentSetCard

/-!
# Line-based essential distinctness and the non-ED degree

The revised detailed proof
`260115_kakeyadetailedproofv3_revised_detailed.tex`, l.153-163, defines
essential distinctness using neighborhoods of complete lines. This module
defines `lineSet`, `lineNbhd`, `IsLineEssDistinct`, and the level data
`LineEDLevelsAt K A₁ 𝒰` and `LineEDLevels A₁ 𝒰`.

## The two notions

* `IsLineEssDistinct A s T` bounds by `A` the number of family members
  contained in the closed `5δ`-neighborhood of any complete line. Axial
  translates of a unit segment are consequently not distinguished.
  `IsLineEssDistinctAt K A s T` uses radius `Kδ`; the radius-`5`
  specialization is definitionally `IsLineEssDistinct`.
* `edDegree s K i` counts the other family members that are not
  essentially distinct from `K i` in the pairwise volume-based sense
  `IsEssentiallyDistinct`. Self is excluded, so pairwise essentially
  distinct families have degree zero (`edDegree_eq_zero_of_pairwise`).

## From line bounds to pairwise selection

* `exists_pairwise_of_edDegree_le` selects a pairwise essentially
  distinct subfamily retaining at least `1/(D + 1)` of any prescribed
  `[0, ∞]`-weight and of the cardinality when all non-ED degrees are
  at most `D`. It specializes
  `Kakeya.exists_pairwise_not_of_degree_le_card` to the relation
  `i ≠ j ∧ ¬ IsEssentiallyDistinct (K i) (K j)`.
* `Tube.carrier_subset_cthickening_line_of_not_essDistinct` puts a
  tube with heavy overlap inside the `C_n δ`-neighborhood of the
  other tube's core line, where
  `C_n = Kakeya.Tube.tubeOverlapCoreClose.C n = 9 + 2 * 4^n / c_n`.
  The proof combines the tube-overlap dilation estimate with equality
  of tube volumes and the description of a dilate as a neighborhood
  of a longer segment on the same line.
* `edDegree_add_one_le_of_isLineEssDistinctAt` therefore gives
  `edDegree ≤ A - 1` from a line-based bound at radius `C_n δ`.

This radius matters: `C_n` is approximately `101` in dimension three,
so the overlap estimate does not give containment in a `5δ`-neighborhood.
`IsLineEssDistinctAt C_n A` is stronger than the radius-`5` condition
by `IsLineEssDistinctAt.mono_radius`. A net construction can establish
the larger-radius bound by the same six-dimensional packing argument
used in the revised proof at l.4790-4800, with the constant adjusted.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

section LineED

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- The complete line through `p` with direction `d`: `{p + t • d : t ∈ ℝ}`. -/
def lineSet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p d : F) : Set F :=
  {y | ∃ t : ℝ, y = p + t • d}

theorem mem_lineSet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p d : F) (t : ℝ) :
    p + t • d ∈ lineSet p d := ⟨t, rfl⟩

/-- `N_r(L)`, the **closed** `r`-neighbourhood of the line `L` through `p` with direction `d`
(refined l.152: "For a line `L ⊂ ℝⁿ`, write `N_{5δ}(L)` for its closed `5δ`-neighbourhood"). -/
def lineNbhd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p d : F) (r : ℝ) : Set F :=
  Metric.cthickening r (lineSet p d)

theorem mem_lineNbhd_of_dist_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p d : F} {r : ℝ} {y : F} (t : ℝ)
    (h : dist y (p + t • d) ≤ r) : y ∈ lineNbhd p d r :=
  Metric.mem_cthickening_of_dist_le y _ r _ (mem_lineSet p d t) h

open scoped Classical in
/-- **Line-based `A`-essential distinctness, refined l.153–157 verbatim.**  A finite family `𝕋`
of `δ`-tubes is `A`-essentially distinct if `#{T ∈ 𝕋 : T ⊂ N_{5δ}(L)} ≤ A` for every line
`L ⊂ ℝⁿ`.  Lines are given by a point and a **unit** direction.

This is deliberately a condition on complete lines rather than on unit segments: axial
translates of one unit segment have the same line parameters, so there is no fifth axial
parameter — which is exactly why a bush of tubes through one point does not defeat it, while it
does defeat the pairwise, volume-based `Kakeya.IsEssentiallyDistinct`
(`Kakeya.LooseUniform.bush_obstruction`). -/
def IsLineEssDistinct (A : ℕ) {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) :
    Prop :=
  ∀ p d : E, ‖d‖ = 1 →
    (s.filter (fun i => (T i).carrier ⊆ lineNbhd p d (5 * (δ : ℝ)))).card ≤ A

end LineED

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

section RadiusParametrised

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] {ι : Type*}

/-- The line `lineSet p d` is the range of `t ↦ p + t • d`, so `lineNbhd p d r` is the closed
`r`-neighbourhood of that range — the bridge between the C6-a spelling and the inline one. -/
theorem lineNbhd_eq_cthickening_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p d : F) (r : ℝ) :
    lineNbhd p d r = Metric.cthickening r (Set.range fun t : ℝ ↦ p + t • d) := by
  unfold lineNbhd lineSet
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]

open scoped Classical in
/-- **Line-based `A`-essential distinctness at the neighbourhood radius `K δ`.**  The refined
notion is the case `K = 5` (`isLineEssDistinct_iff_at`); the degree bound below needs the case
`K = Kakeya.Tube.tubeOverlapCoreClose.C n`, the tree's two-tube overlap constant. -/
def IsLineEssDistinctAt (K : ℝ) (A : ℕ) {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) : Prop :=
  ∀ p d : E, ‖d‖ = 1 →
    (s.filter (fun i => (T i).carrier ⊆ lineNbhd p d (K * (δ : ℝ)))).card ≤ A

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The refined notion is the radius-`5` instance. -/
theorem isLineEssDistinct_iff_at {A : ℕ} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} :
    IsLineEssDistinct A s T ↔ IsLineEssDistinctAt 5 A s T := Iff.rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A smaller neighbourhood radius is a weaker condition. -/
theorem IsLineEssDistinctAt.mono_radius {K K' : ℝ} {A : ℕ} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} (h : IsLineEssDistinctAt K A s T) (hK : K' ≤ K) :
    IsLineEssDistinctAt K' A s T := by
  classical
  intro p d hd
  refine le_trans (Finset.card_le_card ?_) (h p d hd)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans (cthickening_mono (mul_le_mul_of_nonneg_right hK δ.coe_nonneg) _)⟩

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A larger count bound is a weaker condition. -/
theorem IsLineEssDistinctAt.mono_A {K : ℝ} {A A' : ℕ} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} (h : IsLineEssDistinctAt K A s T) (hA : A ≤ A') :
    IsLineEssDistinctAt K A' s T :=
  fun p d hd => le_trans (h p d hd) hA

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Line-based essential distinctness passes to subfamilies. -/
theorem IsLineEssDistinctAt.subset {K : ℝ} {A : ℕ} {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} (h : IsLineEssDistinctAt K A s T) (hts : t ⊆ s) :
    IsLineEssDistinctAt K A t T := by
  classical
  intro p d hd
  exact le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hts)) (h p d hd)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Line-based essential distinctness passes to subfamilies (the `5δ` notion). -/
theorem IsLineEssDistinct.subset {A : ℕ} {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} (h : IsLineEssDistinct A s T) (hts : t ⊆ s) :
    IsLineEssDistinct A t T :=
  (isLineEssDistinct_iff_at.1 h).subset hts

/-- **Line-based `A₁`-essential distinctness of every level of a hierarchy, at neighbourhood
radius `K δ`** — the level datum  item 1 (the refined
"the level `𝕋_k` is `A₁`-essentially distinct", l.4085–4092, `A₁ = 2·641⁶`, l.4900–4901), stated
at a general radius because the bridge to the tree's pairwise vocabulary needs
`K = Kakeya.Tube.tubeOverlapCoreClose.C n` (§1.3) while the refined notion is `K = 5`.  `Kakeya.ML2Core.LineEDLevels` and `LineEDLevelsAt` use this predicate.  Not a field of `Tube.UniformTubeSet`
; additive and Section-9-local.  The levels are `k < N`, the active-level range (the producer's `activeRestrict` hierarchy has the `N` levels
`0, …, N-1`). -/
def LineEDLevelsAt (K : ℝ) (A₁ : ℕ) {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) : Prop :=
  ∀ k, k < N → IsLineEssDistinctAt K A₁ (𝒰.cover.indexSet k) (𝒰.cover.tube k)

/-- **The datum, as the map names it** :
`LineEDLevels A₁ 𝒰` says that for every level `k` of the **exact** hierarchy `𝒰` the level-`k`
nodes are `A₁`-line-essentially distinct — the refined radius `5`. -/
def LineEDLevels (A₁ : ℕ) {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) : Prop :=
  LineEDLevelsAt 5 A₁ 𝒰

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem lineEDLevels_iff_at {A₁ : ℕ} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} {𝒰 : Tube.UniformTubeSet s T N C} :
    LineEDLevels A₁ 𝒰 ↔ LineEDLevelsAt 5 A₁ 𝒰 := Iff.rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The flat form of the refined datum. -/
theorem lineEDLevels_iff {A₁ : ℕ} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} {𝒰 : Tube.UniformTubeSet s T N C} :
    LineEDLevels A₁ 𝒰 ↔
      ∀ k, k < N → IsLineEssDistinct A₁ (𝒰.cover.indexSet k) (𝒰.cover.tube k) :=
  Iff.rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A level datum at a larger neighbourhood radius is the stronger one. -/
theorem LineEDLevelsAt.mono_radius {K K' : ℝ} {A₁ : ℕ} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} {𝒰 : Tube.UniformTubeSet s T N C}
    (h : LineEDLevelsAt K A₁ 𝒰) (hK : K' ≤ K) : LineEDLevelsAt K' A₁ 𝒰 :=
  fun k hk ↦ (h k hk).mono_radius hK

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A larger count bound is the weaker datum. -/
theorem LineEDLevelsAt.mono_A {K : ℝ} {A₁ A₂ : ℕ} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} {𝒰 : Tube.UniformTubeSet s T N C}
    (h : LineEDLevelsAt K A₁ 𝒰) (hA : A₁ ≤ A₂) : LineEDLevelsAt K A₂ 𝒰 :=
  fun k hk ↦ (h k hk).mono_A hA

end RadiusParametrised

/-! ### The non-ED degree, and the bridge to the pairwise vocabulary -/

section Degree

variable {F : Type*} [MeasureSpace F] {ι : Type*}

/-- **The non-ED degree bound of the ball-core segments**: refined `propvnslocalization` (l.5381) makes the capsule family line-based
`A₀`-essentially distinct with `A₀ = 2·223⁶`; a `δ`-free absolute, its own
symbol — not `SpineEDExtraction`'s family-level `M`, not `bd.C₀`.  The value is **provisional
at the refined `A₀`**: the producer of the degree bound (C7-b, the canonical-capsule core) proves
its family's non-ED degree by `ℝ⁶`-packing at the tree's two-tube constant
`Kakeya.Tube.tubeOverlapCoreClose.C 3` (≈ `101`, not the refined `5`), and its value replaces
this one token if it is larger.  Every consumer reads the constant through this name only.

**Value.**  The refined `A₀ = 2·223⁶ = 245956992494978` is this
same recipe — `2 · (packing count)⁶` over the six parameters of a pair of capsules — at the
refined radius `5`.  The tree's bridge runs at `C₃ = Kakeya.Tube.tubeOverlapCoreClose.C 3 =
9 + 288/π ≈ 100.673` instead, so the packing constant grows by `≈ 4.5 · 10⁷`: the compiled leaf
`CapsuleNet.edDegree_capsuleAt_le` (`CanonicalCapsules.lean`) gives
`edDegree ≤ 2 · (2 · (5 · C₃ · ρ) / (ε / 2) + 1)^(2·3)`, which at the producer's `ρ = 2δ`,
`ε = δ` is `2 · (40 · C₃ + 1)⁶` with `40 · C₃ + 1 ≈ 4027.93`; over-estimated with only `π > 3`
(`288/π < 96`, `C₃ < 105`, `40 · C₃ + 1 < 4201`) it is `2 · 4201⁶ = 10993755773892049250402`.
Any explicit `δ`-free numeral `≥ 2 · 4201⁶` is inside the licence (B4-C2). -/
def edMultiplicityConstant : ℕ := 2 * 4201 ^ 6

theorem one_le_edMultiplicityConstant : 1 ≤ edMultiplicityConstant := by
  unfold edMultiplicityConstant
  norm_num

/-- **The non-ED degree** of the index `i` in the family `K` on `s`: the number of *other* indices
`j ∈ s` whose body is **not** essentially distinct from `K i`, in the tree's pairwise
volume-based sense `IsEssentiallyDistinct`.  Stated with `Set.ncard`, as
`Kakeya.exists_pairwise_not_of_degree_le` states its degree hypothesis, so that no
`DecidableRel` is needed. -/
noncomputable def edDegree (s : Finset ι) (K : ι → Set F) (i : ι) : ℕ :=
  {j ∈ (s : Set ι) | j ≠ i ∧ ¬ _root_.IsEssentiallyDistinct (K i) (K j)}.ncard

/-- The degree set is finite. -/
theorem edDegree_set_finite (s : Finset ι) (K : ι → Set F) (i : ι) :
    {j ∈ (s : Set ι) | j ≠ i ∧ ¬ _root_.IsEssentiallyDistinct (K i) (K j)}.Finite :=
  s.finite_toSet.subset fun _ hj => hj.1

/-- **Pairwise essentially distinct ⇒ non-ED degree `0`.** -/
theorem edDegree_eq_zero_of_pairwise {s : Finset ι} {K : ι → Set F}
    (h : (s : Set ι).Pairwise fun i j => _root_.IsEssentiallyDistinct (K i) (K j))
    {i : ι} (hi : i ∈ s) : edDegree s K i = 0 := by
  unfold edDegree
  have hempty : {j ∈ (s : Set ι) | j ≠ i ∧ ¬ _root_.IsEssentiallyDistinct (K i) (K j)} = ∅ := by
    ext j
    simp only [mem_setOf_eq, Finset.mem_coe, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hj hji
    exact h hi hj (Ne.symm hji)
  rw [hempty, Set.ncard_empty]

/-- The non-ED degree is monotone in the family. -/
theorem edDegree_mono {s t : Finset ι} (hts : t ⊆ s) (K : ι → Set F) (i : ι) :
    edDegree t K i ≤ edDegree s K i :=
  Set.ncard_le_ncard (fun _ hj => ⟨hts hj.1, hj.2⟩) (edDegree_set_finite s K i)

/-- **Non-ED degree `≤ D` ⇒ a pairwise essentially distinct subfamily with `1/(D+1)` of any
weight and of the cardinality** — `Kakeya.exists_pairwise_not_of_degree_le_card` at the relation
`i ≠ j ∧ ¬ IsEssentiallyDistinct (K i) (K j)`.  The retention is multiplicative,
`∑_s y ≤ (D + 1) ∑_{s'} y` and `#s ≤ (D + 1) #s'`, so no division in `ℝ≥0∞` occurs. -/
theorem exists_pairwise_of_edDegree_le (s : Finset ι) (K : ι → Set F) {D : ℕ}
    (hdeg : ∀ i ∈ s, edDegree s K i ≤ D) (y : ι → ENNReal) :
    ∃ s' ⊆ s, (s' : Set ι).Pairwise (fun i j => _root_.IsEssentiallyDistinct (K i) (K j)) ∧
      ∑ j ∈ s, y j ≤ (D + 1 : ℕ) * ∑ j ∈ s', y j ∧ s.card ≤ (D + 1) * s'.card := by
  let r : ι → ι → Prop := fun i j => i ≠ j ∧ ¬ _root_.IsEssentiallyDistinct (K i) (K j)
  have hsymm : ∀ i j, r i j → r j i :=
    fun _ _ h => ⟨h.1.symm, fun h' => h.2 (isEssentiallyDistinct_symm h')⟩
  have hirr : ∀ i, ¬ r i i := fun _ h => h.1 rfl
  have hdeg' : ∀ i ∈ s, {j ∈ (s : Set ι) | r j i}.ncard ≤ D := by
    intro i hi
    have hset : {j ∈ (s : Set ι) | r j i} =
        {j ∈ (s : Set ι) | j ≠ i ∧ ¬ _root_.IsEssentiallyDistinct (K i) (K j)} := by
      ext j
      simp only [mem_setOf_eq, r]
      constructor
      · rintro ⟨hj, hne, hn⟩
        exact ⟨hj, hne, fun h => hn (isEssentiallyDistinct_symm h)⟩
      · rintro ⟨hj, hne, hn⟩
        exact ⟨hj, hne, fun h => hn (isEssentiallyDistinct_symm h)⟩
    rw [hset]
    exact hdeg i hi
  obtain ⟨s', hsub, hpair, hsum, hcard⟩ :=
    Kakeya.exists_pairwise_not_of_degree_le_card s r hsymm hirr hdeg' y
  refine ⟨s', hsub, ?_, hsum, hcard⟩
  intro i hi j hj hij
  by_contra hn
  exact hpair hi hj hij ⟨hij, hn⟩

end Degree

/-! ### Two non-essentially-distinct tubes: the second lies near the first's core line -/

section TwoTubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {ι : Type*}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- A segment whose endpoints lie on the line `t ↦ x + t • v` lies on that line. -/
theorem segment_subset_range_line {x v P Q : E} {p q : ℝ} (hP : P = x + p • v)
    (hQ : Q = x + q • v) :
    segment ℝ P Q ⊆ Set.range fun t : ℝ ↦ x + t • v := by
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨θ, -, rfl⟩ := hz
  refine ⟨p + θ * (q - p), ?_⟩
  rw [hP, hQ]
  module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The carrier of a `δ`-tube lies in the `K δ`-neighbourhood of its own core line, for `1 ≤ K`. -/
theorem _root_.Tube.carrier_subset_cthickening_line_self {δ : NNReal} (T : Tube δ E) {K : ℝ}
    (hK : 1 ≤ K) :
    T.carrier ⊆ cthickening (K * (δ : ℝ)) (Set.range fun t : ℝ ↦ T.x + t • T.direction) := by
  rw [T.carrier_eq_cthickening]
  refine (cthickening_mono ?_ _).trans (cthickening_subset_of_subset _ ?_)
  · have := δ.coe_nonneg
    nlinarith
  · exact segment_subset_range_line (p := 0) (q := 1) (by simp) (by simp [Tube.direction])

/-- **Two `δ`-tubes that are not essentially distinct: the second lies in the
`C_n δ`-neighbourhood of the first's core line**, `C_n = Kakeya.Tube.tubeOverlapCoreClose.C n`.

`¬ IsEssentiallyDistinct` is `½ · max (|T|, |T'|) < |T ∩ T'|`; all `δ`-tubes have the same
volume (`Tube.volume_carrier_eq_volume_carrier`), so this is the hypothesis of the existing
`Kakeya.Tube.tubeOverlapCoreClose`, whose conclusion `T' ⊆ C_n · T` is, by
`Kakeya.Tube.dilate_carrier_eq_cthickening`, containment in the `C_n δ`-neighbourhood of a
segment on `T`'s core line.

This is the map's [ARGUED A6] with the tree's constant in place of the refined `5`: the only
route from `¬ IsEssentiallyDistinct` to a line neighbourhood in the tree is this one, and its
constant is `9 + 2·4ⁿ/c_n ≈ 101` in `ℝ³`. -/
theorem _root_.Tube.carrier_subset_cthickening_line_of_not_essDistinct {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (T T' : Tube δ E)
    (h : ¬ _root_.IsEssentiallyDistinct T.carrier T'.carrier) :
    T'.carrier ⊆ cthickening (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (δ : ℝ))
      (Set.range fun t : ℝ ↦ T.x + t • T.direction) := by
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCn
  have hCn1 : 1 < Cn := Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _
  have hCn0 : 0 < Cn := lt_trans zero_lt_one hCn1
  -- the overlap hypothesis of `tubeOverlapCoreClose`
  have hvol : volume T.carrier = volume T'.carrier :=
    _root_.Tube.volume_carrier_eq_volume_carrier T T'
  have hlt : (1 / 2 : ENNReal) * volume T.carrier < volume (T.carrier ∩ T'.carrier) := by
    unfold _root_.IsEssentiallyDistinct at h
    rw [hvol, max_self] at h
    rw [hvol]
    exact not_le.mp h
  have hsub := Kakeya.Tube.tubeOverlapCoreClose hδ hδ1 T T' hlt
  refine hsub.trans ?_
  rw [Kakeya.Tube.dilate_carrier_eq_cthickening T hCn0]
  refine cthickening_subset_of_subset _ ?_
  -- the dilated segment lies on the core line
  have hcm : T.center = (1 / 2 : ℝ) • (T.x + T.y) := by
    change midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
    rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
  refine segment_subset_range_line (p := (1 - Cn) / 2) (q := (1 + Cn) / 2) ?_ ?_
  · rw [AffineMap.homothety_apply, hcm]
    simp only [vsub_eq_sub, vadd_eq_add, Tube.direction]
    module
  · rw [AffineMap.homothety_apply, hcm]
    simp only [vsub_eq_sub, vadd_eq_add, Tube.direction]
    module

/-- **Line-based essential distinctness at radius `C_n δ` bounds the non-ED degree by
`A − 1`**, in the form `edDegree + 1 ≤ A`: the index `i` itself and every `j` not essentially
distinct from it lie in the family counted by the line through `T i`'s core. -/
theorem edDegree_add_one_le_of_isLineEssDistinctAt {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {A : ℕ}
    (hED : IsLineEssDistinctAt (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) A s T)
    {i : ι} (hi : i ∈ s) :
    edDegree s (fun j ↦ (T j).carrier) i + 1 ≤ A := by
  classical
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCn
  have hCn1 : 1 < Cn := Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _
  have hline := hED (T i).x (T i).direction (T i).norm_direction
  rw [lineNbhd_eq_cthickening_range] at hline
  set N : Set E := cthickening (Cn * (δ : ℝ)) (Set.range fun t : ℝ ↦ (T i).x + t • (T i).direction)
    with hN
  set G : Finset ι := s.filter fun j ↦ (T j).carrier ⊆ N with hG
  have hline' : G.card ≤ A := by
    refine le_trans (le_of_eq ?_) hline
    congr 1
  have hiG : i ∈ G := by
    rw [hG, Finset.mem_filter]
    exact ⟨hi, (T i).carrier_subset_cthickening_line_self hCn1.le⟩
  have hsub : {j ∈ (s : Set ι) | j ≠ i ∧
      ¬ _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier} ⊆
        ((G.erase i : Finset ι) : Set ι) := by
    rintro j ⟨hj, hji, hn⟩
    rw [Finset.mem_coe, Finset.mem_erase, hG, Finset.mem_filter]
    exact ⟨hji, hj, Tube.carrier_subset_cthickening_line_of_not_essDistinct hδ hδ1 (T i) (T j) hn⟩
  have hdeg : edDegree s (fun j ↦ (T j).carrier) i ≤ (G.erase i).card := by
    have := Set.ncard_le_ncard hsub (G.erase i).finite_toSet
    rwa [Set.ncard_coe_finset] at this
  calc edDegree s (fun j ↦ (T j).carrier) i + 1 ≤ (G.erase i).card + 1 := by omega
    _ = G.card := Finset.card_erase_add_one hiG
    _ ≤ A := hline'

/-- The degree bound in the form `edDegree ≤ A − 1`. -/
theorem edDegree_le_of_isLineEssDistinctAt {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {A : ℕ}
    (hED : IsLineEssDistinctAt (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) A s T)
    {i : ι} (hi : i ∈ s) :
    edDegree s (fun j ↦ (T j).carrier) i ≤ A - 1 := by
  have := edDegree_add_one_le_of_isLineEssDistinctAt hδ hδ1 hED hi
  omega

/-- **Line-ED at radius `C_n δ` ⇒ a pairwise essentially distinct subfamily with `1/A` of any
weight and of the cardinality.**  The composition of the degree bound with the greedy selection;
for `A = 0` the hypothesis is contradictory on a nonempty family, and on the empty family the
conclusion is trivial. -/
theorem exists_pairwise_of_isLineEssDistinctAt {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {A : ℕ}
    (hED : IsLineEssDistinctAt (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) A s T)
    (y : ι → ENNReal) :
    ∃ s' ⊆ s, (s' : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
      ∑ j ∈ s, y j ≤ (A - 1 + 1 : ℕ) * ∑ j ∈ s', y j ∧ s.card ≤ (A - 1 + 1) * s'.card :=
  exists_pairwise_of_edDegree_le s (fun j ↦ (T j).carrier)
    (fun _ hi => edDegree_le_of_isLineEssDistinctAt hδ hδ1 hED hi) y

end TwoTubes

end Kakeya.VeryNotSticky

end
