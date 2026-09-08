/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.GreedyIndependentSetCard
public import Kakeya.AffineMap
public import Kakeya.DimensionThree.MainLemma2.PlankPresentation
public import Kakeya.DimensionThree.MainLemma2.ThickPlankInterface
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct

/-!
# Plank selection inside a block

A single selected subfamily supplies `sel_card`, `essDistinct`, and
the shaded-mass retention used by `ThickPlankPresentation.fullness_ge`.

GWZ l.2021 defines the per-ball family `𝕋_B` to be essentially
distinct. Its normalized block `𝒫 = L(𝕋_{B,W})` inherits that
property by affine invariance. Here it is an explicit hypothesis `hED`:

* `edImages_of_edSegments` transports essential distinctness of the
  segment bodies to the images `L(T_p)` by
  `IsEssentiallyDistinct.image_affineEquiv`.
* `thickPlankSelection_of_edImages` applies
  `plankSubfamilySelection_card` to those images. Its conclusions
  supply essential distinctness, cardinality retention, and weight
  retention at `y p = |Y_p.shade|`.

## Simultaneous mass and cardinality retention

Two independent selections do not suffice: the selected subfamily
can depend on the weight, whereas both `sel_card` and `fullness_ge`
refer to the same `sel`. Nor can one generally retain constant
fractions of two arbitrary weights. In a clique on `D + 1` vertices,
independent sets are singletons and two weights can be supported on
different vertices.

The additional weight here is the constant `1`. The greedy selection
of `Kakeya.exists_pairwise_not_of_degree_le` is maximal, and every
maximal independent set in a graph of degree at most `D` contains
at least `1/(D + 1)` of the vertices. The combined lemma
`Kakeya.exists_pairwise_not_of_degree_le_card` therefore retains
both the prescribed mass and the cardinality in one selection.
`plankSubfamilySelection_card` applies it with the fixed constant
`Kakeya.VeryNotSticky.plankSelectionConstant C₀`.
-/

@[expose] public section

open Finset MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya.VeryNotSticky

open Kakeya

/-- Shorthand for the ambient space of the thick case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

universe u

/-! ### The selection, retaining a weight and the cardinality at once -/

/-- **The plank subfamily selection, with the cardinality clause**
(the twin of `Kakeya.VeryNotSticky.plankSubfamilySelection`).

Same hypotheses, same subfamily, one further conclusion: the selection keeps a `Csel⁻¹`
fraction of the *cardinality* as well as of the weight `y`. Both conclusions are about the
**same** `sel`, which is what `Kakeya.VeryNotSticky.ThickPlankPresentation` needs — its
`sel_card` and `fullness_ge` fields are retention clauses for two different weights on the one
field `sel`. See the module docstring for why a second call of the one-weight statement does
not do it, and why the constant weight in particular is free. -/
theorem plankSubfamilySelection_card {C₀ Csel : NNReal} (hC₀ : 1 ≤ C₀)
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
      (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j ≤ ∑ j ∈ sel, y j ∧
      (Csel : ENNReal)⁻¹ * ((s.card : ℕ) : ENNReal) ≤ ((sel.card : ℕ) : ENNReal) := by
  classical
  let D : ℕ := cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹)
  let r : ι → ι → Prop := fun i j =>
    i ≠ j ∧ ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
  have hsymm : ∀ i j, r i j → r j i := by
    intro i j hij
    rcases hij with ⟨hne, hnot⟩
    exact ⟨hne.symm, fun hji => hnot (isEssentiallyDistinct_symm hji)⟩
  have hirr : ∀ i, ¬ r i i := fun i h => (h.1 rfl).elim
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
  rcases exists_pairwise_not_of_degree_le_card s r hsymm hirr (D := D) hDeg y with
    ⟨sel, hselSub, hpair, hsum, hcard⟩
  have hcncl_pair : (sel : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) := by
    intro i hi j hj hij
    by_cases hED : IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
    · exact hED
    · exact (hpair hi hj hij ⟨hij, hED⟩).elim
  have hselConst_nn : plankSelectionConstant C₀ = (D : NNReal) + 1 := by
    simp [plankSelectionConstant, D]
  have hC_nn : (D : NNReal) + 1 ≤ Csel := by rwa [hselConst_nn] at hCsel
  have hC : ((D : NNReal) + 1 : ENNReal) ≤ (Csel : ENNReal) := by exact_mod_cast hC_nn
  have h1leCsel : (1 : NNReal) ≤ Csel :=
    le_trans (by norm_num : (1 : NNReal) ≤ (D : NNReal) + 1) hC_nn
  have hcnonzero : (Csel : ENNReal) ≠ 0 := by
    have hone : (1 : ENNReal) ≤ (Csel : ENNReal) := by exact_mod_cast h1leCsel
    exact (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hone))
  have hclear : ∀ X Z : ENNReal, X ≤ (Csel : ENNReal) * Z → (Csel : ENNReal)⁻¹ * X ≤ Z := by
    intro X Z hXZ
    calc
      (Csel : ENNReal)⁻¹ * X ≤ (Csel : ENNReal)⁻¹ * ((Csel : ENNReal) * Z) := by gcongr
      _ = Z := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel hcnonzero (ENNReal.coe_ne_top : (Csel : ENNReal) ≠ ⊤), one_mul]
  refine ⟨sel, hselSub, hcncl_pair, hclear _ _ ?_, hclear _ _ ?_⟩
  · have hsumNN : ∑ j ∈ s, y j ≤ ((D : NNReal) + 1 : ENNReal) * ∑ j ∈ sel, y j := by
      simpa using hsum
    exact le_trans hsumNN (by gcongr)
  · have hcardE : ((s.card : ℕ) : ENNReal) ≤ ((D : NNReal) + 1 : ENNReal) *
        ((sel.card : ℕ) : ENNReal) := by
      have h := (Nat.cast_le (α := ENNReal)).2 hcard
      simpa [Nat.cast_mul] using h
    exact le_trans hcardE (by gcongr)

/-! ### R31-a: essential distinctness transports to the normalised images -/

/-- **Segment essential distinctness transports to the images** (R31-a).

`IsEssentiallyDistinct` is preserved by every affine equivalence of `ℝ³`
(`IsEssentiallyDistinct.image_affineEquiv`), so the hypothesis that the segments of a ball are
pairwise essentially distinct — GWZ l.2021's definition of `𝕋_B`, supplied to the thick case as
the binder `hED` — gives the same for the images under the normalising map `L`, on any
subfamily. This is what feeds `Kakeya.VeryNotSticky.plankSubfamilySelection_card`. -/
theorem edImages_of_edSegments {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {B : bd.bι} (t : Finset bd.σ) (ht : t ⊆ bd.segs B)
    (hED : (bd.segs B : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier)
    (L : E₃ ≃ᵃ[ℝ] E₃) :
    (t : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (L '' (bd.Y p).carrier)
        (L '' (bd.Y q).carrier) := by
  intro p hp q hq hpq
  exact ((hED (ht hp) (ht hq) hpq).image_affineEquiv L)

/-! ### R31-b: the per-block selection -/

/-- **The per-block plank selection of the thick case** (R31-b).

Given, on the block `𝕋_{B,W} = {p ∈ segs B : blk p = j}`, an enclosing plank family `P`, an
inner family `K` of essentially distinct bodies of comparable volume, and any weight `y`, the
selection returns **one** subfamily `sel` which is

* pairwise essentially distinct as planks — the field
  `Kakeya.VeryNotSticky.ThickPlankPresentation.essDistinct`;
* of cardinality at least `C^{sel}(C₀)⁻¹ |𝕋_{B,W}|` — the field
  `Kakeya.VeryNotSticky.ThickPlankPresentation.sel_card`;
* carrying at least a `C^{sel}(C₀)⁻¹` fraction of `y` — at `y p = |Y_p.shade|` this is the
  numerator half of `Kakeya.VeryNotSticky.ThickPlankPresentation.fullness_ge`.

The loss is `Kakeya.VeryNotSticky.plankSelectionConstant bd.C₀`, which is `δ`-free: it is
`cardEssDistinctConvexInPrismConstant 3 ((clusterDilationConstant³ · plankEnclosureConstant
C₀)⁻¹) + 1`, a function of `bd.C₀` and the ambient dimension alone. It is the only place the
plank constant `CP` has to absorb a selection cost. -/
theorem thickPlankSelection_of_edImages {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {B : bd.bι} {j : bd.ω} {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    (P : bd.σ → Plank a' b' hab' hb1')
    (K : bd.σ → ConvexSpaceBody E₃)
    (hKP : ∀ p ∈ (bd.segs B).filter (fun p => bd.blk p = j), (K p).carrier ⊆ (P p).carrier)
    (hKvol : ∀ p ∈ (bd.segs B).filter (fun p => bd.blk p = j),
      8 * (a' : ENNReal) * (b' : ENNReal) ≤
        (plankEnclosureConstant bd.C₀ : ENNReal) * volume (K p).carrier)
    (hKed : (((bd.segs B).filter (fun p => bd.blk p = j)) : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (K p).carrier (K q).carrier)
    (y : bd.σ → ENNReal) :
    ∃ sel ⊆ (bd.segs B).filter (fun p => bd.blk p = j),
      (sel : Set bd.σ).Pairwise
        (fun p q => _root_.IsEssentiallyDistinct (P p).carrier (P q).carrier) ∧
      ((plankSelectionConstant bd.C₀ : NNReal) : ENNReal)⁻¹ *
          ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : ENNReal) ≤
        ((sel.card : ℕ) : ENNReal) ∧
      ((plankSelectionConstant bd.C₀ : NNReal) : ENNReal)⁻¹ *
          ∑ p ∈ (bd.segs B).filter (fun p => bd.blk p = j), y p ≤ ∑ p ∈ sel, y p := by
  classical
  obtain ⟨sel, hsub, hed, hy, hcard⟩ :=
    plankSubfamilySelection_card (C₀ := bd.C₀) (Csel := plankSelectionConstant bd.C₀)
      bd.hC₀ le_rfl ha' hab' hb1' ((bd.segs B).filter (fun p => bd.blk p = j)) P K hKP hKvol
      hKed y
  exact ⟨sel, hsub, hed, hcard, hy⟩

/-- **The shaded-mass instance of the selection** (`y p = |Y_p.shade|`), the weight
`Kakeya.VeryNotSticky.ThickPlankPresentation.fullness_ge` is stated over.

`fullness` is a ratio of sums, `(∑ |shade|)/(∑ |carrier|)`, so the field needs a lower bound
for the *shade* sum on `sel` against the shade sum on the block, and nothing else: the plank
carriers all have the common volume `8 a' b'`, and the block's own carriers are bounded below
by `8 a' b' / C^{enc}(C₀)` by `hKvol`. That lower bound is this corollary, and it comes with
the cardinality clause attached to the same `sel`.

The shading is read on the *unrescaled* segments `bd.Y`; `fullness` is a ratio of volumes and
the normalising map multiplies every volume by the same Jacobian, so no transport is needed
before the selection runs. -/
theorem thickPlankSelection_of_edImages_shade {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {B : bd.bι} {j : bd.ω} {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    (P : bd.σ → Plank a' b' hab' hb1')
    (K : bd.σ → ConvexSpaceBody E₃)
    (hKP : ∀ p ∈ (bd.segs B).filter (fun p => bd.blk p = j), (K p).carrier ⊆ (P p).carrier)
    (hKvol : ∀ p ∈ (bd.segs B).filter (fun p => bd.blk p = j),
      8 * (a' : ENNReal) * (b' : ENNReal) ≤
        (plankEnclosureConstant bd.C₀ : ENNReal) * volume (K p).carrier)
    (hKed : (((bd.segs B).filter (fun p => bd.blk p = j)) : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (K p).carrier (K q).carrier) :
    ∃ sel ⊆ (bd.segs B).filter (fun p => bd.blk p = j),
      (sel : Set bd.σ).Pairwise
        (fun p q => _root_.IsEssentiallyDistinct (P p).carrier (P q).carrier) ∧
      ((plankSelectionConstant bd.C₀ : NNReal) : ENNReal)⁻¹ *
          ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : ENNReal) ≤
        ((sel.card : ℕ) : ENNReal) ∧
      ((plankSelectionConstant bd.C₀ : NNReal) : ENNReal)⁻¹ *
          ∑ p ∈ (bd.segs B).filter (fun p => bd.blk p = j), volume (bd.Y p).shade ≤
        ∑ p ∈ sel, volume (bd.Y p).shade :=
  thickPlankSelection_of_edImages bd ha' hab' hb1' P K hKP hKvol hKed
    (fun p => volume (bd.Y p).shade)

/-! ### R31 at a degree bound: the additive twins

The refined text's per-ball capsule family is line-based `A₀`-essentially distinct and **not**
pairwise essentially distinct , so the
per-ball hypothesis of the thick case arrives as a **non-ED degree bound**
`{q ∈ segs B | q ≠ p ∧ ¬ IsEssentiallyDistinct (Y p) (Y q)}.ncard ≤ edMultiplicityConstant`
(`MainLemma2/LineEssDistinct.lean`, row E0; the constant is A-C1 symbol).  The three
theorems above are true — they are the degree-`0` instances — and keep their consumer
`thickPlankSelection_of_edImages`; the twins below take the degree bound and are what
`thickPlankPresentable_of_ballData` now reads.  The `q ≠ p` is load-bearing: a body of positive
finite volume is never essentially distinct from itself, and `exists_pairwise_not_of_degree_le`'s
relation has to be irreflexive. -/

/-- **The clustering relation has bounded degree, from a degree bound on the inner bodies**
(twin of `Kakeya.VeryNotSticky.plankClusterBound`).

If every inner body `K i` is non-essentially-distinct from at most `D_K` others, then the planks
clustered with `P i` number at most `(D_K + 1)(D + 1) − 1`, `D` the pairwise cluster constant:
inside `{i} ∪ cluster(i)` a greedy independent set for the `K`-relation that **contains `i`** (the
weight is the indicator of `i`) retains a `1/(D_K + 1)` fraction of the cardinality, and on it
`plankClusterBound` applies.  Stated as `ncard + 1 ≤ (D_K + 1)(D + 1)` to avoid `ℕ`-subtraction. -/
theorem plankClusterBound_of_degree {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    {ι : Type*} (s : Finset ι) (P : ι → Plank a' b' hab' hb1') (K : ι → ConvexSpaceBody E₃)
    (hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier)
    (hKvol : ∀ j ∈ s, 8 * (a' : ENNReal) * b'
      ≤ (plankEnclosureConstant C₀ : ENNReal) * volume ((K j).carrier : Set E₃))
    {D_K : ℕ}
    (hKdeg : ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧
      ¬ IsEssentiallyDistinct ((K i).carrier : Set E₃) ((K j).carrier : Set E₃)}.ncard ≤ D_K) :
    ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
          ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)}.ncard + 1
        ≤ (D_K + 1) * (cardEssDistinctConvexInPrismConstant 3
            (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) + 1) := by
  classical
  intro i hi
  set Dcl : ℕ := cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) with hDcl
  set J : Finset ι := s.filter fun j => j ≠ i ∧
    ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃) with hJ
  have hJs : J ⊆ s := Finset.filter_subset _ _
  have hiJ : i ∉ J := by simp [hJ]
  set Ji : Finset ι := insert i J with hJi
  have hJis : Ji ⊆ s := Finset.insert_subset hi hJs
  let r : ι → ι → Prop := fun a b => a ≠ b ∧
    ¬ IsEssentiallyDistinct ((K a).carrier : Set E₃) ((K b).carrier : Set E₃)
  have hsymm : ∀ a b, r a b → r b a :=
    fun _ _ h => ⟨h.1.symm, fun h' => h.2 (isEssentiallyDistinct_symm h')⟩
  have hirr : ∀ a, ¬ r a a := fun _ h => h.1 rfl
  have hdeg : ∀ a ∈ Ji, {b ∈ (Ji : Set ι) | r b a}.ncard ≤ D_K := by
    intro a ha
    refine le_trans (Set.ncard_le_ncard ?_ (s.finite_toSet.subset fun _ hb => hb.1))
      (hKdeg a (hJis ha))
    rintro b ⟨hb, hba, hn⟩
    exact ⟨hJis hb, hba, fun h => hn (isEssentiallyDistinct_symm h)⟩
  obtain ⟨J', hJ'sub, hpair, hsum, hcard⟩ :=
    Kakeya.exists_pairwise_not_of_degree_le_card Ji r hsymm hirr hdeg
      (fun j => if j = i then (1 : ENNReal) else 0)
  have hiJ' : i ∈ J' := by
    by_contra hne
    have h1 : ∑ j ∈ Ji, (if j = i then (1 : ENNReal) else 0) = 1 := by
      rw [Finset.sum_ite_eq' Ji i]
      simp [hJi]
    have h2 : ∑ j ∈ J', (if j = i then (1 : ENNReal) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [if_neg]
      intro h
      subst h
      exact hne hj
    rw [h1, h2, mul_zero] at hsum
    exact absurd hsum (by simp)
  have hedJ' : (J' : Set ι).Pairwise fun a b =>
      IsEssentiallyDistinct ((K a).carrier : Set E₃) ((K b).carrier : Set E₃) := by
    intro a ha b hb hab
    by_contra hn
    exact hpair ha hb hab ⟨hab, hn⟩
  have hcl := plankClusterBound hC₀ ha' hab' hb1' J' P K
    (fun j hj => hKP j (hJis (hJ'sub hj))) (fun j hj => hKvol j (hJis (hJ'sub hj))) hedJ' i hiJ'
  have hJ'set : {j ∈ (J' : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
      ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)} = ((J'.erase i : Finset ι) : Set ι) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro ⟨hj, hji, -⟩
      exact ⟨hji, hj⟩
    · rintro ⟨hji, hj⟩
      refine ⟨hj, hji, ?_⟩
      have hmem : j ∈ Ji := hJ'sub hj
      rw [hJi, Finset.mem_insert] at hmem
      rcases hmem with h | h
      · exact absurd h hji
      · rw [hJ, Finset.mem_filter] at h
        exact h.2.2
  rw [hJ'set, Set.ncard_coe_finset, Finset.card_erase_of_mem hiJ'] at hcl
  have hJcard : {j ∈ (s : Set ι) | j ≠ i ∧ ¬ IsEssentiallyDistinct
      ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)}.ncard = J.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [hJ]
  have hJicard : Ji.card = J.card + 1 := Finset.card_insert_of_notMem hiJ
  rw [hJcard]
  calc J.card + 1 = Ji.card := hJicard.symm
    _ ≤ (D_K + 1) * J'.card := hcard
    _ ≤ (D_K + 1) * (Dcl + 1) := by
        apply Nat.mul_le_mul_left
        omega

/-- **The plank subfamily selection with the cardinality clause, from a degree bound on the
inner bodies**.  Same conclusion; the pairwise hypothesis becomes the non-ED degree bound
`hKdeg`, and the selection constant's floor is `(D_K + 1) · C^{sel}(C₀)` (P3 floor form): the
cluster degree is `(D_K + 1)(D + 1) − 1` by `plankClusterBound_of_degree`, and the greedy
selection retains `1/(degree + 1) = 1/((D_K + 1) C^{sel}(C₀))`. -/
theorem plankSubfamilySelection_card_of_degree {C₀ Csel : NNReal} (hC₀ : 1 ≤ C₀) {D_K : ℕ}
    (hCsel : ((D_K : NNReal) + 1) * plankSelectionConstant C₀ ≤ Csel)
    {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b') (hb1' : b' ≤ 1)
    {ι : Type*} (s : Finset ι) (P : ι → Plank a' b' hab' hb1') (K : ι → ConvexSpaceBody E₃)
    (hKP : ∀ j ∈ s, ((K j).carrier : Set E₃) ⊆ (P j).carrier)
    (hKvol : ∀ j ∈ s, 8 * (a' : ENNReal) * b'
      ≤ (plankEnclosureConstant C₀ : ENNReal) * volume ((K j).carrier : Set E₃))
    (hKdeg : ∀ i ∈ s, {j ∈ (s : Set ι) | j ≠ i ∧
      ¬ IsEssentiallyDistinct ((K i).carrier : Set E₃) ((K j).carrier : Set E₃)}.ncard ≤ D_K)
    (y : ι → ENNReal) :
    ∃ sel ⊆ s, (sel : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) ∧
      (Csel : ENNReal)⁻¹ * ∑ j ∈ s, y j ≤ ∑ j ∈ sel, y j ∧
      (Csel : ENNReal)⁻¹ * ((s.card : ℕ) : ENNReal) ≤ ((sel.card : ℕ) : ENNReal) := by
  classical
  set Dcl : ℕ := cardEssDistinctConvexInPrismConstant 3
    (((clusterDilationConstant : ℝ) ^ 3 * (plankEnclosureConstant C₀ : ℝ))⁻¹) with hDcl
  have hpos : 1 ≤ (D_K + 1) * (Dcl + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set D : ℕ := (D_K + 1) * (Dcl + 1) - 1 with hD
  have hD1 : D + 1 = (D_K + 1) * (Dcl + 1) := by omega
  let r : ι → ι → Prop := fun i j =>
    i ≠ j ∧ ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
  have hsymm : ∀ i j, r i j → r j i := by
    intro i j hij
    rcases hij with ⟨hne, hnot⟩
    exact ⟨hne.symm, fun hji => hnot (isEssentiallyDistinct_symm hji)⟩
  have hirr : ∀ i, ¬ r i i := fun i h => (h.1 rfl).elim
  have hDeg : ∀ i ∈ s, {j ∈ (s : Set ι) | r j i}.ncard ≤ D := by
    intro i hi
    have hbound := plankClusterBound_of_degree hC₀ ha' hab' hb1' s P K hKP hKvol hKdeg i hi
    rw [← hDcl] at hbound
    have hset : {j ∈ (s : Set ι) | r j i} = {j ∈ (s : Set ι) | j ≠ i ∧
        ¬ IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)} := by
      ext j
      simp only [Set.mem_setOf_eq, r]
      constructor
      · rintro ⟨hjs, hjne, hnot⟩
        exact ⟨hjs, hjne, fun hij => hnot (isEssentiallyDistinct_symm hij)⟩
      · rintro ⟨hjs, hjne, hnot⟩
        exact ⟨hjs, hjne, fun hji => hnot (isEssentiallyDistinct_symm hji)⟩
    rw [hset]
    omega
  rcases Kakeya.exists_pairwise_not_of_degree_le_card s r hsymm hirr (D := D) hDeg y with
    ⟨sel, hselSub, hpair, hsum, hcard⟩
  have hcncl_pair : (sel : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)) := by
    intro i hi j hj hij
    by_cases hED : IsEssentiallyDistinct ((P i).carrier : Set E₃) ((P j).carrier : Set E₃)
    · exact hED
    · exact (hpair hi hj hij ⟨hij, hED⟩).elim
  have hpsc : plankSelectionConstant C₀ = (Dcl : NNReal) + 1 := by
    simp [plankSelectionConstant, hDcl]
  have hD1' : ((D : NNReal) + 1) = ((D_K : NNReal) + 1) * plankSelectionConstant C₀ := by
    rw [hpsc]
    have h : ((D : NNReal) + 1) = ((D + 1 : ℕ) : NNReal) := by push_cast; ring
    rw [h, hD1]
    push_cast
    ring
  have hC_nn : (D : NNReal) + 1 ≤ Csel := by rw [hD1']; exact hCsel
  have hC : ((D : NNReal) + 1 : ENNReal) ≤ (Csel : ENNReal) := by exact_mod_cast hC_nn
  have h1leCsel : (1 : NNReal) ≤ Csel :=
    le_trans (by norm_num : (1 : NNReal) ≤ (D : NNReal) + 1) hC_nn
  have hcnonzero : (Csel : ENNReal) ≠ 0 := by
    have hone : (1 : ENNReal) ≤ (Csel : ENNReal) := by exact_mod_cast h1leCsel
    exact (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hone))
  have hclear : ∀ X Z : ENNReal, X ≤ (Csel : ENNReal) * Z → (Csel : ENNReal)⁻¹ * X ≤ Z := by
    intro X Z hXZ
    calc
      (Csel : ENNReal)⁻¹ * X ≤ (Csel : ENNReal)⁻¹ * ((Csel : ENNReal) * Z) := by gcongr
      _ = Z := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel hcnonzero (ENNReal.coe_ne_top : (Csel : ENNReal) ≠ ⊤), one_mul]
  refine ⟨sel, hselSub, hcncl_pair, hclear _ _ ?_, hclear _ _ ?_⟩
  · have hsumNN : ∑ j ∈ s, y j ≤ ((D : NNReal) + 1 : ENNReal) * ∑ j ∈ sel, y j := by
      simpa using hsum
    exact le_trans hsumNN (by gcongr)
  · have hcardE : ((s.card : ℕ) : ENNReal) ≤ ((D : NNReal) + 1 : ENNReal) *
        ((sel.card : ℕ) : ENNReal) := by
      have h := (Nat.cast_le (α := ENNReal)).2 hcard
      simpa [Nat.cast_mul] using h
    exact le_trans hcardE (by gcongr)

/-- **The degree bound transports to the normalised images** (twin of
`Kakeya.VeryNotSticky.edImages_of_edSegments`, R31-a at a degree bound): essential distinctness
is preserved by every affine equivalence (`IsEssentiallyDistinct.image_affineEquiv`), so two
images that are *not* essentially distinct come from two segments that are not, and the count on
any subfamily `t ⊆ segs B` is at most the count on `segs B`. -/
theorem edImages_of_edSegments_degree {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {B : bd.bι} (t : Finset bd.σ) (ht : t ⊆ bd.segs B) {D_K : ℕ}
    (hEDdeg : ∀ p ∈ bd.segs B, {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
      ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤ D_K)
    (L : E₃ ≃ᵃ[ℝ] E₃) :
    ∀ p ∈ t, {q ∈ (t : Set bd.σ) | q ≠ p ∧
      ¬ _root_.IsEssentiallyDistinct (L '' (bd.Y p).carrier) (L '' (bd.Y q).carrier)}.ncard
        ≤ D_K := by
  intro p hp
  refine le_trans (Set.ncard_le_ncard ?_ ((bd.segs B).finite_toSet.subset fun _ hq => hq.1))
    (hEDdeg p (ht hp))
  rintro q ⟨hq, hqp, hn⟩
  exact ⟨ht hq, hqp, fun h => hn (h.image_affineEquiv L)⟩

/-- **The existing pairwise binder implies the degree binder at any bound**: pairwise essential distinctness is non-ED degree `0`
(`Kakeya.VeryNotSticky.edDegree_eq_zero_of_pairwise`).  This is what lets a consumer that still
carries the pairwise `hED` feed `thickPlankPresentable_of_ballData`. -/
theorem segsDegree_le_of_pairwise {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    (hED : ∀ B ∈ bd.bs, (bd.segs B : Set bd.σ).Pairwise
      fun p q => _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier) (D : ℕ) :
    ∀ B ∈ bd.bs, ∀ p ∈ bd.segs B, {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
      ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤ D := by
  intro B hB p hp
  have h0 := edDegree_eq_zero_of_pairwise (hED B hB) hp
  change edDegree (bd.segs B) (fun q => (bd.Y q).carrier) p ≤ D
  rw [h0]
  exact Nat.zero_le _

end Kakeya.VeryNotSticky

end

end
