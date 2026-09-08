/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.MetricSpace.Thickening
import Kakeya.Pigeonhole

/-!
# Boundedly overlapping covers

This file formalizes blueprint Subsection `subsec:covers`. Many arguments in this development
cover a set by balls that are allowed to overlap, but only boundedly often, and then sum a
quantity over the balls of the cover. The notion is fixed once here, with the overlap constant
made explicit, together with the consequences used downstream:

* `Kakeya.IsBoundedlyOverlappingCover` (blueprint `def:boundedlyOverlappingCover`): the notion
  itself;
* `Kakeya.IsBoundedlyOverlappingCover.sum_volume_le_mul_volume_iUnion` and
  `Kakeya.IsBoundedlyOverlappingCover.sum_volume_le_mul_volume_cthickening` (blueprint
  `lem:boundedOverlapVolumeSum`): the volume sum, in the two forms the blueprint records;
* `Kakeya.sum_volume_inter_ball_le` (blueprint `lem:boundedOverlapRestrictSum`): the restricted
  volume sum, which needs the overlap bound only and not the covering property;
* `Kakeya.exists_volume_inter_ball_ge` (blueprint `lem:coverAveragePigeonhole`): the averaging
  pigeonhole over the balls of a cover;
* `Kakeya.exists_subordinatePartition` (blueprint `lem:subordinatePartition`) and
  `Kakeya.sum_volume_inter_partition_eq` (blueprint `lem:partitionMassIdentity`): the
  measurable partition subordinate to a cover and the *exact* mass identity it supplies —
  which is what a cover, being lossy by a factor `D`, does not give;
* `Kakeya.exists_separatedNetCover` (blueprint `lem:separatedNetCover`) and its five
  ingredients: the covers produced by a maximal separated set;
* `Kakeya.exists_mem_volume_inter_ball_ge` (blueprint `lem:massSubball`): a set of bounded
  diameter has a subball of comparable radius carrying a proportional share of its mass.

The overlap constant `D` is always carried explicitly; in every application in this development
it depends only on the ambient dimension.
-/

@[expose] public section

namespace Kakeya

open MeasureTheory Metric

open scoped Classical in
/-- A finite family of balls `(B i)_{i ∈ s}`, where `B i = ball (c i) (r i)`, is a
*`D`-boundedly overlapping cover* of `S` if it covers `S` and no point of the ambient
space lies in more than `D` of the balls (blueprint `def:boundedlyOverlappingCover`). -/
structure IsBoundedlyOverlappingCover {E : Type*} [PseudoMetricSpace E] {ι : Type*}
    (s : Finset ι) (c : ι → E) (r : ι → ℝ) (D : ℕ) (S : Set E) : Prop where
  /-- The balls cover `S`. -/
  subset_iUnion : S ⊆ ⋃ i ∈ s, ball (c i) (r i)
  /-- No point lies in more than `D` of the balls. -/
  card_filter_le : ∀ x : E, {i ∈ s | x ∈ ball (c i) (r i)}.card ≤ D

/-! ### Volume sums over the balls of a cover -/

section VolumeSum

variable {E : Type*} [PseudoMetricSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
  {ι : Type*} {s : Finset ι} {c : ι → E} {r : ι → ℝ} {D : ℕ} {S : Set E}

open scoped Classical in
/-- **Volume sum of a boundedly overlapping cover** (blueprint
`lem:boundedOverlapVolumeSum`, first inequality).

Pointwise `∑ i, 1_{B i} ≤ D · 1_{⋃ i, B i}`: off the union the left-hand side vanishes, and
on it the sum is at most `D`. Integrating gives the estimate.

As for `Kakeya.sum_volume_inter_ball_le`, only the overlap bound is used — the covering
property, and hence the covered set `S`, play no role — so the hypothesis is the field
`IsBoundedlyOverlappingCover.card_filter_le` rather than the structure itself. -/
theorem IsBoundedlyOverlappingCover.sum_volume_le_mul_volume_iUnion (s : Finset ι) (c : ι → E)
    (r : ι → ℝ) {D : ℕ} (hoverlap : ∀ x : E, {i ∈ s | x ∈ ball (c i) (r i)}.card ≤ D) :
    ∑ i ∈ s, volume (ball (c i) (r i)) ≤
      (D : ENNReal) * volume (⋃ i ∈ s, ball (c i) (r i)) := by
  let A : ι → Set E := fun i => ball (c i) (r i)
  let U : Set E := ⋃ i ∈ s, A i
  have hmeas : ∀ i ∈ s, MeasurableSet (A i) := fun i _ => measurableSet_ball
  have hmeasU : MeasurableSet U := Finset.measurableSet_biUnion s hmeas
  have hsub : ∀ i ∈ s, A i ⊆ U := fun i hi x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
  calc
    ∑ i ∈ s, volume (A i)
      = ∑ i ∈ s, volume (A i ∩ U) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Set.inter_eq_self_of_subset_left (hsub i hi)]
    _ = ∑ i ∈ s, ∫⁻ x in U, (A i).indicator (fun _ => (1 : ENNReal)) x := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [setLIntegral_indicator (hmeas i hi) (fun _ => (1 : ENNReal)),
          setLIntegral_const, one_mul]
    _ = ∫⁻ x in U, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x := by
        rw [lintegral_finsetSum (μ := volume.restrict U) s
          (fun i hi => measurable_const.indicator (hmeas i hi))]
    _ = ∫⁻ x in U, ({i ∈ s | x ∈ A i}.card : ENNReal) := by
        refine setLIntegral_congr_fun hmeasU ?_
        intro x hx
        classical
        simp only [Set.indicator_apply, Finset.sum_boole]
    _ ≤ ∫⁻ x in U, (D : ENNReal) := by
        refine setLIntegral_mono_ae (g := fun _ => (D : ENNReal)) ?_ ?_
        · exact aemeasurable_const
        · exact Filter.Eventually.of_forall (fun x hx => by exact_mod_cast hoverlap x)
    _ = (D : ENNReal) * volume U := by
        rw [setLIntegral_const]

omit [MeasureSpace E] [OpensMeasurableSpace E] in
/-- The balls of a family of radius `ρ` each meeting `S` are contained in the
`2ρ`-neighbourhood of `S` (blueprint `lem:boundedOverlapVolumeSum`, the containment used for
its second inequality).

The radius has to be *doubled*: the balls are only assumed to meet `S`, so their centres need
not lie in `S`. (For `ρ < 0` the balls are empty and the statement is vacuous, so no
positivity hypothesis on `ρ` is needed.) -/
theorem iUnion_ball_subset_cthickening {ρ : ℝ}
    (hmeets : ∀ i ∈ s, (ball (c i) ρ ∩ S).Nonempty) :
    (⋃ i ∈ s, ball (c i) ρ) ⊆ cthickening (2 * ρ) S := by
  intro z hz
  rcases Set.mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
  rcases hmeets i hi with ⟨y, hy⟩
  refine Metric.mem_cthickening_of_dist_le z y (2 * ρ) S hy.2 ?_
  have hzci : dist z (c i) < ρ := by simpa using hzi
  have hyci : dist (c i) y < ρ := by simpa [dist_comm] using hy.1
  exact le_of_lt (by nlinarith [hzci, hyci, dist_triangle z (c i) y])

/-- **Volume sum of a boundedly overlapping cover, neighbourhood form** (blueprint
`lem:boundedOverlapVolumeSum`, second inequality).

If all the balls of the cover have the same radius `ρ` and each meets `S`, then
`∑ i, |B i| ≤ D |N_{2ρ}(S)|`. This is the form used in the thin case, where `S` is a tube
segment and the balls are the `δ`-balls of a cover of it. -/
theorem IsBoundedlyOverlappingCover.sum_volume_le_mul_volume_cthickening {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : IsBoundedlyOverlappingCover s c (fun _ => ρ) D S)
    (hmeets : ∀ i ∈ s, (ball (c i) ρ ∩ S).Nonempty) :
    ∑ i ∈ s, volume (ball (c i) ρ) ≤ (D : ENNReal) * volume (cthickening (2 * ρ) S) := by
  classical
  have _ : 0 ≤ 2 * ρ := by positivity
  let A : ι → Set E := fun i => ball (c i) ρ
  let U : Set E := cthickening (2 * ρ) S
  have hmeas : ∀ i ∈ s, MeasurableSet (A i) := fun i _ => measurableSet_ball
  have hmeasU : MeasurableSet U := Metric.isClosed_cthickening.measurableSet
  have hsub : ∀ i ∈ s, A i ⊆ U := fun i hi x hx =>
    iUnion_ball_subset_cthickening hmeets (Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩)
  calc
    ∑ i ∈ s, volume (A i)
      = ∑ i ∈ s, volume (A i ∩ U) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Set.inter_eq_self_of_subset_left (hsub i hi)]
    _ = ∑ i ∈ s, ∫⁻ x in U, (A i).indicator (fun _ => (1 : ENNReal)) x := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [setLIntegral_indicator (hmeas i hi) (fun _ => (1 : ENNReal)),
          setLIntegral_const, one_mul]
    _ = ∫⁻ x in U, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x := by
        rw [lintegral_finsetSum (μ := volume.restrict U) s
          (fun i hi => measurable_const.indicator (hmeas i hi))]
    _ = ∫⁻ x in U, ({i ∈ s | x ∈ A i}.card : ENNReal) := by
        refine setLIntegral_congr_fun hmeasU ?_
        intro x hx
        classical
        simp only [Set.indicator_apply, Finset.sum_boole]
    _ ≤ ∫⁻ x in U, (D : ENNReal) := by
        refine setLIntegral_mono_ae (g := fun _ => (D : ENNReal)) ?_ ?_
        · exact aemeasurable_const
        · exact Filter.Eventually.of_forall (fun x hx => by exact_mod_cast h.card_filter_le x)
    _ = (D : ENNReal) * volume U := by
        rw [setLIntegral_const]

open scoped Classical in
/-- **Restricted volume sum of a boundedly overlapping cover** (blueprint
`lem:boundedOverlapRestrictSum`).

Integrating the pointwise overlap bound `∑ i, 1_{B i} ≤ D` over a measurable set `F` gives
`∑ i, |F ∩ B i| ≤ D |F|`.

Only the overlap bound is used, not the covering property, so the hypothesis is the field
`IsBoundedlyOverlappingCover.card_filter_le` rather than the structure itself; the applications
in the thin case are to families (the `A`-balls at an `A`-separated set) which are *not*
covers of the set being estimated. -/
theorem sum_volume_inter_ball_le (s : Finset ι) (c : ι → E) (r : ι → ℝ) {D : ℕ}
    (hoverlap : ∀ x : E, {i ∈ s | x ∈ ball (c i) (r i)}.card ≤ D)
    {F : Set E} (hF : MeasurableSet F) :
    ∑ i ∈ s, volume (F ∩ ball (c i) (r i)) ≤ (D : ENNReal) * volume F := by
  let hmeas : ∀ i ∈ s, MeasurableSet (ball (c i) (r i)) := fun i _ => measurableSet_ball
  let hind : ∀ i ∈ s, Measurable ((ball (c i) (r i)).indicator (fun _ => (1 : ENNReal))) :=
    fun i hi => measurable_const.indicator (hmeas i hi)
  calc
    ∑ i ∈ s, volume (F ∩ ball (c i) (r i))
      = ∑ i ∈ s, volume (ball (c i) (r i) ∩ F) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Set.inter_comm]
    _ = ∑ i ∈ s, ∫⁻ x in F, (ball (c i) (r i)).indicator (fun _ => (1 : ENNReal)) x ∂volume := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [setLIntegral_indicator (hmeas i hi) (fun _ => (1 : ENNReal)),
          setLIntegral_const, one_mul]
    _ = ∫⁻ x in F, ∑ i ∈ s, (ball (c i) (r i)).indicator (fun _ => (1 : ENNReal)) x ∂volume := by
        rw [lintegral_finsetSum (μ := volume.restrict F) s hind]
    _ = ∫⁻ x in F, ({i ∈ s | x ∈ ball (c i) (r i)}.card : ENNReal) ∂volume := by
        refine setLIntegral_congr_fun hF ?_
        intro x hx
        simp only [Set.indicator_apply, Finset.sum_boole]
    _ ≤ ∫⁻ x in F, (D : ENNReal) ∂volume := by
        refine setLIntegral_mono_ae (g := fun _ => (D : ENNReal)) ?_ ?_
        · exact (aemeasurable_const : AEMeasurable (fun _ : E => (D : ENNReal)) (volume.restrict F))
        · exact Filter.Eventually.of_forall (fun x hx => by exact_mod_cast hoverlap x)
    _ = (D : ENNReal) * volume F := by
        rw [setLIntegral_const]

omit [OpensMeasurableSpace E] in
/-- **Averaging over the balls of a cover** (blueprint `lem:coverAveragePigeonhole`).

A set `Z` covered by the balls `B i`, `i ∈ s`, and of measure at least `α ∑ i, |B i|`, is an
`α`-fraction of at least one of them.

The blueprint states this for balls of a *common* radius, so that `∑ i, |B i| = |s| · v`; the
argument needs no such hypothesis, since `α ∑ i, |B i| = ∑ i, α |B i|` and the pigeonhole
`ENNReal.exists_le_of_sum_le` compares the two sums termwise. (The generic
`Finset.exists_le_of_sum_le` does not apply: it needs a cancellative ordered monoid, which
`ℝ≥0∞` is not.) -/
theorem exists_volume_inter_ball_ge (hs : s.Nonempty) (c : ι → E) (r : ι → ℝ)
    {Z : Set E} (hZ : Z ⊆ ⋃ i ∈ s, ball (c i) (r i))
    {α : ENNReal} (hvol : α * ∑ i ∈ s, volume (ball (c i) (r i)) ≤ volume Z) :
    ∃ i ∈ s, α * volume (ball (c i) (r i)) ≤ volume (Z ∩ ball (c i) (r i)) := by
  have hZ_eq : Z = ⋃ i ∈ s, (Z ∩ ball (c i) (r i)) := by
    apply le_antisymm
    · intro x hx
      rcases Set.mem_iUnion₂.mp (hZ hx) with ⟨i, hi, hxball⟩
      exact Set.mem_biUnion hi ⟨hx, hxball⟩
    · intro x hx
      aesop
  have hmeas : volume Z ≤ ∑ i ∈ s, volume (Z ∩ ball (c i) (r i)) := by
    calc
      volume Z ≤ volume (⋃ i ∈ s, (Z ∩ ball (c i) (r i))) := by
        exact measure_mono (le_of_eq hZ_eq)
      _ ≤ ∑ i ∈ s, volume (Z ∩ ball (c i) (r i)) := by
        exact measure_biUnion_finset_le s (fun i => Z ∩ ball (c i) (r i))
  have hsum : ∑ i ∈ s, α * volume (ball (c i) (r i)) ≤ volume Z := by
    rwa [Finset.mul_sum] at hvol
  have hle : ∑ i ∈ s, α * volume (ball (c i) (r i)) ≤
      ∑ i ∈ s, volume (Z ∩ ball (c i) (r i)) :=
    le_trans hsum hmeas
  exact ENNReal.exists_le_of_sum_le hs hle

end VolumeSum

/-! ### The subordinate partition -/

section Partition

variable {E : Type*}

/-- **A measurable partition subordinate to a boundedly overlapping cover** (blueprint
`lem:subordinatePartition`).

Given a finite family of measurable sets `(B i)_{i ∈ s}` there are measurable pieces
`P i ⊆ B i`, pairwise disjoint, with the same union. In the applications `(B i)` is the family
of balls of a `D`-boundedly overlapping cover of `S`, and the conclusion says that every point
of `S ⊆ ⋃ i, B i = ⋃ i, P i` lies in `P i` for exactly one `i`.

This is what lets a cover be used as if it were a partition: it is needed whenever a
construction is carried out separately in each ball and the results have to be amalgamated,
since for a genuine cover the pieces belonging to overlapping balls interfere.

The statement is for an arbitrary finite family rather than for balls, and it is existential:
the blueprint exhibits the pieces `B_{i_k} \ ⋃_{l < k} B_{i_l}` for a chosen enumeration of
`s`, but nothing downstream depends on that choice. -/
theorem exists_subordinatePartition [MeasurableSpace E] {ι : Type*} (s : Finset ι)
    (B : ι → Set E) (hB : ∀ i ∈ s, MeasurableSet (B i)) :
    ∃ P : ι → Set E, (∀ i ∈ s, P i ⊆ B i) ∧ (∀ i ∈ s, MeasurableSet (P i)) ∧
      (s : Set ι).PairwiseDisjoint P ∧ ⋃ i ∈ s, P i = ⋃ i ∈ s, B i := by
  classical
  let e : s ≃ Fin s.card := Finset.equivFin s
  let G : Fin s.card → Set E := fun k => B (e.symm k)
  let P : ι → Set E := fun i => if h : i ∈ s then disjointed G (e ⟨i, h⟩) else ∅
  have hmeasG : ∀ k : Fin s.card, MeasurableSet (G k) := by
    intro k
    exact hB (e.symm k) (e.symm k).property
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp [P]
    rw [dif_pos hi]
    exact (disjointed_subset G (e ⟨i, hi⟩)).trans (by
      simp [G])
  · intro i hi
    dsimp [P]
    rw [dif_pos hi]
    exact disjointedRec (f := G) (p := MeasurableSet)
      (fun t k ht => ht.diff (hmeasG k)) (hmeasG (e ⟨i, hi⟩))
  · intro a ha b hb hab
    change Disjoint (P a) (P b)
    have ha' : a ∈ s := by simpa
    have hb' : b ∈ s := by simpa
    dsimp [P]
    rw [dif_pos ha', dif_pos hb']
    exact (disjoint_disjointed G) (by
      intro hne
      exact hab (by
        have hsub : (⟨a, ha'⟩ : s) = ⟨b, hb'⟩ := e.injective hne
        exact congrArg (fun x : s => (x : ι)) hsub))
  · calc
      ⋃ i ∈ s, P i = ⋃ i : (s : Set ι), P i.1 := by
        simp [Set.iUnion_subtype]
      _ = ⋃ k : Fin s.card, disjointed G k := by
        apply Set.iUnion_congr_of_surjective e e.surjective
        intro i
        simp [P]
      _ = ⋃ k : Fin s.card, G k := iUnion_disjointed (f := G)
      _ = ⋃ i : (s : Set ι), B i := by
        apply Set.iUnion_congr_of_surjective e.symm e.symm.surjective
        intro k
        rfl
      _ = ⋃ i ∈ s, B i := by
        simp [Set.iUnion_subtype]

/-- **Mass identity for a partition** (blueprint `lem:partitionMassIdentity`).

Splitting a finite family of measurable sets along the pieces of a finite measurable partition
loses *no* mass at all, whereas splitting it along the balls of a cover would only give
two-sided bounds with a factor `D`. This exactness is the reason the subordinate partition of
`Kakeya.exists_subordinatePartition` is worth the trouble.

The sets `F j` being split are *not* assumed measurable: the pieces `P i` are measurable,
pairwise disjoint and cover `F j`, so Carathéodory additivity applies to an arbitrary `F j`.
This matters at the point of use, `Kakeya.ThinCase.amalgamateCost`, which has no
measurability hypothesis on its shadings. -/
theorem sum_volume_inter_partition_eq [MeasureSpace E] {ι κ : Type*} (s : Finset ι)
    (P : ι → Set E) (hdisj : (s : Set ι).PairwiseDisjoint P)
    (hP : ∀ i ∈ s, MeasurableSet (P i))
    (t : Finset κ) (F : κ → Set E)
    (hcov : ∀ j ∈ t, F j ⊆ ⋃ i ∈ s, P i) :
    ∑ j ∈ t, ∑ i ∈ s, volume (F j ∩ P i) = ∑ j ∈ t, volume (F j) := by
  have hmeas_union : MeasurableSet (⋃ i ∈ s, P i) :=
    Finset.measurableSet_biUnion s hP
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hb : (volume.restrict (F j)) (⋃ i ∈ s, P i) =
      ∑ i ∈ s, (volume.restrict (F j)) (P i) :=
    MeasureTheory.measure_biUnion_finset hdisj hP
  have hL : (volume.restrict (F j)) (⋃ i ∈ s, P i) = volume (F j) := by
    rw [MeasureTheory.Measure.restrict_apply hmeas_union]
    rw [Set.inter_eq_self_of_subset_right (hcov j hj)]
  have hR : (∑ i ∈ s, (volume.restrict (F j)) (P i)) = ∑ i ∈ s, volume (F j ∩ P i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [MeasureTheory.Measure.restrict_apply (hP i hi)]
    rw [Set.inter_comm]
  rw [← hR, ← hL, hb]

end Partition

/-! ### Covers produced by a maximal separated set

Throughout this section a subset `N` of a metric space is *`r`-separated* when
`r ≤ dist y z` for all distinct `y, z ∈ N`, and it is a *maximal* `r`-separated subset of `S`
when moreover `N ⊆ S` and every point of `S` is at distance `< r` from some point of `N` —
equivalently, no point of `S` can be added to `N` keeping `r`-separation. Both conditions are
spelled out inline rather than through `Metric.IsSeparated`, whose convention is the *strict*
inequality `r < dist y z`, and through `Metric.IsCover`, which uses closed balls. -/

section Separated

/-- **Constant in Lemma `lem:separatedNetCover`** (blueprint
`def:separatedNetCoverConstant`).

The overlap constant `5 ^ n` of the two covers built from a maximal separated set in
dimension `n`; it arises from a volume comparison between balls of radius `r / 2` and
`5r / 2`. It depends only on `n`. -/
def separatedNetCoverConstant (n : ℕ) : ℕ := 5 ^ n

lemma one_le_separatedNetCoverConstant (n : ℕ) : 1 ≤ separatedNetCoverConstant n :=
  Nat.one_le_pow _ _ (by norm_num)

/-- **Half-radius balls at a separated set are disjoint** (blueprint
`lem:separatedNetDisjoint`). -/
theorem pairwiseDisjoint_ball_half {E : Type*} [PseudoMetricSpace E] {N : Set E} {r : ℝ}
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) :
    N.PairwiseDisjoint fun y => ball y (r / 2) := by
  intro y hy z hz hyz
  exact Metric.ball_disjoint_ball (by linarith [hsep y hy z hz hyz])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Cardinality of a separated set in a ball** (blueprint `lem:separatedNetCard`).

An `r`-separated subset of a ball of radius `R` is finite of cardinality at most
`(1 + 2R/r) ^ n`; in particular `|N| ≲ 1` when `R ≲ r`. The proof compares the volumes of the
disjoint balls `B(y, r/2)`, `y ∈ N`, all contained in `B(x₀, R + r/2)`.

The hypothesis `0 ≤ R` cannot be dropped: for `R < -r/2` the ball is empty, so `N` is empty,
while the bound `(1 + 2R/r) ^ n` is negative in odd dimensions. The repository's
`Metric.packingNumber_mul_pow_le_volume_cthickening` thickens by `r` where the disjoint balls
have radius `r/2`, so it yields only `(2 + 2R/r) ^ n`; the sharp constant needs the direct
volume comparison. -/
theorem finite_and_card_le_of_separated {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (x₀ : E) {N : Set E}
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) (hN : N ⊆ ball x₀ R) :
    N.Finite ∧ (N.ncard : ℝ) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E := by
  classical
  let n := Module.finrank ℝ E
  let v₁ : ENNReal := volume (ball (0 : E) 1)
  have hr2 : 0 < r / 2 := by positivity
  have hr2nonneg : 0 ≤ r / 2 := le_of_lt hr2
  have hRr2 : 0 < R + r / 2 := by positivity
  have hRr2nonneg : 0 ≤ R + r / 2 := le_of_lt hRr2
  have hv₁a : v₁ ≠ 0 := ne_of_gt (Metric.measure_ball_pos (volume : Measure E) (0 : E) one_pos)
  have hv₁b : v₁ ≠ ⊤ := ne_of_lt (MeasureTheory.measure_ball_lt_top (x := (0 : E)) (r := 1))
  have hvolball (x : E) (t : ℝ) (ht : 0 < t) :
      volume (ball x t) = ENNReal.ofReal (t ^ n) * v₁ := by
    dsimp [n, v₁]
    exact MeasureTheory.Measure.addHaar_ball_of_pos (μ := volume) x ht
  have hcard_fin (T : Finset E) (hTN : (T : Set E) ⊆ N) :
      (T.card : ℝ) ≤ (1 + 2 * R / r) ^ n := by
    have hdisj : (T : Set E).PairwiseDisjoint (fun y => ball y (r / 2)) :=
      (pairwiseDisjoint_ball_half hsep).subset hTN
    have hmeas : ∀ y ∈ T, MeasurableSet (ball y (r / 2)) := fun y _ => measurableSet_ball
    have hsum : (∑ y ∈ T, volume (ball y (r / 2))) =
        volume (⋃ y ∈ T, ball y (r / 2)) :=
      (MeasureTheory.measure_biUnion_finset hdisj hmeas).symm
    have hsub : (⋃ y ∈ T, ball y (r / 2)) ⊆ ball x₀ (R + r / 2) := by
      intro z hz
      rcases Set.mem_iUnion₂.mp hz with ⟨y, hyT, hzy⟩
      rw [Metric.mem_ball]
      have hyN : dist y x₀ < R := Metric.mem_ball.mp (hN (hTN hyT))
      calc
        dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle z y x₀
        _ < r / 2 + R := add_lt_add (Metric.mem_ball.mp hzy) hyN
        _ = R + r / 2 := by ring
    have hvol_le : (∑ y ∈ T, volume (ball y (r / 2))) ≤ volume (ball x₀ (R + r / 2)) := by
      rw [hsum]
      exact measure_mono hsub
    have hsum_vol : (∑ y ∈ T, volume (ball y (r / 2))) =
        (T.card : ENNReal) * (ENNReal.ofReal ((r / 2) ^ n) * v₁) := by
      calc
        ∑ y ∈ T, volume (ball y (r / 2))
            = ∑ y ∈ T, (ENNReal.ofReal ((r / 2) ^ n) * v₁) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [hvolball y (r / 2) hr2]
        _ = (T.card : ENNReal) * (ENNReal.ofReal ((r / 2) ^ n) * v₁) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    have hcancel : (T.card : ENNReal) * ENNReal.ofReal ((r / 2) ^ n) ≤
        ENNReal.ofReal ((R + r / 2) ^ n) := by
      have h0 : ((T.card : ENNReal) * ENNReal.ofReal ((r / 2) ^ n)) * v₁ ≤
          ENNReal.ofReal ((R + r / 2) ^ n) * v₁ := by
        calc
          ((T.card : ENNReal) * ENNReal.ofReal ((r / 2) ^ n)) * v₁
              = ∑ y ∈ T, volume (ball y (r / 2)) := by
                rw [mul_assoc, ← hsum_vol]
          _ ≤ volume (ball x₀ (R + r / 2)) := by
                exact hvol_le
          _ = ENNReal.ofReal ((R + r / 2) ^ n) * v₁ := by
                rw [hvolball x₀ (R + r / 2) hRr2]
      exact (ENNReal.mul_le_mul_iff_left hv₁a hv₁b).mp h0
    have hreal : (T.card : ℝ) * (r / 2) ^ n ≤ (R + r / 2) ^ n := by
      have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcancel
      simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (pow_nonneg hr2nonneg n),
        ENNReal.toReal_ofReal (pow_nonneg hRr2nonneg n)] using hle
    have hpowpos : 0 < (r / 2) ^ n := pow_pos hr2 n
    have hrec : (T.card : ℝ) ≤ (R + r / 2) ^ n / (r / 2) ^ n := (le_div_iff₀ hpowpos).mpr hreal
    have hpoweq : (R + r / 2) ^ n / (r / 2) ^ n = (1 + 2 * R / r) ^ n := by
      rw [← div_pow]
      congr 1
      field_simp [ne_of_gt hr]
      ring
    rwa [hpoweq] at hrec
  rcases Set.finite_or_infinite N with hNfin | hNinf
  · refine ⟨hNfin, ?_⟩
    letI : Fintype (↥N) := hNfin.fintype
    have hsubT : (N.toFinset : Set E) ⊆ N := by
      intro x hx
      exact Set.mem_toFinset.mp hx
    have hb := hcard_fin N.toFinset hsubT
    have hcard_eq : (N.ncard : ℝ) = (N.toFinset.card : ℝ) := by
      congr 1
      exact Set.ncard_eq_toFinset_card' N
    exact hcard_eq.trans_le hb
  · exfalso
    let M : ℕ := Nat.ceil ((1 + 2 * R / r) ^ n) + 1
    have hlt : (1 + 2 * R / r) ^ n < (M : ℝ) := by
      have h1 : (1 + 2 * R / r) ^ n ≤ (Nat.ceil ((1 + 2 * R / r) ^ n) : ℝ) :=
        Nat.le_ceil _
      have h2 : (Nat.ceil ((1 + 2 * R / r) ^ n) : ℝ) < (M : ℝ) := by
        dsimp [M]
        exact_mod_cast (Nat.lt_succ_self _)
      linarith
    obtain ⟨T, hTN, hTcard⟩ := hNinf.exists_subset_card_eq M
    have hb := hcard_fin T hTN
    have hMle : (M : ℝ) ≤ (1 + 2 * R / r) ^ n := by
      rwa [hTcard] at hb
    exact (not_lt_of_ge hMle) hlt

open scoped Classical in
/-- **Overlap of the balls at a separated set** (blueprint `lem:separatedNetOverlapBound`).

For an `r`-separated set `N` and a radius `t ≤ 2r`, no point lies in more than
`separatedNetCoverConstant n` of the balls `B(y, t)`, `y ∈ N`: the relevant centres lie in
`B(x, t) ⊆ B(x, 2r)` and are `r`-separated, so `finite_and_card_le_of_separated` with `R = 2r`
bounds their number by `(1 + 4) ^ n = 5 ^ n`. -/
theorem card_filter_ball_le {r t : ℝ} (hr : 0 < r) (ht : t ≤ 2 * r) {N : Finset E}
    (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) (x : E) :
    {y ∈ N | x ∈ ball y t}.card ≤ separatedNetCoverConstant (Module.finrank ℝ E) := by
  let F : Finset E := {y ∈ N | x ∈ ball y t}
  let M : Set E := {y ∈ (N : Set E) | x ∈ ball y t}
  have hM_eq : M = (F : Set E) := by
    ext y
    simp [F, M]
  have hsepr : ∀ y ∈ M, ∀ z ∈ M, y ≠ z → r ≤ dist y z := by
    intro y hy z hz hyz
    exact hsep y hy.1 z hz.1 hyz
  have hMball : M ⊆ ball x (2 * r) := by
    intro y hy
    rw [Metric.mem_ball]
    calc
      dist y x = dist x y := dist_comm y x
      _ < t := Metric.mem_ball.mp hy.2
      _ ≤ 2 * r := ht
  have hcardM : (M.ncard : ℝ) ≤ (1 + 2 * (2 * r) / r) ^ Module.finrank ℝ E :=
    (finite_and_card_le_of_separated hr (by positivity) x hsepr hMball).2
  have hcardF : (F.card : ℝ) ≤ (1 + 2 * (2 * r) / r) ^ Module.finrank ℝ E := by
    simpa [hM_eq, Set.ncard_coe_finset] using hcardM
  have hmain : (F.card : ℝ) ≤ (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ) := by
    calc
      (F.card : ℝ) ≤ (1 + 2 * (2 * r) / r) ^ Module.finrank ℝ E := hcardF
      _ = (5 : ℝ) ^ Module.finrank ℝ E := by
        have hcalc : (1 + 2 * (2 * r) / r : ℝ) = 5 := by
          field_simp [ne_of_gt hr]
          ring
        rw [hcalc]
      _ = (separatedNetCoverConstant (Module.finrank ℝ E) : ℝ) := by
        rw [separatedNetCoverConstant]
        norm_num
  exact_mod_cast hmain

/-- **Existence of a finite maximal separated set** (blueprint
`lem:maximalSeparatedSetExists`).

A bounded set `S` has a finite maximal `r`-separated subset. Maximality is stated in the form
actually used downstream — every point of `S` is at distance `< r` from a point of the net —
which for `r > 0` is equivalent to the impossibility of adding a point of `S`.

In Lean the net is produced by `Metric.maximalSeparatedSet`, whose side condition
`Metric.packingNumber r S ≠ ⊤` follows for bounded `S` from the repository's
`Bornology.IsBounded.coveringNumber_ne_top`; two conventions have to be reconciled, since
`Metric.IsSeparated` uses the strict inequality and `Metric.IsCover` closed balls. -/
theorem exists_maximal_separated {S : Set E} (hS : Bornology.IsBounded S) {r : ℝ} (hr : 0 < r) :
    ∃ N : Finset E, ↑N ⊆ S ∧ (∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) ∧
      ∀ x ∈ S, ∃ y ∈ N, dist x y < r := by
  classical
  -- `S` is bounded, so it lies in a ball, and every `r`-separated finite subset of it
  -- has cardinality bounded by a constant `B`.
  obtain ⟨R, hSR⟩ := hS.subset_ball (0 : E)
  let R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right R 0
  have hSR' : S ⊆ ball (0 : E) R' := hSR.trans (Metric.ball_subset_ball (le_max_left R 0))
  let B : ℝ := (1 + 2 * R' / r) ^ Module.finrank ℝ E
  have hcard (N : Finset E) (hN : (↑N : Set E) ⊆ S)
      (hSep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) : (N.card : ℝ) ≤ B := by
    have hNball : (↑N : Set E) ⊆ ball (0 : E) R' := hN.trans hSR'
    have hfr := finite_and_card_le_of_separated hr hR' (0 : E) (N := (↑N : Set E)) hSep hNball
    rw [Set.ncard_coe_finset] at hfr
    exact hfr.2
  -- Cardinalities of `r`-separated subsets of `S` form a nonempty bounded-above set.
  let Good : Set ℕ := {k | ∃ N : Finset E, (↑N : Set E) ⊆ S ∧
    (∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) ∧ N.card = k}
  have hGood_nonempty : Good.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, by simp, by simp, rfl⟩
  have hGood_bdd : BddAbove Good := by
    refine ⟨Nat.ceil B, ?_⟩
    intro k hk
    rcases hk with ⟨N, hN, hSep, hk'⟩
    have hk_le : (k : ℝ) ≤ B := by rw [← hk']; exact hcard N hN hSep
    exact_mod_cast (le_trans hk_le (Nat.le_ceil B))
  -- A maximal-cardinality `r`-separated subset.
  obtain ⟨m, hm⟩ := BddAbove.exists_isGreatest_of_nonempty hGood_bdd hGood_nonempty
  rcases hm with ⟨hm_mem, hm_max⟩
  rcases hm_mem with ⟨N, hNsub, hNsep, hNcard⟩
  refine ⟨N, hNsub, hNsep, ?_⟩
  -- Maximality gives the covering property: every `x ∈ S` is within `< r` of the net.
  intro x hx
  by_contra hcover
  push Not at hcover
  have hxnotN : x ∉ N := by
    intro hxN
    have hxdist : dist x x = 0 := dist_self x
    linarith [hcover x hxN]
  let N' : Finset E := insert x N
  have hN'_good : N'.card ∈ Good := by
    refine ⟨N', ?_, ?_, rfl⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyN
      · exact hx
      · exact hNsub hyN
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with rfl | hyN
      · rcases Finset.mem_insert.mp hz with rfl | hzN
        · exact False.elim (hyz rfl)
        · exact (hcover z hzN)
      · rcases Finset.mem_insert.mp hz with rfl | hzN
        · simpa [dist_comm] using (hcover y hyN)
        · exact hNsep y hyN z hzN hyz
  have hm_le : N'.card ≤ m := hm_max hN'_good
  have hm_lt : m < N'.card := by
    rw [← hNcard, Finset.card_insert_of_notMem hxnotN]
    omega
  exact (not_le_of_gt hm_lt) hm_le

/-- **A maximal separated set covers at radius `r`** (blueprint `lem:separatedNetCoverR`).

The balls `B(y, r)`, `y ∈ N`, are a `separatedNetCoverConstant n`-boundedly overlapping cover
of `S`: the covering is maximality, and the overlap bound is `card_filter_ball_le` with
`t = r`. -/
theorem isBoundedlyOverlappingCover_ball {S : Set E} {r : ℝ} (hr : 0 < r) (N : Finset E)
    (_hNS : ↑N ⊆ S) (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    (hmax : ∀ x ∈ S, ∃ y ∈ N, dist x y < r) :
    IsBoundedlyOverlappingCover N id (fun _ => r)
      (separatedNetCoverConstant (Module.finrank ℝ E)) S := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hmax x hx with ⟨y, hy, hxy⟩
    exact Set.mem_iUnion₂.mpr ⟨y, hy, by simpa using hxy⟩
  · intro x
    exact card_filter_ball_le hr (by linarith) hsep x

/-- **A maximal separated set covers the `r`-neighbourhood at radius `2r`** (blueprint
`lem:separatedNetCoverTwoR`).

If `x` is within `< r` of a point `x' ∈ S` and `x'` is within `< r` of `y ∈ N`, then `x` is
within `< 2r` of `y`; the overlap bound is `card_filter_ball_le` with `t = 2r`.

The neighbourhood is the *open* one, `Metric.thickening`: for the closed neighbourhood the
statement is false at radius `2r`, as the example `S = (1, 2]`, `r = 1`, `N = {2}`, `x = 0`
shows. Statements phrased with `Metric.cthickening` must therefore either enlarge the radius
or first pass to a strictly larger open neighbourhood. -/
theorem isBoundedlyOverlappingCover_ball_two_mul {S : Set E} {r : ℝ} (hr : 0 < r) (N : Finset E)
    (_hNS : ↑N ⊆ S) (hsep : ∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z)
    (hmax : ∀ x ∈ S, ∃ y ∈ N, dist x y < r) :
    IsBoundedlyOverlappingCover N id (fun _ => 2 * r)
      (separatedNetCoverConstant (Module.finrank ℝ E)) (thickening r S) := by
  constructor
  · rintro x hx
    rcases Metric.mem_thickening_iff.mp hx with ⟨x', hx'S, hxx'⟩
    rcases hmax x' hx'S with ⟨y, hyN, hx'y⟩
    have hxy : x ∈ ball y (2 * r) := by
      rw [Metric.mem_ball]
      calc
        dist x y ≤ dist x x' + dist x' y := dist_triangle x x' y
        _ < r + r := add_lt_add hxx' hx'y
        _ = 2 * r := by ring
    exact Set.mem_biUnion hyN hxy
  · intro x
    exact card_filter_ball_le hr (le_refl (2 * r)) hsep x

/-- **Covers produced by a maximal separated set** (blueprint `lem:separatedNetCover`).

The statement cited downstream: a bounded set `S` has a finite maximal `r`-separated subset
`N`, and for any such `N`, writing `C = separatedNetCoverConstant n`,

* the balls `B(y, r)`, `y ∈ N`, are a `C`-boundedly overlapping cover of `S`;
* the balls `B(y, 2r)`, `y ∈ N`, are a `C`-boundedly overlapping cover of the open
  neighbourhood `N_r(S)`;
* the balls `B(y, r/2)`, `y ∈ N`, are pairwise disjoint;
* if `S ⊆ B(x₀, R)` with `0 ≤ R` then `|N| ≤ (1 + 2R/r) ^ n`.

It merely assembles the five preceding lemmas. -/
theorem exists_separatedNetCover {S : Set E} (hS : Bornology.IsBounded S) {r : ℝ} (hr : 0 < r) :
    ∃ N : Finset E, ↑N ⊆ S ∧ (∀ y ∈ N, ∀ z ∈ N, y ≠ z → r ≤ dist y z) ∧
      (∀ x ∈ S, ∃ y ∈ N, dist x y < r) ∧
      IsBoundedlyOverlappingCover N id (fun _ => r)
        (separatedNetCoverConstant (Module.finrank ℝ E)) S ∧
      IsBoundedlyOverlappingCover N id (fun _ => 2 * r)
        (separatedNetCoverConstant (Module.finrank ℝ E)) (thickening r S) ∧
      (↑N : Set E).PairwiseDisjoint (fun y => ball y (r / 2)) ∧
      ∀ (x₀ : E) (R : ℝ), 0 ≤ R → S ⊆ ball x₀ R →
        (N.card : ℝ) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E := by
  rcases exists_maximal_separated hS hr with ⟨N, hNS, hsep, hmax⟩
  refine ⟨N, hNS, hsep, hmax, ?_, ?_, ?_, ?_⟩
  · exact isBoundedlyOverlappingCover_ball hr N hNS hsep hmax
  · exact isBoundedlyOverlappingCover_ball_two_mul hr N hNS hsep hmax
  · exact pairwiseDisjoint_ball_half hsep
  · intro x₀ R hR hSR
    have hN₀ : (↑N : Set E) ⊆ ball x₀ R := hNS.trans hSR
    have hcard : ((↑N : Set E).ncard : ℝ) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E :=
      (finite_and_card_le_of_separated hr hR x₀ (N := (↑N : Set E)) (by simpa using hsep) hN₀).2
    simpa [Set.ncard_coe_finset] using hcard

/-- **Constant in Lemma `lem:massSubball`** (blueprint `def:massSubballConstant`).

For an ambient dimension `n` and a ratio bound `K ≥ 1` between the diameter scale of the set
and the radius of the subball, this is `(1 + 2K)⁻¹ ^ n ∈ (0, 1]`, the reciprocal of the
cardinality bound of blueprint `lem:separatedNetCard`. -/
noncomputable def massSubballConstant (n : ℕ) (K : NNReal) : NNReal := ((1 + 2 * K) ^ n)⁻¹

/-- **A subball carrying a proportional share of the mass** (blueprint `lem:massSubball`).

A measurable set `S` contained in a ball of radius `R ≤ Kρ` has a point `y ∈ S` with
`|S ∩ B(y, ρ)| ≥ massSubballConstant n K · |S|`: the balls at a maximal `ρ`-separated subset
`M ⊆ S` cover `S` and `|M| ≤ (1 + 2K) ^ n`, so one of the at most `(1 + 2K) ^ n` terms of
`∑_{y ∈ M} |S ∩ B(y, ρ)| ≥ |S|` is large.

The point `y` is a point of `S` itself, which is what the transverse case uses. No
measurability of `S` is needed: the covering step is subadditivity of the outer measure. -/
theorem exists_mem_volume_inter_ball_ge {S : Set E} (hS' : S.Nonempty)
    {ρ R : ℝ} (hρ : 0 < ρ) {K : NNReal} (hK : 1 ≤ K) (x₁ : E) (hSsub : S ⊆ ball x₁ R)
    (hR : R ≤ K * ρ) :
    ∃ y ∈ S, (massSubballConstant (Module.finrank ℝ E) K : ENNReal) * volume S ≤
      volume (S ∩ ball y ρ) := by
  classical
  have hBdd : Bornology.IsBounded S := Metric.isBounded_ball.subset hSsub
  rcases exists_separatedNetCover hBdd hρ with ⟨N, hNsub, hsep, hmax, hcov, hcov₂, hdisj, hcard⟩
  have hNne : N.Nonempty := by
    rcases hS' with ⟨x, hx⟩
    rcases hmax x hx with ⟨y, hyN, _⟩
    exact ⟨y, Finset.mem_coe.mp hyN⟩
  have hS_cov : S ⊆ ⋃ c ∈ N, S ∩ ball c ρ := by
    intro x hx
    rcases hmax x hx with ⟨y, hyN, hxy⟩
    refine Set.mem_iUnion₂.mpr ⟨y, Finset.mem_coe.mp hyN, ?_⟩
    exact ⟨hx, Metric.mem_ball.mpr (by simpa [dist_comm] using hxy)⟩
  obtain ⟨c, hcN, hpig⟩ :=
    exists_card_inv_mul_setLIntegral_le (μ := volume) hNne (fun c => S ∩ ball c ρ)
      (fun _ => (1 : ENNReal)) hS_cov
  have hvol : (N.card : ENNReal)⁻¹ * volume S ≤ volume (S ∩ ball c ρ) := by
    calc
      (N.card : ENNReal)⁻¹ * volume S =
          (N.card : ENNReal)⁻¹ * ∫⁻ x in S, (1 : ENNReal) ∂volume := by
        rw [setLIntegral_const, one_mul]
      _ ≤ ∫⁻ x in S ∩ ball c ρ, (1 : ENNReal) ∂volume := hpig
      _ = volume (S ∩ ball c ρ) := by
        rw [setLIntegral_const, one_mul]
  have hRpos : 0 < R := by
    rcases hS' with ⟨y, hy⟩
    exact lt_of_le_of_lt (dist_nonneg (x := x₁) (y := y))
      (by simpa [dist_comm] using Metric.mem_ball.mp (hSsub hy))
  have hcardR : (N.card : ℝ) ≤ (1 + 2 * R / ρ) ^ Module.finrank ℝ E :=
    hcard x₁ R (le_of_lt hRpos) hSsub
  have hRρ : R / ρ ≤ (K : ℝ) := (div_le_iff₀ hρ).mpr hR
  have hPQ : (1 + 2 * R / ρ : ℝ) ≤ (1 + 2 * (K : ℝ)) := by
    have hRρ2 : 2 * (R / ρ) ≤ 2 * (K : ℝ) :=
      mul_le_mul_of_nonneg_left hRρ (by norm_num : (0 : ℝ) ≤ 2)
    ring_nf at hRρ2 ⊢
    linarith
  have hRρ0 : 0 ≤ R / ρ := le_of_lt (div_pos hRpos hρ)
  have hP_nonneg : 0 ≤ (1 + 2 * R / ρ : ℝ) := by
    have h2R : 0 ≤ 2 * (R / ρ) := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRρ0
    ring_nf at h2R ⊢
    linarith
  have hpow : (1 + 2 * R / ρ : ℝ) ^ Module.finrank ℝ E ≤
      (1 + 2 * (K : ℝ)) ^ Module.finrank ℝ E :=
    pow_le_pow_left₀ hP_nonneg hPQ _
  have hcardK : (N.card : ℝ) ≤ (1 + 2 * (K : ℝ)) ^ Module.finrank ℝ E :=
    le_trans hcardR hpow
  have hcardNN : (N.card : NNReal) ≤ (1 + 2 * K : NNReal) ^ Module.finrank ℝ E := by
    exact_mod_cast hcardK
  have hcardE : (N.card : ENNReal) ≤
      (((1 + 2 * K : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal) := by
    simpa using (ENNReal.coe_le_coe.mpr hcardNN)
  have hinv : (((1 + 2 * K : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal)⁻¹ ≤
      (N.card : ENNReal)⁻¹ :=
    ENNReal.inv_le_inv.mpr hcardE
  have hmain : (((1 + 2 * K : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal)⁻¹ * volume S ≤
      (N.card : ENNReal)⁻¹ * volume S :=
    mul_le_mul_of_nonneg_right hinv (by positivity : (0 : ENNReal) ≤ volume S)
  have hQ : (1 : NNReal) ≤ 1 + 2 * K := by
    exact le_add_of_nonneg_right (by positivity : (0 : NNReal) ≤ 2 * K)
  have hQn1 : (1 : NNReal) ≤ (1 + 2 * K) ^ Module.finrank ℝ E := by
    simpa using (pow_le_pow_left₀ (a := (1 : NNReal)) (b := (1 + 2 * K : NNReal))
      (by norm_num) hQ _)
  have hQn0 : (1 + 2 * K : NNReal) ^ Module.finrank ℝ E ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hQn1)
  have hconst : (massSubballConstant (Module.finrank ℝ E) K : ENNReal) =
      (((1 + 2 * K : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal)⁻¹ := by
    simp [massSubballConstant, hQn0]
  refine ⟨c, ?_, ?_⟩
  · exact hNsub (Finset.mem_coe.mp hcN)
  · calc
      (massSubballConstant (Module.finrank ℝ E) K : ENNReal) * volume S
          = (((1 + 2 * K : NNReal) ^ Module.finrank ℝ E : NNReal) : ENNReal)⁻¹ * volume S := by
        rw [hconst]
      _ ≤ (N.card : ENNReal)⁻¹ * volume S := hmain
      _ ≤ volume (S ∩ ball c ρ) := hvol

end Separated

end Kakeya
