/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.RepresentativeFibres
public import Kakeya.DimensionThree.Plank.ThickenedGeometry
public import Kakeya.Mathlib.Algebra.Order.Field
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap

/-!
# Slab assignment and mass decomposition API

Construction of thickened representatives, fibre-to-slab assignment, translation-aware pose
packing, and the aggregate slab-mass decomposition consumed by Lemma 6.13.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-! ## Slab-mass fibre clustering (`lem:slabMass*` helpers)

The Lean-facing helpers behind `slabMassDecomposition`: a representative choice on each active
thickened prism, the fibre-clustering angle and carrier bounds that place a whole representative
fibre in one containing slab, and the resulting `SlabAssignment` with a trimmed used set. -/


private lemma carrier_subset_Vi'_thickened_dilation (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ Ceq : ℝ≥0, 1 ≤ Ceq ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) {θ : ℝ≥0} {hθ1 : θ ≤ 1}
        (R : ThickenedRepr s V θ hθ1 cThk) (rep : ThickenedPlank θ b hθ1 hb1 → ι)
        (_hrep : ∀ Q ∈ R.indexSet, rep Q ∈ s ∧ R.repr (rep Q) = Q)
        (_hθ0 : 0 < θ) (_hb0 : 0 < b) (i : ι) (_hi : i ∈ s),
        ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((V (rep (R.repr i))).thickened θ hθ1).toPrismNDim.dilation (Ceq * cThk)).carrier := by
  obtain ⟨Ceq, hCeq, hEq⟩ := equalScaleThickening_twoSidedDilation
  refine ⟨Ceq, hCeq, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R rep hrep hθ0 hb0 i hi
  obtain ⟨hi', hQ⟩ := hrep (R.repr i) (R.repr_mem_indexSet hi)
  have hreq := R.repr_eq (rep (R.repr i)) hi'
  have hsub := R.subset_repr i hi
  rw [← hQ, hreq] at hsub
  have hnd : ¬ PrismNDim.IsEssentiallyDistinct (((V (rep (R.repr i))).thickened θ hθ1).toPrismNDim)
      (((V (R.sel (rep (R.repr i)))).thickened θ hθ1).toPrismNDim) := by
    rw [← hreq]; exact R.notEssentiallyDistinct_repr (rep (R.repr i)) hi'
  exact hsub.trans (hEq hθ1 hθ0 hb0 _ _ hnd cThk hcThk).1

-- `Plank.exists_thickenedRepr` now lives in `Kakeya.DimensionThree.Plank.ThickenedRepr`,
-- where it produces the typed `ThickenedPlank`-valued representative map.

/-- sharing a thickened representative `Q = R.repr i` need not share a shaded point, so the
angle bound is derived from the scale-aware two-sided dilation lemma
`equalScaleThickening_twoSidedDilation` applied at `r = cThk`
(`angle_le_of_carrier_subset_thickened_dilation`), not from `IsTypicalPlankAngle`. There
is a uniform `Cang ≥ 1` (depending only on `cThk`) with induced angle `≤ Cang · θ`
between each plank and its representative's containing slab.

`0 < b` and `0 < θ` are required: see `angle_le_of_carrier_subset_thickened_dilation`. -/
theorem fibre_slab_angle_le (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ Cang : ℝ≥0, 1 ≤ Cang ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) {θ : ℝ≥0} {hθ1 : θ ≤ 1}
        (R : ThickenedRepr s V θ hθ1 cThk) (rep : ThickenedPlank θ b hθ1 hb1 → ι)
        (_hrep : ∀ Q ∈ R.indexSet, rep Q ∈ s ∧ R.repr (rep Q) = Q)
        (_hθa : a ≤ θ) (_hθ0 : 0 < θ) (_hb0 : 0 < b),
        ∀ i ∈ s, Prism3D.angle (V i) ((V (rep (R.repr i))).toSlab θ hθ1) ≤ (Cang : ℝ) * (θ : ℝ)
            := by
  obtain ⟨Ceq, hCeq, hCarrier⟩ := carrier_subset_Vi'_thickened_dilation cThk hcThk
  refine ⟨max (3 * Ceq * cThk) 1, le_max_right _ _, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R rep hrep hθa hθ0 hb0 i hi
  -- the containing slab shares the plank's `basis 0`, so the angle is unchanged
  refine (angle_le_of_carrier_subset_thickened_dilation (V i) (V (rep (R.repr i))) θ hθ1
    (Ceq * cThk) hb0 (hCarrier s V R rep hrep hθ0 hb0 i hi)).trans
    (mul_le_mul_of_nonneg_right ?_ θ.coe_nonneg)
  exact_mod_cast (mul_assoc (3 : ℝ≥0) Ceq cThk).ge.trans (le_max_left _ 1)

/-- **Fibre clustering, carrier containment** (`lem:slabMassFibreCarrierContainment`), controlled
form. Each plank carrier lies in a fixed `Cset`-dilation of the shared containing slab of its
representative's fibre. The dilation comes from `equalScaleThickening_twoSidedDilation` at
`r = cThk`: `V i` lies in a `Ceq * cThk`-dilation of `(V i')_θ`, which then sits in a
`Cset`-dilation of the slab.
`Cset` depends only on `cThk`. -/
theorem fibre_carrier_subset_slab (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ Cset : ℝ≥0, 1 ≤ Cset ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) {θ : ℝ≥0} {hθ1 : θ ≤ 1}
        (R : ThickenedRepr s V θ hθ1 cThk) (rep : ThickenedPlank θ b hθ1 hb1 → ι)
        (_hrep : ∀ Q ∈ R.indexSet, rep Q ∈ s ∧ R.repr (rep Q) = Q)
        (_hθa : a ≤ θ) (_hθ0 : 0 < θ) (_hb0 : 0 < b),
        ∀ i ∈ s, ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((V (rep (R.repr i))).toSlab θ hθ1).toPrismNDim.dilation Cset).carrier := by
  obtain ⟨Ceq, hCeq, hCarrier⟩ := carrier_subset_Vi'_thickened_dilation cThk hcThk
  refine ⟨max (Ceq * cThk) 1, le_max_right _ _, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R rep hrep hθa hθ0 hb0 i hi
  exact (hCarrier s V R rep hrep hθ0 hb0 i hi).trans
    (thickened_dilation_subset_toSlab_dilation _ θ hθ1 (le_max_left (Ceq * cThk) 1))

/-- **Fibre clustering: a fibre shares one controlled containing slab**
(`lem:slabMassFibreClustering`), controlled form. Combining the controlled angle and carrier
bounds, every plank of a representative fibre lies in the *controlled* slab family
`inSlabFamilyC Cset Cang` of the one shared containing slab. This is the `hcoh` consumed by
`SlabAssignment.ofFibreRep`. -/
theorem fibre_inSlabFamily_sharedSlab (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ Cset Cang : ℝ≥0, 1 ≤ Cset ∧ 1 ≤ Cang ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) {θ : ℝ≥0} {hθ1 : θ ≤ 1}
        (R : ThickenedRepr s V θ hθ1 cThk) (rep : ThickenedPlank θ b hθ1 hb1 → ι)
        (_hrep : ∀ Q ∈ R.indexSet, rep Q ∈ s ∧ R.repr (rep Q) = Q)
        (_hθa : a ≤ θ) (_hθ0 : 0 < θ) (_hb0 : 0 < b),
        ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V ((V (rep (R.repr i))).toSlab θ hθ1) := by
  obtain ⟨Cang, hCang, hAng⟩ := fibre_slab_angle_le cThk hcThk
  obtain ⟨Cset, hCset, hCar⟩ := fibre_carrier_subset_slab cThk hcThk
  refine ⟨Cset, Cang, hCset, hCang, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R rep hrep hθa hθ0 hb0 i hi
  exact mem_inSlabFamilyC.mpr
    ⟨hi, hCar s V R rep hrep hθa hθ0 hb0 i hi, hAng s V R rep hrep hθa hθ0 hb0 i hi⟩

/-- **Fixed-scale comparability of non-distinct slabs** (`lem:slabFixedScaleComparable`). There is
an absolute constant `Csl ≥ 1`, fixed before the configuration, such that any two `θ × 1 × 1` slabs
that are *not* essentially distinct each lie in the `Csl`-dilation of the other (hence are
`Csl`-comparable). -/
theorem slab_isCComparable_of_not_essentiallyDistinct :
    ∃ Csl : ℝ≥0, 1 ≤ Csl ∧
      ∀ {θ : ℝ≥0} (hθ1 : θ ≤ 1) (S S' : Slab θ hθ1),
        ¬ PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim →
        ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (S'.toPrismNDim.dilation Csl).carrier ∧
          (S'.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (S.toPrismNDim.dilation Csl).carrier) := by
  refine ⟨64, by norm_num, ?_⟩
  intro θ hθ1 S S' hnd
  -- `hnd`, read through the definition, is a strict volume inequality.
  have hnd' : ¬ (volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) ≤
      (1/2 : ENNReal) * max (volume S.carrier) (volume S'.carrier)) := hnd
  have hinter : 0 < volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) :=
    lt_of_le_of_lt _root_.zero_le (not_le.mp hnd')
  -- A positive-volume intersection forces `0 < θ` and provides a shared point.
  have hθ0 : 0 < θ := pos_iff_ne_zero.mpr fun h => by
    have hS := hinter.trans_le (measure_mono Set.inter_subset_left)
    simp [Slab.volume_carrier S, h] at hS
  obtain ⟨p, hpS, hpS'⟩ := nonempty_of_measure_ne_zero hinter.ne'
  have hang := slab_angle_lt_of_not_essentiallyDistinct hθ0 hθ1 S S' hnd
  exact ⟨slab_subset_dilation_of_angle_lt hθ0 hθ1 S S' hang hpS hpS',
    slab_subset_dilation_of_angle_lt hθ0 hθ1 S' S (by rwa [Prism3D.angle_comm]) hpS' hpS⟩

/-- **Scale-aware comparability of non-distinct slabs.** The `∀ r ≥ 1` form of
`slab_isCComparable_of_not_essentiallyDistinct`. This is the form actually consumed by the slab
assignment, which has to push an already-`Cset`-dilated plank carrier from a candidate slab into
its selected partner; a fixed-scale containment cannot be chained through that dilation. -/
theorem slab_dilation_subset_of_not_essentiallyDistinct
    {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (S S' : Slab θ hθ1)
    (hnd : ¬ PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim)
    {r : ℝ≥0} (hr : 1 ≤ r) :
    ((S.toPrismNDim.dilation r).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (S'.toPrismNDim.dilation (64 * r)).carrier := by
  -- `hnd`, read through the definition, is a strict volume inequality, hence a shared point.
  have hnd' : ¬ (volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) ≤
      (1/2 : ENNReal) * max (volume S.carrier) (volume S'.carrier)) := hnd
  have hinter : 0 < volume ((S.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S'.carrier) :=
    lt_of_le_of_lt _root_.zero_le (not_le.mp hnd')
  obtain ⟨p, hpS, hpS'⟩ := nonempty_of_measure_ne_zero hinter.ne'
  exact slab_dilation_subset_of_angle_lt hθ0 hθ1 S S'
    (slab_angle_lt_of_not_essentiallyDistinct hθ0 hθ1 S S' hnd) hpS hpS' hr

/-- Choice for a partially defined existential: if `q x ·` is inhabited whenever `p x` holds, a
single total function realizes all those choices at once. Stated at arbitrary types so that the
choice bookkeeping is not re-elaborated at a large dependent geometric type. -/
private lemma exists_total_choice {α β : Type*} [Nonempty β] (p : α → Prop) (q : α → β → Prop)
    (h : ∀ x, p x → ∃ y, q x y) : ∃ f : α → β, ∀ x, p x → q x (f x) := by
  -- (extracted by Fuse golfer)
  choose! f hf using h
  exact ⟨f, hf⟩

/-- Greedy selection of a maximal `r`-pairwise subfamily of a finite family, for a symmetric
relation `r`: there is `𝒮 ⊆ T` on which `r` holds pairwise and such that every `x ∈ T` admits a
`y ∈ 𝒮` that it is *not* `r`-related to (unless `x = y`). Stated at an arbitrary type so that the
`Finset` bookkeeping does not have to be re-elaborated at a large dependent geometric type. -/
private lemma exists_maximal_pairwise_subset {α : Type*} (T : Finset α) (r : α → α → Prop)
    (hsymm : ∀ x y, r x y → r y x) :
    ∃ 𝒮 : Finset α, 𝒮 ⊆ T ∧ (↑𝒮 : Set α).Pairwise r ∧
      ∀ x ∈ T, ∃ y ∈ 𝒮, x ≠ y → ¬ r x y := by
  -- (extracted by Fuse golfer)
  classical
  obtain ⟨𝒮, h𝒮, hmax⟩ := Finset.exists_max_image
    (T.powerset.filter fun U : Finset α => (↑U : Set α).Pairwise r) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by
      rw [Finset.coe_empty]; exact Set.pairwise_empty r⟩⟩
  obtain ⟨hpow, hpair⟩ := Finset.mem_filter.mp h𝒮
  have hsub : 𝒮 ⊆ T := Finset.mem_powerset.mp hpow
  refine ⟨𝒮, hsub, hpair, fun x hx => ?_⟩
  by_cases hmem : x ∈ 𝒮
  · exact ⟨x, hmem, fun hne => absurd rfl hne⟩
  have hnp : ¬ (↑(insert x 𝒮) : Set α).Pairwise r := fun hp => by
    have := hmax _ (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hsub), hp⟩)
    rw [Finset.card_insert_of_notMem hmem] at this
    omega
  rw [Finset.coe_insert, Set.pairwise_insert] at hnp
  push Not at hnp
  obtain ⟨y, hy, -, hr⟩ := hnp hpair
  exact ⟨y, hy, fun _ h => hr h (hsymm _ _ h)⟩

open Classical in
/-- **A finite maximal essentially-distinct slab family** (`lem:slabMassMaximalSlabFamily`). There
is an absolute `Csl ≥ 1` such that from the candidate slabs `Q ↦ (V (rep Q)).toSlab θ hθ1` one may
select a subfinset `𝒮 ⊆ R.indexSet` whose candidate slabs are pairwise essentially distinct, and
such that every candidate slab is `Csl`-comparable to a selected one. -/
theorem exists_maximal_essentiallyDistinct_slabs :
    ∃ Csl : ℝ≥0, 1 ≤ Csl ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        {θ : ℝ≥0} (hθ1 : θ ≤ 1) {cThk : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk)
        (rep : ThickenedPlank θ b hθ1 hb1 → ι),
        a ≤ θ →
        (∀ Q ∈ R.indexSet, rep Q ∈ s ∧ R.repr (rep Q) = Q) →
        ∃ 𝒮 : Finset (ThickenedPlank θ b hθ1 hb1), 𝒮 ⊆ R.indexSet ∧
          (↑𝒮 : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise (fun Q Q' =>
            PrismNDim.IsEssentiallyDistinct ((V (rep Q)).toSlab θ hθ1).toPrismNDim
              ((V (rep Q')).toSlab θ hθ1).toPrismNDim) ∧
          ∀ Q' ∈ R.indexSet, ∃ Q ∈ 𝒮,
            (PrismNDim.IsCComparable ((V (rep Q')).toSlab θ hθ1).toPrismNDim
              ((V (rep Q)).toSlab θ hθ1).toPrismNDim Csl ∧
             (Q' ≠ Q → ¬ PrismNDim.IsEssentiallyDistinct ((V (rep Q')).toSlab θ hθ1).toPrismNDim
              ((V (rep Q)).toSlab θ hθ1).toPrismNDim)) := by
  obtain ⟨Csl, hCsl_ge1, hCsl⟩ := slab_isCComparable_of_not_essentiallyDistinct
  refine ⟨Csl, hCsl_ge1, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 cThk R rep hθa hrep
  obtain ⟨𝒮, hsub, hpair, hcov⟩ := exists_maximal_pairwise_subset R.indexSet
    (fun Q Q' => PrismNDim.IsEssentiallyDistinct ((V (rep Q)).toSlab θ hθ1).toPrismNDim
      ((V (rep Q')).toSlab θ hθ1).toPrismNDim)
    (fun _ _ h => (PrismNDim.isEssentiallyDistinct_comm _ _).mp h)
  refine ⟨𝒮, hsub, hpair, fun Q' hQ' => ?_⟩
  obtain ⟨Q, hQ, hnd⟩ := hcov Q' hQ'
  by_cases hQQ' : Q' = Q
  · subst hQQ'
    exact ⟨Q', hQ, Or.inl (PrismNDim.self_subset_dilation _ hCsl_ge1), fun hne => absurd rfl hne⟩
  · exact ⟨Q, hQ, Or.inl (hCsl hθ1 _ _ (hnd hQQ')).1, fun _ => hnd hQQ'⟩

/-- Mixed frame entries are controlled by the projective normal distance. If the (sign-blind)
distance between the two short normals is at most `ρ`, then every *mixed* frame inner product
`⟪e j, f k⟫` (exactly one index equal to `0`) is at most `ρ` in absolute value. The sign ambiguity
is harmless: in the `j = 0` case the reference term `⟪f 0, f k⟫` vanishes for `k ≠ 0`, and in the
`k = 0` case the term `⟪e j, e 0⟫` vanishes for `j ≠ 0`, so both `e 0 - f 0` and `e 0 + f 0` give
the same bound. -/
private lemma mixed_frame_le_of_projNormalDist
    (e f : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) {ρ : ℝ}
    (hρ : projNormalDist (e 0) (f 0) ≤ ρ) :
    ∀ j k : Fin 3, (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0) → |inner ℝ (e j) (f k)| ≤ ρ := by
  -- Both signs are handled at once by `σ = ±1`: the reference term drops out either way.
  have key : ∀ σ : ℝ, |σ| = 1 → ∀ j k : Fin 3, (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0) →
      |inner ℝ (e j) (f k)| ≤ ‖e 0 + σ • f 0‖ := by
    rintro σ hσ j k (⟨rfl, hk⟩ | ⟨hj, rfl⟩)
    · have h_orth : inner ℝ (f 0) (f k) = 0 := f.inner_eq_zero (Ne.symm hk)
      calc
        |inner ℝ (e 0) (f k)| = |inner ℝ (e 0 + σ • f 0) (f k)| := by
          rw [inner_add_left, real_inner_smul_left, h_orth, mul_zero, add_zero]
        _ ≤ ‖e 0 + σ • f 0‖ * ‖f k‖ := abs_real_inner_le_norm _ _
        _ = ‖e 0 + σ • f 0‖ := by rw [f.norm_eq_one k, mul_one]
    · have h_orth : inner ℝ (e j) (e 0) = 0 := e.inner_eq_zero hj
      calc
        |inner ℝ (e j) (f 0)| = |inner ℝ (e j) (e 0 + σ • f 0)| := by
          rw [inner_add_right, real_inner_smul_right, h_orth, zero_add, abs_mul, hσ, one_mul]
        _ ≤ ‖e j‖ * ‖e 0 + σ • f 0‖ := abs_real_inner_le_norm _ _
        _ = ‖e 0 + σ • f 0‖ := by rw [e.norm_eq_one j, one_mul]
  intro j k hjk
  rcases min_le_iff.mp hρ with (hd | hs)
  · exact (key (-1) (by norm_num) j k hjk).trans (by rwa [neg_one_smul, ← sub_eq_add_neg])
  · exact (key 1 (by norm_num) j k hjk).trans (by rwa [one_smul])

/-- The `S₀`-normal component of the offset `S.center -ᵥ x` is controlled at the *thin* scale `θ`.
Combining the intrinsic thin bound `|⟪e 0, S.center -ᵥ x⟫| ≤ Cset θ` with the frame comparison
`projNormalDist (e 0) (f 0) ≤ ρ θ` and the crude norm bound `‖S.center -ᵥ x‖ ≤ 2 Cset` gives
`|⟪f 0, S.center -ᵥ x⟫| ≤ (Cset + 2 ρ Cset) θ`. This is the translational half of the pose
confinement: without it the normalized offset coordinate `θ⁻¹ ⟪f 0, S.center -ᵥ x⟫` would be
unbounded as `θ → 0`. -/
private lemma center_normal_component_le
    (e f : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (w : EuclideanSpace ℝ (Fin 3)) {ρ Cs θ : ℝ} (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (_hCs : 0 ≤ Cs)
    (hpn : projNormalDist (e 0) (f 0) ≤ ρ * θ)
    (hthin : |inner ℝ (e 0) w| ≤ Cs * θ)
    (hnorm : ‖w‖ ≤ 2 * Cs) :
    |inner ℝ (f 0) w| ≤ (Cs + 2 * ρ * Cs) * θ := by
  -- Both signs at once: `⟪f 0, w⟫` differs from `⟪e 0, w⟫` by `±⟪e 0 ∓ f 0, w⟫`.
  have hbound : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ ≤ ρ * θ →
      |inner ℝ v w| ≤ ρ * θ * (2 * Cs) := fun v hv =>
    (abs_real_inner_le_norm v w).trans (mul_le_mul hv hnorm (norm_nonneg w) (mul_nonneg hρ hθ))
  obtain ⟨ht1, ht2⟩ := abs_le.mp hthin
  refine abs_le.mpr ?_
  rcases min_le_iff.mp hpn with h | h
  · obtain ⟨h1, h2⟩ := abs_le.mp (hbound _ h)
    rw [inner_sub_left] at h1 h2
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := abs_le.mp (hbound _ h)
    rw [inner_add_left] at h1 h2
    constructor <;> linarith

/-- Metric packing in the 12-dimensional pose space. A finite family whose poses are
coordinatewise bounded by `K` and pairwise `r`-separated has at most `(2 (4K + r) / r) ^ 12`
members. This isolates the whole measure/packing step of the pointwise overlap bound from the
geometry, so the caller only has to supply confinement and separation. -/
theorem card_le_of_pose_confined_separated
    {α : Type*} (F : Finset α)
    (pose : α → EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3))
    {K : ℝ} (hK : 0 ≤ K) {r : ℝ≥0} (hr : 0 < r)
    (hconf : ∀ S ∈ F, ∀ p, |pose S p| ≤ K)
    (hsep : ∀ S ∈ F, ∀ S' ∈ F, S ≠ S' → (r : ℝ) < dist (pose S) (pose S')) :
    (F.card : ℝ) ≤ (2 * (4 * K + (r : ℝ)) / (r : ℝ)) ^ 12 := by
  classical
  have hr0 : (0 : ℝ) < (r : ℝ) := hr
  have hR : (0 : ℝ) ≤ 4 * K := by linarith
  have h12 : Fintype.card ((Fin 3 × Fin 3) ⊕ Fin 3) = 12 := by simp
  have hinj : Set.InjOn pose (F : Set α) := fun S hS S' hS' h => by
    by_contra hne
    have hd := hsep S hS S' hS' hne
    rw [h, dist_self] at hd
    exact absurd hd (not_lt.mpr hr0.le)
  -- `T` lies in the closed ball of radius `4K`: each of the 12 coordinates is at most `K`.
  have hsub : ((F.image pose : Finset (EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3))) :
      Set (EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3))) ⊆ Metric.closedBall 0 (4 * K) := by
    intro y hy
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖pose S‖ ^ 2 ≤ (4 * K) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine (Finset.sum_le_sum fun p _ => sq_le_sq'
        (abs_le.mp (hconf S hS p)).1 (abs_le.mp (hconf S hS p)).2).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        show (Fintype.card ((Fin 3 × Fin 3) ⊕ Fin 3) : ℝ) = 12 from by exact_mod_cast h12]
      calc (12 : ℝ) * K ^ 2 ≤ 16 * K ^ 2 :=
            mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg K)
        _ = (4 * K) ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) hR).mp hsq
  -- `T` is `r`-separated, since `pose` separates distinct members of `F`.
  have hsep' : Metric.IsSeparated (r : ENNReal)
      ((F.image pose : Finset (EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3))) :
        Set (EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3))) := by
    intro x hx y hy hne
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    obtain ⟨S', hS', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    have hd : (r : ℝ) < dist (pose S) (pose S') := hsep S hS S' hS' fun h => hne (by rw [h])
    rwa [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (hr0.trans hd)]
  have h_pack := Metric.card_le_of_isSeparated_subset_closedBall hr (x := 0)
    (hR := hR) (hTsub := hsub) (hTsep := hsep')
  rwa [Finset.card_image_of_injOn hinj,
    show Module.finrank ℝ (EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3)) = 12 from
      (finrank_euclideanSpace).trans h12] at h_pack

/-- The twelve-dimensional **pose** of a slab `S`, read in the reference frame of a slab `S₀` and
based at a point `x`: the nine frame inner products `⟪S.basis j, S₀.basis k⟫` together with the
three offset coordinates `⟪S₀.basis k, S.center -ᵥ x⟫`. The four mixed frame entries and the
normal offset — exactly the coordinates that are `O(θ)` for slabs confined near `S₀` — are
rescaled by `θ⁻¹`, so that all twelve coordinates are bounded by one absolute constant. -/
private noncomputable def refPose {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S₀ : Slab θ hθ1)
    (x : EuclideanSpace ℝ (Fin 3)) (S : Slab θ hθ1) :
    EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3) := -- (extracted by Fuse golfer)
  WithLp.toLp 2 <| Sum.elim
    (fun jk : Fin 3 × Fin 3 =>
      if (jk.1 = 0 ∧ jk.2 ≠ 0) ∨ (jk.1 ≠ 0 ∧ jk.2 = 0) then
        (θ : ℝ)⁻¹ * inner ℝ (S.basis jk.1) (S₀.basis jk.2)
      else inner ℝ (S.basis jk.1) (S₀.basis jk.2))
    (fun k : Fin 3 =>
      if k = 0 then (θ : ℝ)⁻¹ * inner ℝ (S₀.basis 0) (S.center -ᵥ x)
      else inner ℝ (S₀.basis k) (S.center -ᵥ x))

section RefPose

variable {θ : ℝ≥0} {hθ1 : θ ≤ 1}

/-- The mixed frame coordinates of `refPose`, rescaled by `θ⁻¹`. -/
private lemma refPose_inl_mix (S₀ : Slab θ hθ1) (x : EuclideanSpace ℝ (Fin 3)) (S : Slab θ hθ1)
    {j k : Fin 3} (h : (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0)) :
    refPose S₀ x S (Sum.inl (j, k)) = (θ : ℝ)⁻¹ * inner ℝ (S.basis j) (S₀.basis k) :=
  if_pos h -- (extracted by Fuse golfer)

/-- The unscaled frame coordinates of `refPose`. -/
private lemma refPose_inl_diag (S₀ : Slab θ hθ1) (x : EuclideanSpace ℝ (Fin 3)) (S : Slab θ hθ1)
    {j k : Fin 3} (h : ¬((j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0))) :
    refPose S₀ x S (Sum.inl (j, k)) = inner ℝ (S.basis j) (S₀.basis k) :=
  if_neg h -- (extracted by Fuse golfer)

/-- The normal offset coordinate of `refPose`, rescaled by `θ⁻¹`. -/
private lemma refPose_inr_zero (S₀ : Slab θ hθ1) (x : EuclideanSpace ℝ (Fin 3))
    (S : Slab θ hθ1) :
    refPose S₀ x S (Sum.inr 0) = (θ : ℝ)⁻¹ * inner ℝ (S₀.basis 0) (S.center -ᵥ x) :=
  if_pos (c := (0 : Fin 3) = 0) (e := inner ℝ (S₀.basis 0) (S.center -ᵥ x))
    rfl -- (extracted by Fuse golfer)

/-- The tangential offset coordinates of `refPose`. -/
private lemma refPose_inr (S₀ : Slab θ hθ1) (x : EuclideanSpace ℝ (Fin 3)) (S : Slab θ hθ1)
    {k : Fin 3} (hk : k ≠ 0) :
    refPose S₀ x S (Sum.inr k) = inner ℝ (S₀.basis k) (S.center -ᵥ x) :=
  if_neg hk -- (extracted by Fuse golfer)

/-- **Confinement of the pose.** A slab whose normal is within `ρ θ` of `S₀`'s, whose centre is
within `2 Cs` of `x` and which is `Cs θ`-thin through `x` has all twelve pose coordinates bounded
by any `K` dominating `1`, `ρ`, `2 Cs` and `Cs + 2 ρ Cs`. -/
private lemma abs_refPose_le (hθ0 : (0 : ℝ) < (θ : ℝ)) (S₀ S : Slab θ hθ1)
    (x : EuclideanSpace ℝ (Fin 3)) {ρ Cs K : ℝ} (hρ : 0 ≤ ρ) (hCs : 0 ≤ Cs) (h1K : 1 ≤ K)
    (hρK : ρ ≤ K) (h2K : 2 * Cs ≤ K) (hcK : Cs + 2 * ρ * Cs ≤ K)
    (hpn : projNormalDist (S.basis 0) (S₀.basis 0) ≤ ρ * (θ : ℝ))
    (hnorm : ‖S.center -ᵥ x‖ ≤ 2 * Cs)
    (hthin : |inner ℝ (S.basis 0) (x -ᵥ S.center)| ≤ Cs * (θ : ℝ)) :
    ∀ p, |refPose S₀ x S p| ≤ K := by -- (extracted by Fuse golfer)
  have hmixed := mixed_frame_le_of_projNormalDist S.basis S₀.basis hpn
  have hscale : ∀ y : ℝ, y ≤ K → y * (θ : ℝ) ≤ (θ : ℝ) * K := fun y hy => by
    rw [mul_comm (θ : ℝ) K]; exact mul_le_mul_of_nonneg_right hy hθ0.le
  rintro (⟨j, k⟩ | k)
  · by_cases hjk : (j = 0 ∧ k ≠ 0) ∨ (j ≠ 0 ∧ k = 0)
    · rw [refPose_inl_mix S₀ x S hjk, abs_inv_mul_le_iff hθ0]
      exact (hmixed j k hjk).trans (hscale ρ hρK)
    · rw [refPose_inl_diag S₀ x S hjk]
      have h := abs_real_inner_le_norm (S.basis j) (S₀.basis k)
      rw [S.basis.norm_eq_one j, S₀.basis.norm_eq_one k, mul_one] at h
      exact h.trans h1K
  · by_cases hk : k = 0
    · subst hk
      rw [refPose_inr_zero S₀ x S, abs_inv_mul_le_iff hθ0]
      have hthin' : |inner ℝ (S.basis 0) (S.center -ᵥ x)| ≤ Cs * (θ : ℝ) := by
        rwa [← neg_vsub_eq_vsub_rev x S.center, inner_neg_right, abs_neg]
      exact (center_normal_component_le S.basis S₀.basis (S.center -ᵥ x) hθ0.le hρ hCs hpn hthin'
        hnorm).trans (hscale _ hcK)
    · rw [refPose_inr S₀ x S hk]
      have h := abs_real_inner_le_norm (S₀.basis k) (S.center -ᵥ x)
      rw [S₀.basis.norm_eq_one k, one_mul] at h
      exact h.trans (hnorm.trans h2K)

/-- **Separation of the pose.** Two slabs confined near `S₀` whose poses agree to within `δ` in
every coordinate, with `2 δ ≤ 1 / (1024 K)`, fail to be essentially distinct. This is the
contrapositive half of the packing argument: it turns the metric hypothesis of
`card_le_of_pose_confined_separated` into the geometric hypothesis supplied by the caller. -/
private lemma not_essentiallyDistinct_of_refPose_close (hθ0 : 0 < θ) (S₀ S S' : Slab θ hθ1)
    (x : EuclideanSpace ℝ (Fin 3)) {ρ K δ : ℝ} (h1K : 1 ≤ K) (hρK : ρ ≤ K) (hδ : 0 ≤ δ)
    (hδK : 2 * δ ≤ 1 / (1024 * K))
    (hpn : projNormalDist (S.basis 0) (S₀.basis 0) ≤ ρ * (θ : ℝ))
    (hpn' : projNormalDist (S'.basis 0) (S₀.basis 0) ≤ ρ * (θ : ℝ))
    (hclose : ∀ p, |refPose S₀ x S p - refPose S₀ x S' p| ≤ δ) :
    ¬ PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim := by
  -- (extracted by Fuse golfer)
  have hθ0' : (0 : ℝ) < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hθδ : (0 : ℝ) ≤ (θ : ℝ) * δ := mul_nonneg hθ0'.le hδ
  have hρθK : ρ * (θ : ℝ) ≤ K * (θ : ℝ) := mul_le_mul_of_nonneg_right hρK hθ0'.le
  have hvs : (S.center -ᵥ x : EuclideanSpace ℝ (Fin 3)) - (S'.center -ᵥ x)
      = -(S'.center -ᵥ S.center) :=
    (vsub_sub_vsub_cancel_right _ _ _).trans (neg_vsub_eq_vsub_rev _ _).symm
  have hmixed := mixed_frame_le_of_projNormalDist S.basis S₀.basis hpn
  have hmixed' := mixed_frame_le_of_projNormalDist S'.basis S₀.basis hpn'
  refine not_essentiallyDistinct_of_ref_coords_close hθ0 hθ1 S₀ S S' h1K
    (mul_nonneg zero_le_two hδ) (fun j k hjk => (hmixed j k hjk).trans hρθK)
    (fun j k hjk => (hmixed' j k hjk).trans hρθK) ?_ ?_ ?_ ?_ hδK
  · intro j k hjk
    have h := hclose (Sum.inl (j, k))
    rw [refPose_inl_mix S₀ x S hjk, refPose_inl_mix S₀ x S' hjk, ← mul_sub,
      abs_inv_mul_le_iff hθ0'] at h
    linarith only [h, hθδ]
  · intro j k hjk
    have h := hclose (Sum.inl (j, k))
    rw [refPose_inl_diag S₀ x S hjk, refPose_inl_diag S₀ x S' hjk] at h
    linarith only [h, hδ]
  · have h := hclose (Sum.inr 0)
    rw [refPose_inr_zero S₀ x S, refPose_inr_zero S₀ x S', ← mul_sub, ← inner_sub_right, hvs,
      inner_neg_right, abs_inv_mul_le_iff hθ0', abs_neg] at h
    linarith only [h, hθδ]
  · intro k hk
    have h := hclose (Sum.inr k)
    rw [refPose_inr S₀ x S hk, refPose_inr S₀ x S' hk, ← inner_sub_right, hvs, inner_neg_right,
      abs_neg] at h
    linarith only [h, hδ]

end RefPose

/-- **Choice of the packing constants.** From nonnegative scale parameters `ρ` (angular) and `Cs`
(spatial) one gets a confinement radius `K ≥ 1` dominating each of `ρ`, `2 Cs` and `Cs + 2 ρ Cs`,
together with a positive separation radius `r` with `2 r ≤ 1 / (1024 K)`: exactly the numeric
inputs of `abs_refPose_le`, `not_essentiallyDistinct_of_refPose_close` and
`card_le_of_pose_confined_separated`. -/
private lemma exists_refPose_constants {ρ Cs : ℝ} (hρ : 0 ≤ ρ) (hCs : 0 ≤ Cs) :
    ∃ (K : ℝ) (r : ℝ≥0), 1 ≤ K ∧ ρ ≤ K ∧ 2 * Cs ≤ K ∧ Cs + 2 * ρ * Cs ≤ K ∧ 0 < r ∧
      2 * (r : ℝ) ≤ 1 / (1024 * K) := by -- (extracted by Fuse golfer)
  have hρCs : 0 ≤ ρ * Cs := mul_nonneg hρ hCs
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + ρ + 2 * Cs + (Cs + 2 * ρ * Cs) := ⟨_, rfl⟩
  have h1 : (1 : ℝ) ≤ K := by rw [hK]; linarith only [hρ, hCs, hρCs]
  have hpos : (0 : ℝ) < 1024 * K := by linarith only [h1]
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (r : ℝ) = 1 / (1024 * K) / 2 :=
    ⟨⟨_, div_nonneg (div_nonneg zero_le_one hpos.le) zero_le_two⟩, rfl⟩
  exact ⟨K, r, h1, by rw [hK]; linarith only [hCs, hρCs],
    by rw [hK]; linarith only [hρ, hCs, hρCs], by rw [hK]; linarith only [hρ, hCs],
    by rw [← NNReal.coe_pos, hr]; exact div_pos (div_pos one_pos hpos) two_pos,
    by rw [hr]; linarith only []⟩

open Classical in
/-- **Pointwise overlap bound for the `inSlabFamilyC`-indexed family**
(`lem:slabMassPointwiseOverlap`). There is an absolute integer `Nov ≥ 1` such that for any
configuration, at any point `x`, at most `Nov` used slabs have their `inSlabFamilyC`-assigned
shading union containing `x`. -/
theorem slab_pointwise_overlap_le (C Cset Cang : ℝ≥0) (hCang : 1 ≤ Cang) :
    ∃ Nov : ℕ, 1 ≤ Nov ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {θ : ℝ≥0} (hθ1 : θ ≤ 1) (repr : ι → ThickenedPlank θ b hθ1 hb1)
        (SA : SlabAssignment s V θ hθ1 repr Cset Cang),
        0 < θ → Kakeya.HasMaxPlankAngleBound s Y V θ C →
        (∀ i ∈ s, (Y i).shade ⊆ (V i).carrier) →
        (↑SA.used : Set (Slab θ hθ1)).Pairwise
          (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim) →
        ∀ x : EuclideanSpace ℝ (Fin 3),
          (SA.used.filter
            (fun S => x ∈ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)).card ≤ Nov := by
  -- Absolute constants, chosen so that all four confinement bounds are immediate.
  obtain ⟨K, r, h1_le_K, hρ_le_K, h2Cset_le_K, hCset2_le_K, hr_pos, hrK⟩ :=
    exists_refPose_constants (NNReal.coe_nonneg (2 * Cang + 2 * C)) Cset.coe_nonneg
  refine ⟨max ⌈(2 * (4 * K + (r : ℝ)) / (r : ℝ)) ^ 12⌉₊ 1, le_max_right _ _, ?_⟩
  intro a b hab hb1 ι s V Y θ hθ1 repr SA hθ0 htyp hshade_sub hpairwise x
  set F := SA.used.filter
    (fun S => x ∈ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)
  rcases F.eq_empty_or_nonempty with hF_empty | ⟨S₀, hS₀_mem⟩
  · rw [hF_empty, Finset.card_empty]; exact Nat.zero_le _
  -- Every member of `F` shares the shading point `x`, hence is confined near `S₀`.
  have hwit : ∀ S ∈ F, ∃ i ∈ inSlabFamilyC Cset Cang s V S, x ∈ (Y i).shade := fun S hS => by
    obtain ⟨i, hi, hi'⟩ := Set.mem_iUnion₂.mp (Finset.mem_filter.mp hS).2
    exact ⟨i, hi, hi'⟩
  have hconf : ∀ S ∈ F,
      projNormalDist (S.basis 0) (S₀.basis 0) ≤ ((2 * Cang + 2 * C : ℝ≥0) : ℝ) * (θ : ℝ) ∧
        ‖S.center -ᵥ x‖ ≤ 2 * (Cset : ℝ) ∧
        |inner ℝ (S.basis 0) (x -ᵥ S.center)| ≤ (Cset : ℝ) * (θ : ℝ) := fun S hS =>
    inSlabFamilyC_normal_and_center_confined C Cset Cang hCang s V Y hθ1 repr SA x S₀ S
      hθ0 htyp hshade_sub (hwit S₀ hS₀_mem) (hwit S hS)
  have hcard := card_le_of_pose_confined_separated F (refPose S₀ x)
    (zero_le_one.trans h1_le_K) hr_pos
    (fun S hS => abs_refPose_le (NNReal.coe_pos.mpr hθ0) S₀ S x
      (NNReal.coe_nonneg (2 * Cang + 2 * C)) Cset.coe_nonneg h1_le_K hρ_le_K h2Cset_le_K
      hCset2_le_K (hconf S hS).1 (hconf S hS).2.1 (hconf S hS).2.2)
    (fun S hS S' hS' hne => by
      by_contra! hcon
      exact not_essentiallyDistinct_of_refPose_close hθ0 S₀ S S' x h1_le_K hρ_le_K r.coe_nonneg
          hrK (hconf S hS).1 (hconf S' hS').1
          (fun p => by
            have h := PiLp.dist_apply_le (refPose S₀ x S) (refPose S₀ x S') p
            rw [Real.dist_eq] at h
            exact h.trans hcon)
        (hpairwise (Finset.mem_coe.mpr (Finset.mem_filter.mp hS).1)
          (Finset.mem_coe.mpr (Finset.mem_filter.mp hS').1) hne))
  exact le_trans (by exact_mod_cast hcard.trans (Nat.le_ceil _)) (le_max_left _ _)

open Classical in
/-- **Aggregate union-volume comparison (G1)** (`lem:slabMassAggregateG1`). Given a pointwise
multiplicity bound `Nov` on the family `S ↦ ⋃ i ∈ inSlabFamily s V S, (Y i).shade` of used-slab
shading unions, the aggregate inequality (G1) holds with `cOv = 1 / Nov > 0`:
`cOv · ∑_{S ∈ used} |U(𝒫_S, Y)| ≤ |U(s, Y)|`. -/
theorem slabMass_aggregate_union_le (Nov : ℕ) (hNov : 1 ≤ Nov) :
    ∃ cOv : ℝ≥0, 0 < cOv ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {θ : ℝ≥0} (hθ1 : θ ≤ 1) (repr : ι → ThickenedPlank θ b hθ1 hb1) {Cset Cang : ℝ≥0}
        (SA : SlabAssignment s V θ hθ1 repr Cset Cang),
        (∀ x : EuclideanSpace ℝ (Fin 3),
          (SA.used.filter (fun S => x ∈ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)).card
              ≤ Nov) →
        (cOv : ENNReal) *
            (∑ S ∈ SA.used, volume (⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)) ≤
          volume (⋃ i ∈ s, (Y i).shade) := by
  have hNov0 : (Nov : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_inv_mul : (((Nov : ℝ≥0)⁻¹ : ℝ≥0) : ENNReal) * (Nov : ENNReal) = 1 := by
    rw [ENNReal.coe_inv hNov0, ENNReal.coe_natCast]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hNov0) (ENNReal.natCast_ne_top Nov)
  refine ⟨(Nov : ℝ≥0)⁻¹, pos_iff_ne_zero.mpr (inv_ne_zero hNov0), ?_⟩
  intro a b hab hb1 ι s V Y θ hθ1 repr Cset Cang SA hmult
  have hsum := MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le
    (μ := volume) (s := SA.used) (C := Nov)
    (A := fun S => ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)
    (hA := fun S _ => Finset.measurableSet_biUnion _ fun i _ => (Y i).measurableSet_shade)
    (hC := hmult)
  have hsub : (⋃ S ∈ SA.used, ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade) ⊆
      ⋃ i ∈ s, (Y i).shade :=
    Set.iUnion₂_subset fun _ _ => Set.iUnion₂_subset fun i hi _ hx =>
      Set.mem_iUnion₂.mpr ⟨i, Plank.inSlabFamilyC_subset hi, hx⟩
  refine (mul_le_mul_right (hsum.trans (mul_le_mul_right (measure_mono hsub) _)) _).trans ?_
  rw [← mul_assoc, h_inv_mul, one_mul]

/-- A concrete `θ × 1 × 1` slab, used only as the value of `slabOf` outside the active index set
(where the `SlabAssignment` fields assert nothing). It is never a witness for any geometric
claim. -/
noncomputable def defaultSlab (θ : ℝ≥0) (hθ1 : θ ≤ 1) : Slab θ hθ1 :=
  { PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace.basisFun (Fin 3) ℝ) ![θ, 1, 1] with
    thicknesses_eq := rfl }

open Classical in
/-- **Slab assignment with a pairwise essentially-distinct used family.** Combines fibre
clustering with the maximal essentially-distinct selection: each `repr`-fibre is assigned not its
own candidate slab but the *selected* slab it is comparable to, so the used family is pairwise
essentially distinct — exactly the hypothesis of `slab_pointwise_overlap_le`, which cannot be
dropped (an unbounded number of mutually non-distinct slabs could otherwise share a point).

Transferring the fibre coherence across that selection is where the two new comparison lemmas are
needed: the carrier clause uses the *scale-aware*
`slab_dilation_subset_of_not_essentiallyDistinct` (the already-`Cset₀`-dilated carrier must be
pushed into the selected slab, which a fixed-scale containment cannot do), and the angle clause
uses the quasi-triangle inequality `Prism3D.angle_le_two_mul_add_angle`. The cost is the fixed
constants
`Cset = 64 Cset₀` and `Cang = 2 Cang₀ + 16`. -/
theorem exists_pairwiseDistinct_slabAssignment (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ Cset Cang : ℝ≥0, 1 ≤ Cset ∧ 1 ≤ Cang ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) {θ : ℝ≥0} {hθ1 : θ ≤ 1}
        (R : ThickenedRepr s V θ hθ1 cThk),
        a ≤ θ → 0 < θ → 0 < b →
        ∃ SA : SlabAssignment s V θ hθ1 R.repr Cset Cang,
          (↑SA.used : Set (Slab θ hθ1)).Pairwise
            (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim) := by
  obtain ⟨Cset₀, Cang₀, hCset₀, hCang₀, hfib⟩ := fibre_inSlabFamily_sharedSlab cThk hcThk
  obtain ⟨Csl, hCsl1, hMax⟩ := exists_maximal_essentiallyDistinct_slabs
  have hCset : (1 : ℝ≥0) ≤ 64 * Cset₀ :=
    le_trans hCset₀ (le_mul_of_one_le_left zero_le (by norm_num))
  have hCang : (1 : ℝ≥0) ≤ 2 * Cang₀ + 16 := le_trans (by norm_num) le_add_self
  refine ⟨64 * Cset₀, 2 * Cang₀ + 16, hCset, hCang, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R hθa hθ0 hb0
  classical
  by_cases hι : Nonempty ι
  swap
  · -- `ι` is empty, so `s = ∅`: every field is vacuous and the used family is empty.
    haveI hIE : IsEmpty ι := not_nonempty_iff.mp hι
    refine ⟨{ slabOf := fun _ => defaultSlab θ hθ1
              used := ∅
              slabOf_mem := fun i _ => isEmptyElim i
              mem_inSlabFamily := fun i _ => isEmptyElim i }, ?_⟩
    simp
  haveI : Nonempty ι := hι
  haveI : Nonempty (ThickenedPlank θ b hθ1 hb1) := ⟨R.repr (Classical.arbitrary ι)⟩
  -- A representative index for each active thickened prism.
  obtain ⟨rep, hrep⟩ := exists_total_choice (fun Q : ThickenedPlank θ b hθ1 hb1 => Q ∈ R.indexSet)
    (fun Q i => i ∈ s ∧ R.repr i = Q) fun Q hQ => by
      rw [ThickenedRepr.indexSet, Finset.mem_image] at hQ
      obtain ⟨i, hi, hiQ⟩ := hQ
      exact ⟨i, hi, hiQ⟩
  -- A maximal essentially-distinct subfamily of the candidate slabs.
  obtain ⟨𝒮, h𝒮sub, h𝒮pair, h𝒮cov⟩ := hMax s V hθ1 R rep hθa hrep
  -- Select, for each active prism, the maximal-family member it is not distinct from.
  obtain ⟨selQ, hselQ⟩ := exists_total_choice (fun Q : ThickenedPlank θ b hθ1 hb1 => Q ∈ R.indexSet)
    (fun Q Qs => Qs ∈ 𝒮 ∧ (Q ≠ Qs → ¬ PrismNDim.IsEssentiallyDistinct
      ((V (rep Q)).toSlab θ hθ1).toPrismNDim ((V (rep Qs)).toSlab θ hθ1).toPrismNDim))
    fun Q hQ => by
      obtain ⟨Qs, hQs𝒮, -, hQsnd⟩ := h𝒮cov Q hQ
      exact ⟨Qs, hQs𝒮, hQsnd⟩
  -- Fibre coherence transferred across the selection.
  have hcoh : ∀ i ∈ s, i ∈ inSlabFamilyC (64 * Cset₀) (2 * Cang₀ + 16) s V
      ((V (rep (selQ (R.repr i)))).toSlab θ hθ1) := by
    intro i hi
    obtain ⟨-, hselnd⟩ := hselQ (R.repr i) (R.repr_mem_indexSet hi)
    have hfib0 := hfib s V R rep hrep hθa hθ0 hb0 i hi
    rw [mem_inSlabFamilyC] at hfib0
    obtain ⟨-, hcar0, hang0⟩ := hfib0
    have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
    have hCang₀' : (0 : ℝ) ≤ (Cang₀ : ℝ) := Cang₀.coe_nonneg
    rw [mem_inSlabFamilyC]
    refine ⟨hi, ?_, ?_⟩
    · by_cases heq : R.repr i = selQ (R.repr i)
      · rw [← heq]
        exact hcar0.trans (PrismNDim.dilation_carrier_mono _
          (le_mul_of_one_le_left zero_le (by norm_num)))
      · exact hcar0.trans (slab_dilation_subset_of_not_essentiallyDistinct hθ0 hθ1 _ _
          (hselnd heq) hCset₀)
    · by_cases heq : R.repr i = selQ (R.repr i)
      · rw [← heq]
        refine hang0.trans (mul_le_mul_of_nonneg_right ?_ hθ0'.le)
        push_cast
        linarith
      · have hangs := slab_angle_lt_of_not_essentiallyDistinct hθ0 hθ1
          ((V (rep (R.repr i))).toSlab θ hθ1) ((V (rep (selQ (R.repr i)))).toSlab θ hθ1)
          (hselnd heq)
        have htri := Prism3D.angle_le_two_mul_add_angle (V i) ((V (rep (R.repr i))).toSlab θ hθ1)
          ((V (rep (selQ (R.repr i)))).toSlab θ hθ1)
        push_cast
        linarith
  refine ⟨Plank.SlabAssignment.ofFibreRep hθ1 (fun Q => rep (selQ Q)) (64 * Cset₀)
    (2 * Cang₀ + 16) hcoh, ?_⟩
  -- The used family is contained in the maximal essentially-distinct selection.
  intro S hS S' hS' hne
  simp only [SlabAssignment.ofFibreRep, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hS hS'
  obtain ⟨i, hi, rfl⟩ := hS
  obtain ⟨i', hi', rfl⟩ := hS'
  obtain ⟨hmem, -⟩ := hselQ _ (R.repr_mem_indexSet hi)
  obtain ⟨hmem', -⟩ := hselQ _ (R.repr_mem_indexSet hi')
  exact h𝒮pair hmem hmem' fun h => hne (by rw [h])

open Classical in
/-- A typical plank angle yields a slab assignment together with exactly the uniform mass
comparison consumed by Item 3 of `plankReduction`.  Pointwise overlap counts and a second slab-layer
record are intentionally hidden inside this geometric lemma.

The side hypotheses `0 < a` and `hYV` are genuine structural coherence conditions supplied by the
caller (`plankReduction` has both); neither restates any part of the conclusion. `0 < a` is what
makes the plank nondegenerate, hence `0 < b` and `0 < θ`.

The angle input is the *one-sided* `Kakeya.HasMaxPlankAngleBound`, not the two-sided
`Kakeya.IsTypicalPlankAngle`: tracing the chain
(`slab_pointwise_overlap_le` → `inSlabFamilyC_normal_and_center_confined` → `angularClustering`)
shows only the upper bound `maxPlankAngle ≤ C·θ` is ever used, and there is no stability scale `A`
anywhere.  This matters for the caller: the one-sided bound is monotone under refinement
(`HasMaxPlankAngleBound.mono`), so the slab layer may be applied after an arbitrary deletion of
planks with no pointwise fibre-retention hypothesis.

The used slab family is also returned *pairwise essentially distinct*.  This costs nothing: it is
already in scope, since `exists_pairwiseDistinct_slabAssignment` produces the assignment precisely
by selecting into a maximal essentially-distinct family, and `slab_pointwise_overlap_le` consumes
that property to obtain the aggregate bound.  Exposing it is what lets `Kakeya.plankReduction` state
that its slab family `𝒮` is nondegenerate rather than a repetition of one slab.

The slab-family comparability constants `Cset` and `Cang` are returned in the *outer* existential,
alongside the overlap constant `cOv`, because that is where they are produced: they come from
`exists_pairwiseDistinct_slabAssignment cThk hcThk`, which binds them before any configuration.
Returning them inside the per-configuration existential would let a caller believe they are
configuration-dependent weakening knobs, and would prevent `Kakeya.plankReduction` from quantifying
them before its index type. -/
theorem slabMassDecomposition (cThk C : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ cOv Cset Cang : ℝ≥0, 0 < cOv ∧ 1 ≤ Cset ∧ 1 ≤ Cang ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (θ : ℝ≥0) (hθ1 : θ ≤ 1) (R : ThickenedRepr s V θ hθ1 cThk),
        0 < a → a ≤ θ → Kakeya.HasMaxPlankAngleBound s Y V θ C →
        (∀ i ∈ s, (Y i).shade ⊆ (V i).carrier) →
        ∃ SA : SlabAssignment s V θ hθ1 R.repr Cset Cang,
          ((↑SA.used : Set (Slab θ hθ1)).Pairwise
            (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim)) ∧
          (cOv : ENNReal) *
              (∑ S ∈ SA.used, volume (⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)) ≤
            volume (⋃ i ∈ s, (Y i).shade) := by
  obtain ⟨Cset, Cang, hCset, hCang, hSA⟩ := exists_pairwiseDistinct_slabAssignment cThk hcThk
  obtain ⟨Nov, hNov, hOverlap⟩ := slab_pointwise_overlap_le C Cset Cang hCang
  obtain ⟨cOv, hcOv, hAgg⟩ := slabMass_aggregate_union_le Nov hNov
  refine ⟨cOv, Cset, Cang, hcOv, hCset, hCang, ?_⟩
  intro a b hab hb1 ι s V Y θ hθ1 R ha0 hθa htyp hYV
  have hθ0 : 0 < θ := ha0.trans_le hθa
  obtain ⟨SA, hpairwise⟩ := hSA s V R hθa hθ0 (ha0.trans_le hab)
  exact ⟨SA, hpairwise,
    hAgg s V Y hθ1 R.repr SA (hOverlap s V Y hθ1 R.repr SA hθ0 htyp hYV hpairwise)⟩

end Plank

end
