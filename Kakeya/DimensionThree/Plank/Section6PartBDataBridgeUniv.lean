/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6PartBDataBridge

/-!
# From `(PS, Fz)` to `Section6PartBData`, at the caller's universe

`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank`
(`Kakeya/DimensionThree/Plank/Section6PartBDataBridge.lean`) converts the pair `(PS, Fz)` that GWZ
Proposition 6.6(B) quantifies over into the `Kakeya.Section6PartBData` the proved Part-(B) chain
consumes — but only for `ι : Type`.  The restriction is inherited from
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`, whose cell type is `Finset κ`,
while the field `Kakeya.Section6PartBFactorisation.Cell` lives in `Type`; and in the pair
`(PS, Fz)` the coarse index type is the *leaf* index type `ι` itself
(`Tube.IsUniformAtScale.parent : Finset ι`).  The project statement
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` quantifies over `{ι : Type*}`, so the
`Type`-only bridge cannot be applied inside its proof.  This was the universe blocker (T3).

This file removes it.  The cells are **enumerated**: `Cell := Fin Fz.parts.card`, along
`Finset.equivFin`, so that the cell type is in `Type` whatever the universe of `ι`, while the coarse
index set stays `PS.parent : Finset ι` and the coarse family stays `PS.parentTube` — nothing on the
coarse side is reindexed, so the decomposition half of the datum
(`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScaleHall`, already universe-polymorphic)
composes with it on the nose.  Every field of
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation` is re-derived for the enumerated
cells from the same lemmas; the only genuinely new step is the reindexing of the Katz--Tao clause,
`ConvexSpaceBody.IsKatzTao.of_injOn_reindex`.

The chain itself (`Kakeya.factoringAndMultPropGlobal_of_remark53` and its descendants down to
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData_univ`) was stated with
`{κ : Type}` for the coarse index type; that restriction had no use in any proof and has been
relaxed to `{κ : Type*}` in the same change, so the datum built here is accepted by the chain.

## What this does not do

The two hypotheses of the `Type`-only bridge that Proposition 6.6(B) does not carry are still
hypotheses here: the branching floor `hNC` and the **parent window** `hballs` (the coarse `ρ`-tubes in the closed unit ball).  The
latter is the T4 blocker of, and it is *not* removable at proof level in this
development: `Tube` has a unit core (`Tube.dist_eq_one`), so no homothety maps `δ`-tubes to tubes
and the "rescale by `(1 + 4ρ)⁻¹`" repair the plan describes has no formal counterpart; and the
framed representative plank (`Kakeya.framedPlank`) fits the working window `plankWindowRadius = 4`
only for bodies inside the *unit* ball (`Kakeya.framedPlank_subset_closedBall`, tight at
`A = B = 1`), while `Kakeya.le_framedPlank` needs the body's long coordinate `≤ 1`, which a body
in `B̄(0, 1 + 4ρ)` violates.  See.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

/-! ### Enumerating the cells -/

/-- The cells of the factorisation, enumerated by `Fin Fz.parts.card`. -/
abbrev cellEquiv : Fin Fz.parts.card ≃ {t // t ∈ Fz.parts} := Fz.parts.equivFin.symm

/-- The enumerated cell collecting a coarse index (any fixed cell off the coarse family). -/
def cellIdx (hne : Fz.parts.Nonempty) (k : κ) : Fin Fz.parts.card :=
  if h : k ∈ r then Fz.parts.equivFin ⟨Fz.cellOf k, (Fz.cellOf_spec h).1⟩
  else Fz.parts.equivFin ⟨hne.choose, hne.choose_spec⟩

theorem cellIdx_of_mem (hne : Fz.parts.Nonempty) {k : κ} (hk : k ∈ r) :
    Fz.cellIdx hne k = Fz.parts.equivFin ⟨Fz.cellOf k, (Fz.cellOf_spec hk).1⟩ := by
  simp [cellIdx, hk]

theorem cellEquiv_cellIdx (hne : Fz.parts.Nonempty) {k : κ} (hk : k ∈ r) :
    (Fz.cellEquiv (Fz.cellIdx hne k)).1 = Fz.cellOf k := by
  rw [cellIdx_of_mem Fz hne hk]
  simp [cellEquiv]

theorem cellIdx_eq_iff (hne : Fz.parts.Nonempty) {k : κ} (hk : k ∈ r) {j : Fin Fz.parts.card} :
    Fz.cellIdx hne k = j ↔ Fz.cellOf k = (Fz.cellEquiv j).1 := by
  rw [cellIdx_of_mem Fz hne hk, Equiv.apply_eq_iff_eq_symm_apply]
  exact Subtype.ext_iff

/-- The coarse fibre of an enumerated cell is the part it enumerates. -/
theorem filter_cellIdx_eq (hne : Fz.parts.Nonempty) (j : Fin Fz.parts.card)
    [inst : DecidablePred (fun k => Fz.cellIdx hne k = j)] :
    Finset.filter (fun k => Fz.cellIdx hne k = j) r = (Fz.cellEquiv j).1 := by
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hk, hkj⟩
    rw [cellIdx_eq_iff Fz hne hk] at hkj
    rw [← hkj]
    exact (Fz.cellOf_spec hk).2
  · intro hkt
    have hk : k ∈ r := Fz.le (Fz.cellEquiv j).2 hkt
    exact ⟨hk, (cellIdx_eq_iff Fz hne hk).mpr (Fz.cellOf_eq hk (Fz.cellEquiv j).2 hkt)⟩

/-! ### The two analytic fields, as standalone lemmas -/

/-- The Katz--Tao clause of `Fz`, reindexed along the enumeration of its cells. -/
theorem isKatzTao_cellEquiv :
    IsKatzTao (Finset.univ : Finset (Fin Fz.parts.card))
      (fun j => cellBody (Fz.cellEquiv j).1 Rt) (C₀ : ENNReal) :=
  IsKatzTao.of_injOn_reindex (s := (Finset.univ : Finset (Fin Fz.parts.card)))
    (e := fun j => (Fz.cellEquiv j).1)
    (U := fun t => t.convexHull_biUnion (fun k => (Rt k).toConvexSpaceBody)) Fz.isKatzTao
    (fun j _ => (Fz.cellEquiv j).2)
    (fun _ _ _ _ hjj' => Fz.cellEquiv.injective (Subtype.ext hjj'))

/-- The coarse-fibre Frostman clause of an enumerated cell, in its framed representative plank —
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`'s field, read on the part
`(Fz.cellEquiv j).1`.  The decidability instance of the fibre is a plain argument so that a
caller's instance is taken by unification. -/
theorem isFrostmanIn_cellIdx_fibre (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b) (hρ : 0 < ρ)
    (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (j : Fin Fz.parts.card) (inst : DecidablePred (fun k => Fz.cellIdx hne k = j)) :
    IsFrostmanIn (@Finset.filter κ (fun k => Fz.cellIdx hne k = j) inst r)
      (fun k => (Rt k).toConvexSpaceBody)
      (framedPlank (cellBody (Fz.cellEquiv j).1 Rt) Fz.uniformThin Fz.uniformMid
        Fz.uniformThin_le_uniformMid (Fz.uniformMid_le_one hballs)).toConvexSpaceBody
      ((partBFrostmanConst Cw C₀ : ℝ≥0) : ENNReal) := by
  classical
  have ht : (Fz.cellEquiv j).1 ∈ Fz.parts := (Fz.cellEquiv j).2
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
  have hFr := Fz.isFrostmanIn_plank_of_isPlankOfDimensions ht hK1 ha'0 hb0
    (hfam _ ht)
    (framedPlank (cellBody (Fz.cellEquiv j).1 Rt) Fz.uniformThin Fz.uniformMid
      Fz.uniformThin_le_uniformMid (Fz.uniformMid_le_one hballs))
    (le_framedPlank _ _ (Fz.thicknessNN_two_le_uniformThin ht)
      (Fz.thicknessNN_one_le_uniformMid ht) (Fz.cellBody_subset_closedBall hballs ht))
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
  · rintro ⟨hk, hkj⟩
    rw [cellIdx_eq_iff Fz hne hk] at hkj
    rw [← hkj]
    exact (Fz.cellOf_spec hk).2
  · intro hkt
    have hk : k ∈ r := Fz.le ht hkt
    exact ⟨hk, (cellIdx_eq_iff Fz hne hk).mpr (Fz.cellOf_eq hk ht hkt)⟩

/-! ### The factorisation half, with enumerated cells -/

open Classical in
/-- **The GWZ 6.6(B) datum yields the tree's Part-(B) factorisation datum with cells in `Type`,
whatever the universe of the coarse index type.**

`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation` with `Cell := Fin Fz.parts.card`
in place of `Finset κ`.  Every field is discharged by the same lemma as there, read on the part
`(Fz.cellEquiv j).1` of the enumerated cell `j`; the Katz--Tao clause is reindexed along the
enumeration (`Kakeya.GlobalPlankFactorization.isKatzTao_cellEquiv`), and the coarse-fibre
Frostman clause is `Kakeya.GlobalPlankFactorization.isFrostmanIn_cellIdx_fibre`. -/
def toSection6PartBFactorisationFin (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b) (hρ : 0 < ρ)
    (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Section6PartBFactorisation Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one hballs) r Rt (partBFrostmanConst Cw C₀) C₀ where
  Cell := Fin Fz.parts.card
  cells := Finset.univ
  body := fun j => cellBody (Fz.cellEquiv j).1 Rt
  cellOf := Fz.cellIdx hne
  cellOf_mem := fun _ _ => Finset.mem_univ _
  le_body := fun k hk => by
    rw [Fz.cellEquiv_cellIdx hne hk]
    exact Finset.le_convexHull_biUnion (fun j => (Rt j).toConvexSpaceBody) (Fz.cellOf_spec hk).2
  repr := fun j => framedPlank (cellBody (Fz.cellEquiv j).1 Rt) Fz.uniformThin Fz.uniformMid
    Fz.uniformThin_le_uniformMid (Fz.uniformMid_le_one hballs)
  body_le_repr := fun j _ =>
    le_framedPlank _ _ (Fz.thicknessNN_two_le_uniformThin (Fz.cellEquiv j).2)
      (Fz.thicknessNN_one_le_uniformMid (Fz.cellEquiv j).2)
      (Fz.cellBody_subset_closedBall hballs (Fz.cellEquiv j).2)
  repr_window := fun j _ =>
    framedPlank_subset_closedBall (Fz.thicknessNN_two_le_uniformThin (Fz.cellEquiv j).2)
      (Fz.thicknessNN_one_le_uniformMid (Fz.cellEquiv j).2)
      (Fz.cellBody_subset_closedBall hballs (Fz.cellEquiv j).2)
  one_le_CF := one_le_partBFrostmanConst Cw C₀
  coarse_fibre_frostman := fun j _ =>
    Fz.isFrostmanIn_cellIdx_fibre hCw hb1' hb0 hρ hne hballs j _
  isKatzTao := Fz.isKatzTao_cellEquiv

/-- Every enumerated cell is a cell in use. -/
theorem mem_cells_toSection6PartBFactorisationFin (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b)
    (hρ : 0 < ρ) (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) (j : Fin Fz.parts.card) :
    j ∈ (Fz.toSection6PartBFactorisationFin hCw hb1' hb0 hρ hne hballs).cells :=
  Finset.mem_univ _

@[simp] theorem toSection6PartBFactorisationFin_body (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b)
    (hρ : 0 < ρ) (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) (j : Fin Fz.parts.card) :
    (Fz.toSection6PartBFactorisationFin hCw hb1' hb0 hρ hne hballs).body j
      = cellBody (Fz.cellEquiv j).1 Rt := rfl

@[simp] theorem toSection6PartBFactorisationFin_cellOf (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b)
    (hρ : 0 < ρ) (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) (k : κ) :
    (Fz.toSection6PartBFactorisationFin hCw hb1' hb0 hρ hne hballs).cellOf k
      = Fz.cellIdx hne k := rfl

/-- The coarse fibre of an enumerated cell is its part. -/
theorem coarseFibre_toSection6PartBFactorisationFin (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hb0 : 0 < b)
    (hρ : 0 < ρ) (hne : Fz.parts.Nonempty)
    (hballs : ∀ k ∈ r, (Rt k).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) (j : Fin Fz.parts.card) :
    (Fz.toSection6PartBFactorisationFin hCw hb1' hb0 hρ hne hballs).coarseFibre j
      = (Fz.cellEquiv j).1 := by
  classical
  ext k
  rw [Section6PartBFactorisation.mem_coarseFibre_iff]
  change k ∈ r ∧ Fz.cellIdx hne k = j ↔ k ∈ (Fz.cellEquiv j).1
  constructor
  · rintro ⟨hk, hkj⟩
    rw [cellIdx_eq_iff Fz hne hk] at hkj
    rw [← hkj]
    exact (Fz.cellOf_spec hk).2
  · intro hkt
    have hk : k ∈ r := Fz.le (Fz.cellEquiv j).2 hkt
    exact ⟨hk, (cellIdx_eq_iff Fz hne hk).mpr (Fz.cellOf_eq hk (Fz.cellEquiv j).2 hkt)⟩

end GlobalPlankFactorization

/-! ### The assembly, at the caller's universe -/

open Classical in
/-- **The Part-(B) datum, built from the pair `(PS, Fz)` that GWZ Proposition 6.6(B) quantifies
over, for a leaf index type in any universe.**

`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank` with its `{ι : Type}` relaxed to
`{ι : Type*}`: the factorisation half is
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisationFin` (cells enumerated by
`Fin Fz.parts.card`), the decomposition half is unchanged.  The hypotheses are exactly those of the
`Type`-only constructor; of them, `hballs` — the parent window — is the one that Proposition 6.6(B)
as stated does not carry (see the module docstring). -/
def Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar : ℝ≥0}
    {Cw a b C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
      (fun k => (PS.parentTube k).toConvexSpaceBody) C₀)
    (hCpar : 1 ≤ Cpar) (hδρ : δ ≤ ρ) (hNC : Cpar ^ 2 ≤ PS.branchingN)
    (hb0 : 0 < b) (hρ : 0 < ρ) (hq : q.Nonempty)
    (hballs : ∀ k ∈ PS.parent,
      (PS.parentTube k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Section6PartBData Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one hballs) q T PS.parent PS.parentTube
      PS.branchingN (2 * Cpar ^ 2)
      (GlobalPlankFactorization.partBFrostmanConst Cw C₀) C₀ where
  decomp := Section6CoarseTubeDecomposition.ofUniformAtScaleHall PS hCpar hδρ
    (branchingN_pos_of_nonempty PS hq) hNC
  factor := Fz.toSection6PartBFactorisationFin Fz.one_le_Cw hb1 hb0 hρ
    (by
      obtain ⟨j, hj⟩ := parent_nonempty_of_nonempty PS hq
      obtain ⟨t, ht, _⟩ := Fz.toFinpartition.exists_mem hj
      exact ⟨t, ht⟩)
    hballs

open Classical in
/-- `Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv` with `1 ≤ Cpar` discharged by
weakening the uniformity datum to `max 1 Cpar` (`Tube.IsUniformAtScale.mono`, which leaves
`parent`, `parentTube` and `branchingN` untouched), exactly as
`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank'` does at `ι : Type`. -/
def Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv'
    {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar : ℝ≥0}
    {Cw a b C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
      (fun k => (PS.parentTube k).toConvexSpaceBody) C₀)
    (hδρ : δ ≤ ρ) (hNC : max 1 Cpar ^ 2 ≤ PS.branchingN)
    (hb0 : 0 < b) (hρ : 0 < ρ) (hq : q.Nonempty)
    (hballs : ∀ k ∈ PS.parent,
      (PS.parentTube k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Section6PartBData Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one hballs) q T PS.parent PS.parentTube
      PS.branchingN (2 * max 1 Cpar ^ 2)
      (GlobalPlankFactorization.partBFrostmanConst Cw C₀) C₀ :=
  Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv
    (PS.mono (le_max_right 1 Cpar) (le_max_right 1 Cpar)) Fz
    (le_max_left 1 Cpar) hδρ hNC hb0 hρ hq hballs

end Kakeya

end

end
