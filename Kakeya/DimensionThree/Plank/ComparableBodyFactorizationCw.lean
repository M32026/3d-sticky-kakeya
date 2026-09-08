/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankPartBBridge
public import Kakeya.DimensionThree.Plank.LocalFactorizationGeometry

/-!
# Propagating the `Cw` repair to the two comparable-body factorisation data

`Kakeya.GlobalPlankFactorization` (`Kakeya/DimensionThree/Plank/Factorization.lean`) carries the
repaired transverse lower bound

`wide : ContainsFlatDisc (min b (1 / 2) / Cw) (part.convexHull_biUnion R).carrier`,

with an explicit comparability constant `Cw ≥ 1`.  The reason for the constant is recorded there:
the *unconstanted* radius `min b (1 / 2)` is jointly unsatisfiable with `le_plank` for the producer
GWZ actually has, because a covering / John-ellipsoid comparison returns
`W ⊆ plank (C a, C b, 1)` and `W ⊇ disc (c b)` with `c < 1 < C`, and no single declared middle
half-width satisfies both.

Two sibling data in this development still carry the **unconstanted** radius, and therefore still
carry that defect:

* `Kakeya.ComparableBodyFactorization.wide` (`.../ComparableBodyFactorization.lean`), the part-(A)
  datum;
* `Kakeya.GlobalComparableBodyFactorization.wide` (`.../GlobalPlankFactorization.lean`), the
  part-(B) sibling.

This file propagates the repair to both, **without editing either**.  Editing them in place is not
a cosmetic change: `ComparableBodyFactorization.wide` is consumed by the *proved* part-(A) chain
through `Kakeya.b_le_two_mul_of_comparableBodyFactorization`, and dividing the radius by `Cw`
multiplies the derived scale relation by `Cw` — a quantitative change inside part (A), which is a
different target and is separately known to be vacuous
(`Kakeya.localPlankFactorisation_proves_anything`).  So the propagation is done here additively:

1. `Kakeya.ComparableBodyFactorizationCw` and `Kakeya.GlobalComparableBodyFactorizationCw` are the
   `Cw`-parameterised data;
2. `Kakeya.ComparableBodyFactorization.toCw` and
   `Kakeya.GlobalComparableBodyFactorization.toCw` show the existing data are exactly the
   `Cw = 1` case, so the parameterised versions are **weaker** hypotheses and any theorem stated
   over them is stronger;
3. `Kakeya.b_le_two_mul_mul_of_comparableBodyFactorizationCw` is the **priced** scale consequence:
   `b ≤ 2 * Cw * ρ` in place of `b ≤ 2 * ρ`.  This is the exact cost of the propagation, and it is
   sub-polynomial under the `Cw ≤ δ ^ (-η)` budget the 6.6 statements already spend;
4. `Kakeya.GlobalPlankFactorization.toGlobalComparableBodyFactorizationCw` is the map that did
   **not** exist before: a repaired 6.6(B) datum with `Cw > 1` could not be fed to
   `Kakeya.GlobalComparableBodyFactorization` at all, because that structure's `wide` is tight.
   With the parameterised target the map exists, and it is proved here.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-! ### The `Cw`-parameterised part-(A) datum -/

/-- **`Kakeya.ComparableBodyFactorization` with the transverse lower bound divided by an explicit
comparability constant `Cw ≥ 1`.**

Every field but `wide` is verbatim that of `Kakeya.ComparableBodyFactorization`; `wide` asks only
for a flat disc of radius `min b (1 / 2) / Cw`.  At `Cw = 1` the two agree
(`Kakeya.ComparableBodyFactorization.toCw`). -/
structure ComparableBodyFactorizationCw (Cw b : ℝ≥0) {ι : Type*} (s : Finset ι)
    (Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) where
  /-- The transverse comparability constant is at least one. -/
  one_le_Cw : 1 ≤ Cw
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each fine body. -/
  cellOf : ι → Cell
  /-- Every fine index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ s, cellOf i ∈ cells
  /-- Every fine body lies in the body of its cell. -/
  le_body : ∀ i ∈ s, Tb i ≤ body (cellOf i)
  /-- Minimality of the outer body. -/
  body_le : ∀ x ∈ cells, ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ i ∈ s, cellOf i = x → Tb i ≤ K) → body x ≤ K
  /-- Transverse lower bound, up to the comparability constant. -/
  wide : ∀ x ∈ cells, ContainsFlatDisc (min b (1 / 2) / Cw) (body x).carrier
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : IsKatzTao cells body (C₀ : ENNReal)

/-- **The unconstanted part-(A) datum is the `Cw = 1` case, hence a special case of the
parameterised one for every `Cw ≥ 1`.**  So `Kakeya.ComparableBodyFactorizationCw` is a genuine
*weakening*, and any theorem quantifying over it is stronger. -/
def ComparableBodyFactorization.toCw {Cw b : ℝ≥0} {ι : Type*} {s : Finset ι}
    {Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C₀ : ℝ≥0}
    (F : ComparableBodyFactorization b s Tb C₀) (hCw : 1 ≤ Cw) :
    ComparableBodyFactorizationCw Cw b s Tb C₀ where
  one_le_Cw := hCw
  Cell := F.Cell
  cells := F.cells
  body := F.body
  cellOf := F.cellOf
  cellOf_mem := F.cellOf_mem
  le_body := F.le_body
  body_le := F.body_le
  wide := fun x hx => (F.wide x hx).mono (div_le_self (zero_le) hCw)
  isKatzTao := F.isKatzTao

/-- One outer body of a `Kakeya.ComparableBodyFactorizationCw` of a nonempty fibre lies inside the
coarse tube containing that fibre. -/
theorem ComparableBodyFactorizationCw.exists_body_le {ι : Type*} {Cw b ρ C₀ : ℝ≥0} {s : Finset ι}
    {Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} (hs : s.Nonempty)
    (F : ComparableBodyFactorizationCw Cw b s Tb C₀) (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hTb : ∀ i ∈ s, Tb i ≤ R.toConvexSpaceBody) :
    ∃ x ∈ F.cells, F.body x ≤ R.toConvexSpaceBody := by
  obtain ⟨i₀, hi₀⟩ := hs
  refine ⟨F.cellOf i₀, F.cellOf_mem i₀ hi₀, ?_⟩
  exact F.body_le (F.cellOf i₀) (F.cellOf_mem i₀ hi₀) R.toConvexSpaceBody
    (fun i hi _ => hTb i hi)

open Classical in
/-- **The priced scale relation: `b ≤ 2 * Cw * ρ`.**

This is the exact cost of propagating the `Cw` repair into the part-(A) datum.  At `Cw = 1` it is
`Kakeya.b_le_two_mul_of_comparableBodyFactorization` verbatim; for `Cw ≤ δ ^ (-η)` the loss is
sub-polynomial, i.e. absorbed by the same budget that the 6.6 statements already spend on `Cpar`
and `C₀`.

It is also the reason the repair is **not** applied in place to
`Kakeya.ComparableBodyFactorization`: the proved part-(A) chain consumes the sharp `b ≤ 2 * ρ`,
and moving the constant is a quantitative change inside a different (and separately vacuous)
target. -/
theorem b_le_two_mul_mul_of_comparableBodyFactorizationCw {ι κ : Type*}
    {δ ρ b Cw : ℝ≥0} (hb1 : b ≤ 1)
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hq : q.Nonempty)
    {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, ComparableBodyFactorizationCw Cw b
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    b ≤ 2 * (Cw * ρ) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hq
  set k := assign i₀ with hk_def
  have hk : k ∈ r := (hassign i₀ hi₀).1
  have hfib : ({i ∈ q | assign i = k} : Finset ι).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩
  have hTb : ∀ i ∈ ({i ∈ q | assign i = k} : Finset ι),
      (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody := by
    intro i hi
    obtain ⟨hiq, hik⟩ := Finset.mem_filter.mp hi
    exact hik ▸ (hassign i hiq).2
  obtain ⟨x, hx, hbodyle⟩ :=
    ComparableBodyFactorizationCw.exists_body_le hfib (Fz k hk) (R k) hTb
  have hCw1 : 1 ≤ Cw := (Fz k hk).one_le_Cw
  have hCw0 : (0 : ℝ≥0) < Cw := lt_of_lt_of_le zero_lt_one hCw1
  have hsub : ((Fz k hk).body x).carrier ⊆
      ((R k).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    (SetLike.coe_subset_coe (S := (Fz k hk).body x)
      (T := (R k).toConvexSpaceBody)).mp hbodyle
  have hdiv : min b (1 / 2 : ℝ≥0) / Cw ≤ ρ :=
    ContainsFlatDisc.le_of_subset_tube ((Fz k hk).wide x hx) (R k) hsub
  have hmin : min b (1 / 2 : ℝ≥0) ≤ Cw * ρ := by
    rw [div_le_iff₀ hCw0] at hdiv
    calc min b (1 / 2 : ℝ≥0) = min b (1 / 2 : ℝ≥0) := rfl
      _ ≤ ρ * Cw := hdiv
      _ = Cw * ρ := by ring
  exact le_two_mul_of_min_le hb1 hmin

/-! ### The `Cw`-parameterised part-(B) comparable-body datum -/

/-- **`Kakeya.GlobalComparableBodyFactorization` with the transverse lower bound divided by an
explicit comparability constant `Cw ≥ 1`.** -/
structure GlobalComparableBodyFactorizationCw (Cw a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (s : Finset ι)
    (Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (C₀ : ℝ≥0) where
  /-- The transverse comparability constant is at least one. -/
  one_le_Cw : 1 ≤ Cw
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each coarse body. -/
  cellOf : ι → Cell
  /-- Every coarse index is collected by a cell in use. -/
  cellOf_mem : ∀ i ∈ s, cellOf i ∈ cells
  /-- Every coarse body lies in the body of its cell. -/
  le_body : ∀ i ∈ s, Tb i ≤ body (cellOf i)
  /-- Minimality of the outer body. -/
  body_le : ∀ x ∈ cells, ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
    (∀ i ∈ s, cellOf i = x → Tb i ≤ K) → body x ≤ K
  /-- Transverse upper bound: each outer body fits in an `a × b × 1` plank. -/
  le_plank : ∀ x ∈ cells, ∃ Q : Plank a b hab hb1, body x ≤ Q.toConvexSpaceBody
  /-- Transverse lower bound, up to the comparability constant. -/
  wide : ∀ x ∈ cells, ContainsFlatDisc (min b (1 / 2) / Cw) (body x).carrier
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : IsKatzTao cells body (C₀ : ENNReal)

/-- **The unconstanted part-(B) comparable-body datum is the `Cw = 1` case.** -/
def GlobalComparableBodyFactorization.toCw {Cw a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {ι : Type*} {s : Finset ι}
    {Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C₀ : ℝ≥0}
    (F : GlobalComparableBodyFactorization a b hab hb1 s Tb C₀) (hCw : 1 ≤ Cw) :
    GlobalComparableBodyFactorizationCw Cw a b hab hb1 s Tb C₀ where
  one_le_Cw := hCw
  Cell := F.Cell
  cells := F.cells
  body := F.body
  cellOf := F.cellOf
  cellOf_mem := F.cellOf_mem
  le_body := F.le_body
  body_le := F.body_le
  le_plank := F.le_plank
  wide := fun x hx => (F.wide x hx).mono (div_le_self (zero_le) hCw)
  isKatzTao := F.isKatzTao

/-- **The scale relation `ρ ≤ a` survives the parameterisation**, because it is a consequence of
`le_plank` and not of `wide`. -/
theorem GlobalComparableBodyFactorizationCw.rho_le {κ : Type*} {Cw a b ρ C₀ : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} {r : Finset κ} (hr : r.Nonempty)
    {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    (Fz : GlobalComparableBodyFactorizationCw Cw a b hab hb1 r
      (fun k => (R k).toConvexSpaceBody) C₀) :
    ρ ≤ a := by
  obtain ⟨k, hk⟩ := hr
  obtain ⟨Q, hQ⟩ := Fz.le_plank (Fz.cellOf k) (Fz.cellOf_mem k hk)
  exact Tube.rho_le_of_le_prism3D (R k) Q (le_trans (Fz.le_body k hk) hQ)

/-! ### The map that did not exist before -/

namespace GlobalPlankFactorization

open Classical in
/-- **A repaired GWZ 6.6(B) datum is a `Cw`-parameterised comparable-body factorisation.**

This map is the point of the propagation.  Against the *unconstanted*
`Kakeya.GlobalComparableBodyFactorization` there is no such map for `Cw > 1`: `wide` there demands
a flat disc of radius `min b (1 / 2)`, and a `Kakeya.GlobalPlankFactorization` with `Cw > 1`
supplies only radius `min b (1 / 2) / Cw`.  With the constant propagated, the datum maps over on
the nose, and the minimality clause `body_le` — which the plank datum does not carry as a field —
is *derived* from the fact that the outer bodies are the convex hulls of the parts. -/
def toGlobalComparableBodyFactorizationCw {κ : Type} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} {r : Finset κ}
    {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    (Fz : GlobalPlankFactorization Cw a b hab hb1 r
      (fun k => (Rt k).toConvexSpaceBody) C₀) :
    GlobalComparableBodyFactorizationCw Cw a b hab hb1 r
      (fun k => (Rt k).toConvexSpaceBody) C₀ where
  one_le_Cw := Fz.one_le_Cw
  Cell := Finset κ
  cells := Fz.parts
  body := fun t => cellBody t Rt
  cellOf := Fz.cellOf
  cellOf_mem := fun k hk => (Fz.cellOf_spec hk).1
  le_body := fun k hk =>
    Finset.le_convexHull_biUnion (fun j => (Rt j).toConvexSpaceBody) (Fz.cellOf_spec hk).2
  body_le := by
    intro x hx K hK
    have hne : x.Nonempty := Fz.nonempty_of_mem_parts hx
    refine (hne.convexHull_biUnion_le_iff (fun j => (Rt j).toConvexSpaceBody) K).2 ?_
    intro i hi
    exact hK i (Fz.le hx hi) (Fz.cellOf_eq (Fz.le hx hi) hx hi)
  le_plank := Fz.le_plank
  wide := Fz.wide
  isKatzTao := Fz.isKatzTao

end GlobalPlankFactorization

end Kakeya

end

end
