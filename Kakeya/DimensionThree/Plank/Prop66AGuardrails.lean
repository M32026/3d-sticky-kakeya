/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RelativePlank
public import Kakeya.DimensionThree.Plank.LocalFactorizationGeometry

/-!
# Guardrails for GWZ Proposition 6.6(A)

`Kakeya.tubeMultiplicityOfLocalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Factorization.lean`) carries a compiler-checked proof, but its own
docstring warns that the proof is an `exfalso`: for a nonempty `q` its hypotheses are
contradictory, so the statement asserts nothing about multiplicity.

This file pins that claim mechanically, in the pattern of
`Kakeya/DimensionThree/MainLemma2/AScaleGuardrails.lean`:

1. `Kakeya.LocalPlankFactorisationStatement` restates 6.6(A) as a `Prop` with every binder
   explicit;
2. the `example` immediately below it is the **compatibility**: it type-checks only while
   `Kakeya.tubeMultiplicityOfLocalPlankFactorisation` still says exactly that, so any future
   repair of the statement breaks this file rather than silently invalidating the check;
3. `Kakeya.localPlankFactorisation_hypotheses_uninhabited` derives `False` from the
   factorisation block of those hypotheses alone, whenever `0 < δ` and `q` is nonempty;
4. `Kakeya.localPlankFactorisation_proves_anything` is the sharp form: under exactly the
   hypotheses of 6.6(A) with `q` nonempty, *every* proposition follows, so the multiplicity bound
   in the conclusion carries no information.

The defect is `Kakeya.PlankFactorization.parts_are_planks`, which demands the **equality**
`part.convexHull_biUnion V = Q.toConvexSpaceBody`.  Over `δ`-tubes with `δ > 0` the hull of a
nonempty part is a Minkowski sum `K + closedBall 0 δ`, which has no corner, while a plank carrier
does: `Kakeya.not_plankFactorization_of_shadedTube` (`Kakeya/RelativePlank.lean`).

**The faithful 6.6(A)** should be stated over `Kakeya.ComparableBodyFactorization`
(`Kakeya/DimensionThree/Plank/ComparableBodyFactorization.lean`), which omits `parts_are_planks`
and replaces it by containment in a plank together with the transverse lower bound
`Kakeya.ContainsFlatDisc`.  That structure's `wide` field currently carries the *unconstanted*
radius `min b (1 / 2)`, i.e. exactly the tightness defect that the `Cw` parameterisation of
`Kakeya.GlobalPlankFactorization` was introduced to remove, so the faithful 6.6(A) should carry
the same `Cw`.  Its scale regime differs from part (B)'s — there `b ≤ 2ρ` is *derived* and
`ρ ≤ a` is *false* — so repairing it is a separate steps.  Nothing here attempts it.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

open Classical in
/-- **GWZ Proposition 6.6(A) as currently stated**, verbatim, as a `Prop` in `β`.

Kept in sync with `Kakeya.tubeMultiplicityOfLocalPlankFactorisation` by the compatibility `example`
below. -/
def LocalPlankFactorisationStatement (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet q T
          (Tube.ssfGridLen δ) C)) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
        {κ : Type} (r : Finset κ)
        (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ),
        δ ≤ ρ → ρ ≤ a →
        (∀ i ∈ q, assign i ∈ r ∧
          (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
        ∀ (C₀ : ℝ≥0), C₀ ≤ δ ^ (-η) →
          ∀ (_Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
            {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀),
        ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
          IsFrostmanIn q (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall CF →
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
            (δ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2)
              * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
              * (δ : ENNReal) ^ (-2 * β)
              * ((δ : ENNReal) ^ 2 * (q.card : ENNReal)) ^ (1 - β / 2)

/-- **compatibility / fidelity check.**  `Kakeya.LocalPlankFactorisationStatement` is verbatim what
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` proves.  If 6.6(A) is ever restated, this
`example` stops compiling and the vacuity check below must be redone. -/
example {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    LocalPlankFactorisationStatement β :=
  tubeMultiplicityOfLocalPlankFactorisation hβpos hβle hKKT hKF

open Classical in
/-- **The factorisation block of GWZ 6.6(A) is contradictory whenever `0 < δ` and `q` is
nonempty.**

Only three of 6.6(A)'s hypotheses are used: `0 < δ`, the assignment clause `hassign` (which is
where `assign i ∈ r` comes from), and the local factorisations `Fz`.  Everything else in the
hypothesis list — the window, the uniformity, the fullness, the scale relations, the Frostman
datum, `K_KT(β)`, `K_F(β)` — is irrelevant to the contradiction.

Proof: pick `i ∈ q`, put `k := assign i ∈ r`.  The block `{i ∈ q | assign i = k}` is nonempty,
so `Kakeya.not_plankFactorization_of_shadedTube` empties `Fz k`. -/
theorem localPlankFactorisation_hypotheses_uninhabited
    {ι : Type*} {δ : ℝ≥0} (hδ0 : 0 < δ)
    {q : Finset ι} (hq : q.Nonempty)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type} {r : Finset κ} (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    False := by
  classical
  obtain ⟨i, hi⟩ := hq
  obtain ⟨hk, -⟩ := hassign i hi
  have hne : ({i' ∈ q | assign i' = assign i} : Finset ι).Nonempty :=
    ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩⟩
  exact (not_plankFactorization_of_shadedTube (a := a) (b := b) (hab := hab) (hb1 := hb1)
    hδ0 hne T C₀).elim (Fz (assign i) hk)

open Classical in
/-- **The sharp form of the vacuity: under 6.6(A)'s hypotheses with `q` nonempty, everything is
provable.**

So the multiplicity bound in the conclusion of
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` carries no information: replacing it by `0 = 1`
would give an equally provable theorem.  The remaining content of the statement is the empty case
`q = ∅`, where `ShadedBody.multiplicity_empty` closes it. -/
theorem localPlankFactorisation_proves_anything (P : Prop)
    {ι : Type*} {δ : ℝ≥0} (hδ0 : 0 < δ)
    {q : Finset ι} (hq : q.Nonempty)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {κ : Type} {r : Finset κ} (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    P :=
  (localPlankFactorisation_hypotheses_uninhabited hδ0 hq T R hassign Fz).elim


/-! ## The second, independent defect: the scale ordering of 6.6(A) is backwards

The vacuity above is a defect of the *datum* (`Kakeya.PlankFactorization.parts_are_planks`).  It is
not the only one.  `Kakeya.tubeMultiplicityOfLocalPlankFactorisation` also carries the part-(B)
scale ordering `δ ≤ ρ → ρ ≤ a`, and that ordering is wrong for part (A).

In part (A) the planks sit **inside** the coarse `ρ`-tube — that is the whole difference from part
(B), where the coarse tubes sit inside the planks — so the transverse width of an outer body is
bounded by the coarse radius: `b ≤ 2 ρ`
(`Kakeya.b_le_two_mul_of_comparableBodyFactorization`, proved for the *repaired* part-(A) datum
`Kakeya.ComparableBodyFactorization`).  Adding 6.6(A)'s own `ρ ≤ a ≤ b` forces
`b ≤ 2 ρ ≤ 2 a ≤ 2 b`, i.e. `a ≍ b ≍ ρ`: the eccentricity gain `(a / b) ^ (3 β / 2)` of the
conclusion is then bounded below by the absolute constant `2 ^ (-3 β / 2)`, so the statement is
quantitatively empty even after the datum is repaired.

The correct part-(A) ordering is `δ ≤ a ≤ b ≲ ρ ≤ 1`, as carried by
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` (`Kakeya/Factoring/FlatPrisms.lean`).  This
is why 6.6(A) must be *restated*, not patched: the two defects are independent, and repairing the
datum alone leaves a true but gain-free theorem.
-/

open Classical in
/-- **The scale ordering of GWZ 6.6(A) collapses the eccentricity.**

Under the repaired part-(A) datum together with 6.6(A)'s own scale hypothesis `ρ ≤ a`, the two
transverse scales are comparable: `b ≤ 2 * a`.  So the factor `(a / b) ^ (3 β / 2)` that the
conclusion of `Kakeya.tubeMultiplicityOfLocalPlankFactorisation` advertises as a gain is at least
`2 ^ (-3 β / 2)`, an absolute constant.

Note which hypotheses are used: only nonemptiness of `q`, the assignment clause, the part-(A)
factorisations, and `ρ ≤ a`.  Neither `K_KT(β)` nor `K_F(β)` nor any analytic input appears. -/
theorem localPlankFactorisation_scaleOrder_collapses {ι κ : Type*}
    {δ ρ a b : ℝ≥0} (hb1 : b ≤ 1) (hρa : ρ ≤ a)
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hq : q.Nonempty)
    {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, ComparableBodyFactorization b
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    b ≤ 2 * a := by
  have h := b_le_two_mul_of_comparableBodyFactorization hb1 hq hassign Fz
  calc b ≤ 2 * ρ := h
    _ ≤ 2 * a := by gcongr

end Kakeya

end

end
