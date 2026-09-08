/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6PartBDataBridgeUniv
public import Kakeya.DimensionThree.Plank.Prop66BUniverseFree
public import Kakeya.DimensionThree.Plank.Prop66BCoarseScale

/-!
# GWZ Proposition 6.6(B): the residue of the fine-ED chain, and the parent-window assembly

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Prop66BClose.lean`, where it is proved; it was stated in
`Kakeya/DimensionThree/Plank/Factorization.lean` until then) carries, since, the
fine-family essential-distinctness binder, so the proved Part-(B) chain
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData_univ`
(`Kakeya/DimensionThree/Plank/Prop66BUniverseFree.lean`) is *shaped* to prove it.  Between the two
stand the datum blockers   This file records exactly where that
stands after  :

* **universe (T3) — closed**: `Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv`
  builds the datum from the pair `(PS, Fz)` for a leaf index type in any universe;
* **`Remark53Prop51` (T5) — the residue**: `Kakeya.Prop66BPartBChainConstructed` below is the
  chain head *without* `Kakeya.Section6PartBData.Remark53Prop51` and *without* the essential
  distinctness of the representative planks, and *with* the three clauses the constructed
  Proposition-5.1 route consumes and the datum built from `(PS, Fz)` supplies (nonempty coarse
  fibres, plank dimensions of the cell bodies, GWZ Lemma 4.1 item (ii) on the coarse fibres);
* **outer-representative ED (T7)** — not needed by the residue as stated: on the constructed route
  the outer family is extracted essentially distinct
  (`Kakeya.exists_pairwise_ED_collarPlank_subfamily`), so the residue does not ask for it;
* **parent window (T4) — open, and not a proof-level matter here**: the theorem below derives, from
  the residue, the project statement *with the parent window added*
  (`Kakeya.Prop66BScale.statement_of_universal_prop66B_essDistinct_parentWindow`).  The window is
  the one hypothesis of the datum construction that the project statement does not carry, and this
  development cannot recover it at proof level: `Tube` has a unit core (`Tube.dist_eq_one`), so no
  homothety maps tubes to tubes, and the framed representative plank fits the working window only
  for bodies inside the *unit* ball (`Kakeya.framedPlank_subset_closedBall`, whose arithmetic is
  tight at `A = B = 1`, and `Kakeya.le_framedPlank`, which needs the body's long coordinate `≤ 1`).
  At the single application site the window is supplied
  (`Kakeya.ML2Reduction.PlankFactoringData.ball`, `Kakeya.parentWindow_of_plankFactoringData`).

## The residue, precisely

`Kakeya.Prop66BPartBChainConstructed β` is
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData_univ` with

* the hypothesis `D.Remark53Prop51 Cprop` **deleted** (and with it the parameter `Cprop`);
* the pairwise essential distinctness of `D.factor.repr` **deleted**;
* three hypotheses **added**, each supplied by
  `Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv` from `Fz` alone: every used cell
  has a nonempty coarse fibre; every cell body is a plank of dimensions `a × b × 1` up to a
  sub-polynomial constant `K` (`Kakeya.IsPlankOfDimensions`, from
  `Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`); and every cell's coarse fibre
  attains the maximal density of the coarse family up to `C₀` inside the cell body (the
  `maxDensity_le_mul` clause of `ConvexSpaceBody.Factorization`, GWZ Lemma 4.1 item (ii)).

Every one of the added hypotheses is what the constructed Proposition-5.1 route
(`Kakeya.Section6PartBData.exists_plank_presented_split_of_blockPigeonhole`,
`Kakeya.PartBLoss.exists_threshold_partB_outer_fullness`,
`Kakeya.exists_pairwise_ED_collarPlank_subfamily`) asks of the datum, so the residue is the honest
statement of what remains: rebuild `Kakeya.Section6PartBData.OuterPackage` over that constructed
output and run the existing inner pipeline on it.  Nothing here is proved about the residue except
what it implies.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

universe u

namespace Kakeya

/-! ### The residue -/

open Classical in
/-- **The Part-(B) chain of GWZ Proposition 6.6(B), over the constructed Proposition-5.1 output.**

The chain head `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData_univ` with the
unconstructible presentation contract `Kakeya.Section6PartBData.Remark53Prop51` and the outer
representative essential distinctness removed, and the three datum clauses that
`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv` supplies added.  See the module
docstring.  This is the single hypothesis between the fine-ED chain and the project
statement of Proposition 6.6(B) *with the parent window*
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed`). -/
def Prop66BPartBChainConstructed (β : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0), ∃ s₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (q : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
        {κ : Type*} (r : Finset κ)
        (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ K : ℝ≥0),
        C₀ ≤ δ ^ (-η) → CF ≤ δ ^ (-η) → Cfib ≤ δ ^ (-η) → K ≤ δ ^ (-η) →
        δ ≤ ρ → ρ ≤ a → δ ≤ s₀ * a →
        ∀ (D : Section6PartBData a b hab hb1 q T r R m Cfib CF C₀),
        (∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) →
        (∀ x ∈ D.factor.cells, IsPlankOfDimensions K a b (D.factor.body x)) →
        (∀ x ∈ D.factor.cells,
          maxDensity r (fun k => (R k).toConvexSpaceBody) ≤
            (C₀ : ENNReal) * densityIn (D.factor.coarseFibre x)
              (fun k => (R k).toConvexSpaceBody) (D.factor.body x)) →
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β

namespace Prop66BScale

open Classical in
/-- **The project statement of GWZ Proposition 6.6(B), verbatim**: the pinned
`statement_of_universal_prop66B_essDistinct` with the parent window
`∀ k ∈ PS.parent, (PS.parentTube k).carrier ⊆ Metric.closedBall 0 1` inserted after the branching
floor.  It is the type of `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (the compatibility
`example` beside that theorem in `Kakeya/DimensionThree/Plank/Prop66BClose.lean` pins it there); it
is what the fine-ED chain reaches from
`Kakeya.Prop66BPartBChainConstructed`
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed`); and the one
application site supplies the extra binder verbatim
(`Kakeya.ML2Reduction.PlankFactoringData.ball`, i.e. `Kakeya.parentWindow_of_plankFactoringData`).
The window is GWZ's tacit `O(1)` window at the parent scale made exact —  classifies it as
an explicitation below source resolution, forced by the unit core of `Tube` (`Tube.dist_eq_one`),
and revises  (ii) on this point; the fifth fidelity note in the docstring of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` gives the reading.  The alternative form stays
pinned as `statement_of_universal_prop66B_essDistinct`. -/
def statement_of_universal_prop66B_essDistinct_parentWindow (β ε₂ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ δ₀ > (0 : ℝ≥0),
    ∀ {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (_hδ0 : 0 < δ)
      (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      δ ≤ δ₀ →
      (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (q : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      (∃ C : ℝ≥0, C ≤ δ ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet q T (Tube.ssfGridLen δ) C)) →
      (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
      ∀ (ρ a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (Cw Cpar C₀ : ℝ≥0),
        Cw ≤ δ ^ (-η) → Cpar ≤ δ ^ (-η) → C₀ ≤ δ ^ (-η) →
        (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ → ρ ≤ a →
        ∀ (PS : Tube.IsUniformAtScale q (fun i ↦ (T i).toTube) ρ Cpar),
        (max 1 Cpar) ^ 2 ≤ PS.branchingN →
        (∀ k ∈ PS.parent, (PS.parentTube k).carrier ⊆ Metric.closedBall 0 1) →
        ∀ (_Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
          (fun k ↦ (PS.parentTube k).toConvexSpaceBody) C₀),
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          (δ : ENNReal) ^ (-ε)
            * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β

end Prop66BScale

/-! ### The constants of the datum built from `(PS, Fz)` are sub-polynomial -/

namespace GlobalPlankFactorization

/-- `plankReadingConst Cw C₀ ≤ 3 · Cw · max 1 C₀`. -/
theorem plankReadingConst_le {Cw C₀ : ℝ≥0} (hCw : 1 ≤ Cw) :
    plankReadingConst Cw C₀ ≤ 3 * (Cw * max 1 C₀) := by
  have hM1 : (1 : ℝ≥0) ≤ Cw * max 1 C₀ := one_le_mul_of_one_le_of_one_le hCw (le_max_left _ _)
  unfold plankReadingConst
  refine max_le ?_ (max_le ?_ ?_)
  · calc (3 : ℝ≥0) = 3 * 1 := (mul_one 3).symm
      _ ≤ 3 * (Cw * max 1 C₀) := by gcongr
  · calc 2 * Cw ≤ 3 * Cw := by gcongr; norm_num
      _ = 3 * (Cw * 1) := by ring
      _ ≤ 3 * (Cw * max 1 C₀) := by gcongr; exact le_max_left _ _
  · calc C₀ ≤ max 1 C₀ := le_max_right _ _
      _ = 1 * (1 * max 1 C₀) := by ring
      _ ≤ 3 * (Cw * max 1 C₀) := by gcongr; norm_num

/-- `partBFrostmanConst Cw C₀ ≤ 11664 · (Cw · max 1 C₀) ^ 6`: the Frostman constant of the datum
built from `(PS, Fz)` is a fixed polynomial in `Cw` and `C₀`. -/
theorem partBFrostmanConst_le {Cw C₀ : ℝ≥0} (hCw : 1 ≤ Cw) :
    partBFrostmanConst Cw C₀ ≤ 11664 * (Cw * max 1 C₀) ^ 6 := by
  set M : ℝ≥0 := Cw * max 1 C₀ with hM_def
  have hM1 : (1 : ℝ≥0) ≤ M := one_le_mul_of_one_le_of_one_le hCw (le_max_left _ _)
  have hK : plankReadingConst Cw C₀ ≤ 3 * M := plankReadingConst_le hCw
  have hC₀M : C₀ ≤ M := le_trans (le_max_right 1 C₀) (le_mul_of_one_le_left' hCw)
  have hc3 : Metric.lt_volume_convexHull.c 3 = (6 : ℝ≥0)⁻¹ := by
    norm_num [Metric.lt_volume_convexHull.c]
  have hloss : plankFrostmanLoss (plankReadingConst Cw C₀)
      = 48 * plankReadingConst Cw C₀ ^ 3 := by
    unfold plankFrostmanLoss
    rw [hc3, inv_inv]
    ring
  unfold partBFrostmanConst coarseFibreFrostmanConst
  refine max_le ?_ ?_
  · calc (1 : ℝ≥0) ≤ M ^ 6 := one_le_pow₀ hM1
      _ = 1 * M ^ 6 := (one_mul _).symm
      _ ≤ 11664 * M ^ 6 := by gcongr; norm_num
  · rw [hloss]
    calc C₀ * (48 * plankReadingConst Cw C₀ ^ 3 * plankReadingConst Cw C₀ ^ 2)
        = 48 * (C₀ * plankReadingConst Cw C₀ ^ 5) := by ring
      _ ≤ 48 * (M * (3 * M) ^ 5) := by
          gcongr
      _ = 11664 * M ^ 6 := by ring

/-- **The cell bodies of the datum built from `(PS, Fz)` are planks of dimensions
`uniformThin × uniformMid × 1`, up to `plankReadingConst ^ 2`.**

`Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions` gives the dimensions
`a' × b × 1` at constant `K = plankReadingConst Cw C₀`; the re-declared half-widths satisfy
`a' ≤ K · uniformThin`, `uniformThin ≤ K · a'`, `b ≤ K · uniformMid`, `uniformMid ≤ K · b`, so the
same bodies have dimensions `uniformThin × uniformMid × 1` at constant `K ^ 2`. -/
theorem isPlankOfDimensions_cellBody_uniform {κ : Type*} [DecidableEq κ]
    {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    (Fz : GlobalPlankFactorization Cw a b hab hb1 r (fun k => (Rt k).toConvexSpaceBody) C₀)
    (hCw : 1 ≤ Cw) (hb1' : b ≤ 1) (hne : Fz.parts.Nonempty)
    {t : Finset κ} (ht : t ∈ Fz.parts) :
    IsPlankOfDimensions (plankReadingConst Cw C₀ ^ 2) Fz.uniformThin Fz.uniformMid
      (cellBody t Rt) := by
  classical
  set K : ℝ≥0 := plankReadingConst Cw C₀ with hK_def
  have hK1 : (1 : ℝ≥0) ≤ K := one_le_plankReadingConst Cw C₀
  have hK0 : K ≠ 0 := (lt_of_lt_of_le zero_lt_one hK1).ne'
  have hK20 : K ^ 2 ≠ 0 := pow_ne_zero 2 hK0
  obtain ⟨a', -, -, hfam⟩ := Fz.exists_isPlankFamilyOfDimensions hCw hb1' hne
  have hthin : Fz.uniformThin ≤ K * a' := Fz.uniformThin_le_mul hCw hb1' hne hfam
  have hmid : Fz.uniformMid ≤ K * b := Fz.uniformMid_le_mul hfam
  have hbB : b ≤ K * Fz.uniformMid := Fz.le_mul_uniformMid hCw hb1' hne
  have hτ2 : thicknessNN (cellBody t Rt) 2 ≤ Fz.uniformThin := Fz.thicknessNN_two_le_uniformThin ht
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩, ⟨h20, h21⟩⟩ := hfam t ht
  -- pass to `ℝ≥0`
  rw [← coe_thicknessNN, ← ENNReal.coe_inv hK0, ENNReal.coe_le_coe] at h00
  rw [← coe_thicknessNN, ENNReal.coe_le_coe] at h01
  rw [← coe_thicknessNN, ← ENNReal.coe_inv hK0, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h10
  rw [← coe_thicknessNN, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h11
  rw [← coe_thicknessNN, ← ENNReal.coe_inv hK0, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h20
  rw [← coe_thicknessNN, ← ENNReal.coe_mul, ENNReal.coe_le_coe] at h21
  have hKK : K ≤ K ^ 2 := by
    calc K = K * 1 := (mul_one K).symm
      _ ≤ K * K := by gcongr
      _ = K ^ 2 := by ring
  have hinvKK : (K ^ 2)⁻¹ ≤ K⁻¹ := inv_anti₀ (lt_of_lt_of_le zero_lt_one hK1) hKK
  have hmulinv : ∀ x : ℝ≥0, (K ^ 2)⁻¹ * (K * x) = K⁻¹ * x := by
    intro x
    rw [pow_two, mul_inv, mul_assoc, ← mul_assoc K⁻¹ K x, inv_mul_cancel₀ hK0, one_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← coe_thicknessNN, ← ENNReal.coe_inv hK20, ENNReal.coe_le_coe]
    exact hinvKK.trans h00
  · rw [← coe_thicknessNN, ENNReal.coe_le_coe]
    exact h01.trans hKK
  · rw [← coe_thicknessNN, ← ENNReal.coe_inv hK20, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    calc (K ^ 2)⁻¹ * Fz.uniformMid ≤ (K ^ 2)⁻¹ * (K * b) := by gcongr
      _ = K⁻¹ * b := hmulinv b
      _ ≤ thicknessNN (cellBody t Rt) 1 := h10
  · rw [← coe_thicknessNN, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    calc thicknessNN (cellBody t Rt) 1 ≤ K * b := h11
      _ ≤ K * (K * Fz.uniformMid) := by gcongr
      _ = K ^ 2 * Fz.uniformMid := by ring
  · rw [← coe_thicknessNN, ← ENNReal.coe_inv hK20, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    calc (K ^ 2)⁻¹ * Fz.uniformThin ≤ (K ^ 2)⁻¹ * (K * a') := by gcongr
      _ = K⁻¹ * a' := hmulinv a'
      _ ≤ thicknessNN (cellBody t Rt) 2 := h20
  · rw [← coe_thicknessNN, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    calc thicknessNN (cellBody t Rt) 2 ≤ Fz.uniformThin := hτ2
      _ = 1 * Fz.uniformThin := (one_mul _).symm
      _ ≤ K ^ 2 * Fz.uniformThin := by gcongr; exact one_le_pow₀ hK1

end GlobalPlankFactorization

/-! ### The assembly -/

/-- A nonempty fine family, from positive fullness. -/
theorem nonempty_of_rpow_le_fullness {ι : Type*} {q : Finset ι} {δ : ℝ≥0} (hδ0 : 0 < δ)
    {η : ℝ} (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hfull : (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q V) : q.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hpos : 0 < ShadedBody.fullness q V := lt_of_lt_of_le (NNReal.rpow_pos hδ0) hfull
  have hne := ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos q V hpos
  subst h
  simp at hne

set_option maxHeartbeats 1000000 in
-- The residue is a six-level telescope over the whole datum; instantiating it at the constructed
-- datum and its three clauses exceeds the default budget.
open Classical in
/-- **GWZ Proposition 6.6(B) with the parent window, from the residue of the fine-ED chain.**

Given `Kakeya.Prop66BPartBChainConstructed β`, the project statement with the parent-window binder
follows: the datum is `Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv'` (universe-free,
 T3), its three constants are sub-polynomial
(`Kakeya.GlobalPlankFactorization.partBFrostmanConst_le`, the fibre constant `2 · (max 1 Cpar)²`,
and `plankReadingConst ^ 2`), the inner threshold `δ ≤ s₀ · uniformThin` is
`Kakeya.Prop66BScale.le_mul_of_plankScale_le` through
`Kakeya.GlobalPlankFactorization.le_mul_uniformThin_of_le_mul_rho`, the three datum clauses of the
residue come from `Fz` (`Kakeya.GlobalPlankFactorization.isPlankOfDimensions_cellBody_uniform`,
`Kakeya.GlobalPlankFactorization.coarseFibre_toSection6PartBFactorisationFin`,
`ConvexSpaceBody.Factorization.maxDensity_le_mul`), and the conclusion at the re-declared
half-widths is carried back to `(a, b)` by `Kakeya.GlobalPlankFactorization.uniformThin_le` and
`Kakeya.GlobalPlankFactorization.le_mul_uniformMid`, at the sub-polynomial cost
`plankReadingConst ^ β`.

The hypothesis `hε₂1 : ε₂ ≤ 1` is not consumed; it is retained so that the shape matches the
project statement's. -/
theorem tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1) {ε₂ : ℝ} (hε₂0 : 0 < ε₂) (_hε₂1 : ε₂ ≤ 1)
    (R : Prop66BPartBChainConstructed.{u, u} β) :
    Prop66BScale.statement_of_universal_prop66B_essDistinct_parentWindow.{u} β ε₂ := by
  intro ε hε
  obtain ⟨η', hη', δ₀', hδ₀', s₀, hs₀, hR⟩ := R (ε / 2) (by positivity)
  set η : ℝ := min (η' / 24) (ε / 8) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη24 : η ≤ η' / 24 := min_le_left _ _
  have hη8 : η ≤ ε / 8 := min_le_right _ _
  have hηη' : η ≤ η' := by linarith
  -- thresholds: the absolute constants of the datum, and the inner scale
  obtain ⟨d1, hd1, hfun1⟩ :=
    exists_threshold_le_rpow_neg (11664 : ℝ≥0) (by norm_num) (show (0 : ℝ) < η' / 2 by positivity)
  obtain ⟨d3, hd3, hfun3⟩ :=
    exists_threshold_le_rpow_neg (3 : ℝ≥0) (by norm_num) (show (0 : ℝ) < ε / 4 by positivity)
  have hs₀pow : (0 : ℝ≥0) < s₀ ^ (1 / ε₂) := NNReal.rpow_pos hs₀
  refine ⟨η, hη, min (min δ₀' 1) (min (min d1 d3) (s₀ ^ (1 / ε₂))),
    lt_min (lt_min hδ₀' one_pos) (lt_min (lt_min hd1 hd3) hs₀pow), ?_⟩
  intro ι q δ hδ0 T hδ hball hEDq _huni hfull ρ a b hab hb1 Cw Cpar C₀ hCw hCpar hC₀ hρlb hρa
    PS hbr hballs Fz
  -- unwind the threshold
  have hδδ₀' : δ ≤ δ₀' := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδd1 : δ ≤ d1 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδd3 : δ ≤ d3 :=
    hδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδs₀ : δ ≤ s₀ ^ (1 / ε₂) := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the scales
  have hδρ : δ ≤ ρ := Prop66BScale.le_of_plankScale_le hδ0 hδ1 hε₂0.le hρlb
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 hδρ
  have hb0 : 0 < b := lt_of_lt_of_le hρ0 (hρa.trans hab)
  have hq : q.Nonempty := nonempty_of_rpow_le_fullness hδ0 _ hfull
  have hne : Fz.parts.Nonempty := by
    obtain ⟨j, hj⟩ := parent_nonempty_of_nonempty PS hq
    obtain ⟨t, ht, _⟩ := Fz.toFinpartition.exists_mem hj
    exact ⟨t, ht⟩
  have hCw1 : (1 : ℝ≥0) ≤ Cw := Fz.one_le_Cw
  -- the datum
  set D := Section6PartBData.ofUniformAtScaleOfGlobalPlankUniv' PS Fz hδρ hbr hb0 hρ0 hq hballs
    with hD_def
  -- the re-declared half-widths and the reading constant
  set A : ℝ≥0 := Fz.uniformThin with hA_def
  set B : ℝ≥0 := Fz.uniformMid with hB_def
  set K : ℝ≥0 := plankReadingConst Cw C₀ with hK_def
  set M : ℝ≥0 := Cw * max 1 C₀ with hM_def
  have hK1 : (1 : ℝ≥0) ≤ K := one_le_plankReadingConst Cw C₀
  have hKM : K ≤ 3 * M := GlobalPlankFactorization.plankReadingConst_le (C₀ := C₀) hCw1
  -- sub-polynomial budgets
  have hpow : ∀ {s t : ℝ}, s ≤ t → (δ : ℝ≥0) ^ (-s) ≤ δ ^ (-t) :=
    fun hst => NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (neg_le_neg hst)
  have hone : (1 : ℝ≥0) ≤ δ ^ (-η) := by
    have := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (show -η ≤ (0 : ℝ) by linarith)
    simpa using this
  have hmax : max 1 C₀ ≤ δ ^ (-η) := max_le hone hC₀
  have hδne : δ ≠ 0 := hδ0.ne'
  have hMδ : M ≤ δ ^ (-(2 * η)) := by
    calc M = Cw * max 1 C₀ := rfl
      _ ≤ δ ^ (-η) * δ ^ (-η) := mul_le_mul' hCw hmax
      _ = δ ^ (-(2 * η)) := by rw [← NNReal.rpow_add hδne]; congr 1; ring
  have hM6 : M ^ 6 ≤ δ ^ (-(12 * η)) := by
    calc M ^ 6 ≤ (δ ^ (-(2 * η))) ^ 6 := pow_le_pow_left' hMδ 6
      _ = δ ^ (-(12 * η)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; congr 1; push_cast; ring
  have h11664 : (11664 : ℝ≥0) ≤ δ ^ (-(η' / 2)) := hfun1 δ hδ0 hδd1
  have hhalf : (δ : ℝ≥0) ^ (-(η' / 2)) * δ ^ (-(η' / 2)) = δ ^ (-η') := by
    rw [← NNReal.rpow_add hδne]; congr 1; ring
  have hC₀' : C₀ ≤ δ ^ (-η') := hC₀.trans (hpow hηη')
  have hCF : GlobalPlankFactorization.partBFrostmanConst Cw C₀ ≤ δ ^ (-η') := by
    calc GlobalPlankFactorization.partBFrostmanConst Cw C₀ ≤ 11664 * M ^ 6 :=
          GlobalPlankFactorization.partBFrostmanConst_le (C₀ := C₀) hCw1
      _ ≤ δ ^ (-(η' / 2)) * δ ^ (-(η' / 2)) := by
          refine mul_le_mul' h11664 (hM6.trans (hpow ?_))
          linarith
      _ = δ ^ (-η') := hhalf
  have hCfib : 2 * max 1 Cpar ^ 2 ≤ δ ^ (-η') := by
    have hmaxp : max 1 Cpar ≤ δ ^ (-η) := max_le hone hCpar
    calc 2 * max 1 Cpar ^ 2 ≤ 11664 * (δ ^ (-η)) ^ 2 := by
          gcongr; norm_num
      _ = 11664 * δ ^ (-(2 * η)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; congr 2; push_cast; ring
      _ ≤ δ ^ (-(η' / 2)) * δ ^ (-(η' / 2)) := by
          refine mul_le_mul' h11664 (hpow ?_)
          linarith
      _ = δ ^ (-η') := hhalf
  have hK2 : K ^ 2 ≤ δ ^ (-η') := by
    calc K ^ 2 ≤ (3 * M) ^ 2 := pow_le_pow_left' hKM 2
      _ = 9 * M ^ 2 := by ring
      _ ≤ 11664 * (δ ^ (-(2 * η))) ^ 2 := by gcongr; norm_num
      _ = 11664 * δ ^ (-(4 * η)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]; congr 2; push_cast; ring
      _ ≤ δ ^ (-(η' / 2)) * δ ^ (-(η' / 2)) := by
          refine mul_le_mul' h11664 (hpow ?_)
          linarith
      _ = δ ^ (-η') := hhalf
  have hKε : K ≤ δ ^ (-(ε / 2)) := by
    calc K ≤ 3 * M := hKM
      _ ≤ δ ^ (-(ε / 4)) * δ ^ (-(ε / 4)) := by
          refine mul_le_mul' (hfun3 δ hδ0 hδd3) (hMδ.trans (hpow ?_))
          linarith
      _ = δ ^ (-(ε / 2)) := by rw [← NNReal.rpow_add hδne]; congr 1; ring
  -- the fullness at the residue's exponent
  have hfull' : (δ : ℝ≥0) ^ η' ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) :=
    le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hηη') hfull
  -- the scales at the re-declared thin half-width
  have hρA : ρ ≤ A := Fz.le_uniformThin hne
  have hδs₀A : δ ≤ s₀ * A :=
    Fz.le_mul_uniformThin_of_le_mul_rho hne
      (Prop66BScale.le_mul_of_plankScale_le hδ0 hε₂0 hδs₀ hρlb le_rfl)
  -- the three datum clauses
  have hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty := by
    intro j _
    change ((Fz.toSection6PartBFactorisationFin Fz.one_le_Cw hb1 hb0 hρ0 hne hballs).coarseFibre
      j).Nonempty
    rw [GlobalPlankFactorization.coarseFibre_toSection6PartBFactorisationFin]
    exact Fz.nonempty_of_mem_parts (Fz.cellEquiv j).2
  have hdim : ∀ x ∈ D.factor.cells, IsPlankOfDimensions (K ^ 2) A B (D.factor.body x) := by
    intro j _
    change IsPlankOfDimensions (K ^ 2) A B
      (GlobalPlankFactorization.cellBody (Fz.cellEquiv j).1 PS.parentTube)
    exact Fz.isPlankOfDimensions_cellBody_uniform hCw1 hb1 hne (Fz.cellEquiv j).2
  have hdens : ∀ x ∈ D.factor.cells,
      maxDensity PS.parent (fun k => (PS.parentTube k).toConvexSpaceBody) ≤
        (C₀ : ENNReal) * densityIn (D.factor.coarseFibre x)
          (fun k => (PS.parentTube k).toConvexSpaceBody) (D.factor.body x) := by
    intro j _
    change maxDensity PS.parent (fun k => (PS.parentTube k).toConvexSpaceBody) ≤
        (C₀ : ENNReal) * densityIn
          ((Fz.toSection6PartBFactorisationFin Fz.one_le_Cw hb1 hb0 hρ0 hne hballs).coarseFibre j)
          (fun k => (PS.parentTube k).toConvexSpaceBody)
          (GlobalPlankFactorization.cellBody (Fz.cellEquiv j).1 PS.parentTube)
    rw [GlobalPlankFactorization.coarseFibre_toSection6PartBFactorisationFin]
    exact Fz.maxDensity_le_mul (Fz.cellEquiv j).1 (Fz.cellEquiv j).2
  -- the residue
  have hmain : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-(ε / 2)) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
        * ((A : ENNReal) / (B : ENNReal)) ^ β * (q.card : ENNReal) ^ β :=
    hR q hδ0 T hδδ₀' hball hEDq hfull' ρ A B _ _ _ _ _ _ _ C₀ (K ^ 2) hC₀' hCF hCfib hK2
      hδρ hρA hδs₀A D hcfne hdim hdens
  -- carry the eccentricity factor back to `(a, b)`
  have hAa : A ≤ a := Fz.uniformThin_le
  have hbB : b ≤ K * B := Fz.le_mul_uniformMid hCw1 hb1 hne
  have hK0E : (K : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hK1).ne'
  have hKtop : (K : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hratio : (A : ENNReal) / (B : ENNReal)
      ≤ (K : ENNReal) * ((a : ENNReal) / (b : ENNReal)) := by
    calc (A : ENNReal) / (B : ENNReal) ≤ (a : ENNReal) / (B : ENNReal) :=
          ENNReal.div_le_div (by exact_mod_cast hAa) le_rfl
      _ = ((K : ENNReal) * (a : ENNReal)) / ((K : ENNReal) * (B : ENNReal)) :=
          (ENNReal.mul_div_mul_left _ _ hK0E hKtop).symm
      _ ≤ ((K : ENNReal) * (a : ENNReal)) / (b : ENNReal) := by
          refine ENNReal.div_le_div le_rfl ?_
          exact_mod_cast hbB
      _ = (K : ENNReal) * ((a : ENNReal) / (b : ENNReal)) := mul_div_assoc _ _ _
  have hK1E : (1 : ENNReal) ≤ (K : ENNReal) := by exact_mod_cast hK1
  have hratioβ : ((A : ENNReal) / (B : ENNReal)) ^ β
      ≤ (δ : ENNReal) ^ (-(ε / 2)) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
    calc ((A : ENNReal) / (B : ENNReal)) ^ β
        ≤ ((K : ENNReal) * ((a : ENNReal) / (b : ENNReal))) ^ β :=
          ENNReal.rpow_le_rpow hratio hβpos.le
      _ = (K : ENNReal) ^ β * ((a : ENNReal) / (b : ENNReal)) ^ β :=
          ENNReal.mul_rpow_of_nonneg _ _ hβpos.le
      _ ≤ (K : ENNReal) ^ (1 : ℝ) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
          gcongr
      _ = (K : ENNReal) * ((a : ENNReal) / (b : ENNReal)) ^ β := by rw [ENNReal.rpow_one]
      _ ≤ (δ : ENNReal) ^ (-(ε / 2)) * ((a : ENNReal) / (b : ENNReal)) ^ β := by
          gcongr
          rw [← ENNReal.coe_rpow_of_ne_zero hδne]
          exact_mod_cast hKε
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδne
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : (δ : ENNReal) ^ (-ε) = (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) := by
    rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
  calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-(ε / 2)) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((A : ENNReal) / (B : ENNReal)) ^ β * (q.card : ENNReal) ^ β := hmain
    _ ≤ (δ : ENNReal) ^ (-(ε / 2)) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((δ : ENNReal) ^ (-(ε / 2)) * ((a : ENNReal) / (b : ENNReal)) ^ β)
          * (q.card : ENNReal) ^ β := by gcongr
    _ = (δ : ENNReal) ^ (-ε) * (maxDensity q (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by
        rw [hsplit]; ring

end Kakeya

end

end
