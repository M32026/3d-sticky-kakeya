/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankDatumBridge
public import Kakeya.DimensionThree.Volume

/-!
# `def:Factors` clause (ii): the hull reading and the plank reading

The blueprint's `def:Factors` (`blueprint/src/GWZAdapted/section4.tex`) asks, for a factorization
of a family `𝕍 = (V i)` by outer bodies `(W t)`, that

  (ii)  `Δ_max(𝕍) ≤ C · Δ(𝕍_t, W_t)`   for every block `t`,

where `W_t` is, in the definition's own words, *"a convex body containing `V i` for every `i ∈ t`"*.
The blueprint then records, immediately after the definition, that

  *"The Lean structure uses the canonical choice `W_t = conv(⋃_{i∈t} V i)`.  The more flexible
  condition above also permits a specified containing body, which is convenient when the outer
  bodies are planks or tubes."*

In GWZ Proposition 6.6(B) the outer bodies **are** planks, so GWZ reads clause (ii) against the
plank; `ConvexSpaceBody.Factorization` hard-wires the hull.  This file settles the relation between
the two readings.

## What is proved here

* `Kakeya.FactorsDensityAt.hull` — **the plank reading implies the hull reading**, at the same
  constant and with no hypothesis beyond `V i ≤ W t`.  Hence GWZ's hypothesis for 6.6(B) is
  *stronger* than the one `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` assumes, so that
  statement is at least as strong as GWZ Proposition 6.6(B) and needs no restatement.  This is the
  fidelity settlement.

* `Kakeya.isFrostmanIn_of_le_of_volume_le` and
  `Kakeya.GlobalPlankFactorization.isFrostmanIn_plank_of_isPlankOfDimensions` — the converse
  direction, **quantified**.  The hull reading gives the plank reading against *any* outer plank
  `P₂ ⊇ W`, with the loss `8 C³ / c₃ · (|P₂| / |W|)`, and the plank reading against a plank of
  half-widths `(a₂, b₂, 1)` costs exactly the volume ratio `a₂ b₂ / (a' b)`, where `a'` is the
  actual thin thickness of the cell hull `W`.

* `Kakeya.HasPlankEnvelope` — the residual geometric obligation isolated: an outer plank of
  half-widths comparable to `(a', b, 1)`, i.e. one that is *tight* on the hull.  Against the plank
  handed over by `Kakeya.GlobalPlankFactorization.le_plank` the loss carries the unbounded factor
  `a / a'` (`Kakeya.GlobalPlankFactorization.exists_isFrostmanIn_le_plank_of_thin_comparable` makes
  the dependence explicit); against a tight envelope the loss depends only on the comparability
  constant.

## Why this is the shape of the repair

`Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` is exactly clause (ii) in the plank
reading, and it is what the tree's proved Part-(B) pipeline
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`) consumes.  Producing it from the
6.6(B) datum is therefore the bridge that the proposition's proof needs, and by the results here
that bridge is *purely* a matter of exhibiting a tight outer plank: no further Frostman input is
required.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody

open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-! ### The two readings of clause (ii) -/

section ClauseTwo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A block is at least as dense in its own convex hull as in any body containing it.**

The two densities have the same numerator — every member of the block lies in both bodies, so the
containment filter of `ConvexSpaceBody.densityIn` is vacuous on both sides — and the hull has the
smaller volume. -/
theorem densityIn_le_densityIn_convexHull_biUnion {t : Finset ι} (ht : t.Nonempty)
    (V : ι → ConvexSpaceBody E) {W : ConvexSpaceBody E} (hVW : ∀ i ∈ t, V i ≤ W) :
    densityIn t V W ≤ densityIn t V (t.convexHull_biUnion V) := by
  have hhullW : t.convexHull_biUnion V ≤ W := (ht.convexHull_biUnion_le_iff V W).2 hVW
  have hVhull : ∀ i ∈ t, V i ≤ t.convexHull_biUnion V := fun i hi =>
    Finset.le_convexHull_biUnion V hi
  have hsub : ((t.convexHull_biUnion V).carrier : Set E) ⊆ (W.carrier : Set E) :=
    (SetLike.coe_subset_coe (S := t.convexHull_biUnion V) (T := W)).mp hhullW
  have hvol : volume ((t.convexHull_biUnion V).carrier : Set E) ≤ volume (W.carrier : Set E) :=
    measure_mono hsub
  rw [densityIn_of_all_le hVW, densityIn_of_all_le hVhull]
  exact ENNReal.div_le_div_left hvol _

/-- **`def:Factors` clause (ii) read against a specified containing body** — GWZ's reading, the one
Proposition 6.6(B) uses, where `W t` is the `a × b × 1` plank of the block `t`. -/
def FactorsDensityAt (s : Finset ι) (V : ι → ConvexSpaceBody E)
    (P : Finset (Finset ι)) (W : Finset ι → ConvexSpaceBody E) (C : ENNReal) : Prop :=
  ∀ t ∈ P, maxDensity s V ≤ C * densityIn t V (W t)

/-- **`def:Factors` clause (ii) read against the convex hull** — the reading hard-wired by
`ConvexSpaceBody.Factorization.maxDensity_le_mul`, and hence by
`Kakeya.GlobalPlankFactorization`. -/
def FactorsDensityHull (s : Finset ι) (V : ι → ConvexSpaceBody E)
    (P : Finset (Finset ι)) (C : ENNReal) : Prop :=
  ∀ t ∈ P, maxDensity s V ≤ C * densityIn t V (t.convexHull_biUnion V)

omit [DecidableEq ι] in
/-- **The plank reading implies the hull reading, at the same constant.**

This is the direction that settles fidelity: whatever outer bodies GWZ's `def:Factors` is read
against, as long as they contain their blocks, the hull reading follows.  So a theorem quantifying
over the *hull* reading — as `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` does — is at least
as strong as the same theorem quantifying over GWZ's plank reading, and restating it in the plank
reading would strictly weaken it. -/
theorem FactorsDensityAt.hull {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {P : Finset (Finset ι)} {W : Finset ι → ConvexSpaceBody E} {C : ENNReal}
    (hne : ∀ t ∈ P, t.Nonempty) (hVW : ∀ t ∈ P, ∀ i ∈ t, V i ≤ W t)
    (h : FactorsDensityAt s V P W C) : FactorsDensityHull s V P C := by
  intro t ht
  refine (h t ht).trans ?_
  gcongr
  exact densityIn_le_densityIn_convexHull_biUnion (hne t ht) V (hVW t ht)

omit [DecidableEq ι] in
/-- **Changing the ambient body of a Frostman estimate at an explicit volume cost.**

`ConvexSpaceBody.IsFrostmanIn.change_ambient` pays the exact ratio `|L| / |K|`; this packages the
ratio as a single bound `|L| ≤ L₀ · |K|`, which is the form in which the plank-versus-hull loss is
computed below. -/
theorem isFrostmanIn_of_le_of_volume_le {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {K L : ConvexSpaceBody E} {C L₀ : ENNReal}
    (hFr : IsFrostmanIn s V K C) (hVK : ∀ i ∈ s, V i ≤ K) (hKL : K ≤ L)
    (hK0 : volume (K.carrier : Set E) ≠ 0)
    (hvol : volume (L.carrier : Set E) ≤ L₀ * volume (K.carrier : Set E)) :
    IsFrostmanIn s V L (C * L₀) := by
  have hsub : (K.carrier : Set E) ⊆ (L.carrier : Set E) :=
    (SetLike.coe_subset_coe (S := K) (T := L)).mp hKL
  have hL0 : volume (L.carrier : Set E) ≠ 0 := fun h =>
    hK0 (le_antisymm (h ▸ measure_mono hsub) bot_le)
  have hratio : volume (L.carrier : Set E) / volume (K.carrier : Set E) ≤ L₀ :=
    ENNReal.div_le_of_le_mul hvol
  refine (hFr.change_ambient hVK (fun i hi => (hVK i hi).trans hKL) hK0 hL0).mono ?_
  gcongr

end ClauseTwo

/-! ### The plank reading of the GWZ 6.6(B) datum -/

/-- The absolute part of the loss incurred by reading `def:Factors` clause (ii) against an outer
plank rather than against the cell hull: the ratio between the crude volume upper bound `8 a₂ b₂`
of a plank and the `Kakeya.IsPlankOfDimensions.volume_lower` lower bound for the hull. -/
def plankFrostmanLoss (C : ℝ≥0) : ℝ≥0 := 8 * C ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹

theorem one_le_plankFrostmanLoss {C : ℝ≥0} (hC : 1 ≤ C) : 1 ≤ plankFrostmanLoss C := by
  have hCp : (1 : ℝ≥0) ≤ C ^ 3 := one_le_pow₀ hC
  have h8 : (1 : ℝ≥0) ≤ 8 * C ^ 3 := by
    calc (1 : ℝ≥0) = 1 * 1 := by norm_num
      _ ≤ 8 * C ^ 3 := mul_le_mul' (by norm_num) hCp
  have hc3 : Metric.lt_volume_convexHull.c 3 = (6 : ℝ≥0)⁻¹ := by
    norm_num [Metric.lt_volume_convexHull.c]
  have hinv : (1 : ℝ≥0) ≤ (Metric.lt_volume_convexHull.c 3)⁻¹ := by
    rw [hc3, inv_inv]; norm_num
  calc (1 : ℝ≥0) = 1 * 1 := by norm_num
    _ ≤ (8 * C ^ 3) * (Metric.lt_volume_convexHull.c 3)⁻¹ := mul_le_mul' h8 hinv
    _ = plankFrostmanLoss C := rfl

/-- **The volume of an outer plank, against the volume of the body it wraps.**

If `W` has the dimensions of an `a' × b × 1` plank up to `C`, and `P₂` is an exact
`a₂ × b₂ × 1` plank whose transverse area is at most `K` times `a' * b`, then
`|P₂| ≤ plankFrostmanLoss C * K * |W|`.  The whole content is `8 a₂ b₂ ≤ 8 K a' b` together with
`Kakeya.IsPlankOfDimensions.volume_lower`. -/
theorem volume_plank_le_mul_volume_of_isPlankOfDimensions
    {C a' b a₂ b₂ K : ℝ≥0} {hab₂ : a₂ ≤ b₂} {hb₂1 : b₂ ≤ 1}
    {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hC : 1 ≤ C) (hdimW : IsPlankOfDimensions C a' b W)
    (P₂ : Plank a₂ b₂ hab₂ hb₂1) (hcmp : a₂ * b₂ ≤ K * (a' * b)) :
    volume ((P₂.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      ≤ ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal) * volume (W.carrier : Set _) := by
  have hC0 : (C : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero]
    exact (lt_of_lt_of_le zero_lt_one hC).ne'
  have hc0 : (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
  have hC3ne : ((C : ENNReal) ^ 3) ≠ 0 := pow_ne_zero _ hC0
  have hC3top : ((C : ENNReal) ^ 3) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hlow := hdimW.volume_lower (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
  have hcoe : ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal)
      = 8 * (C : ENNReal) ^ 3 * (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ * (K : ENNReal) := by
    rw [plankFrostmanLoss]
    push_cast [ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne']
    ring
  set cc : ENNReal := (Metric.lt_volume_convexHull.c 3 : ENNReal) with hccdef
  have hcancel : ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal)
      * ((((C : ENNReal) ^ 3)⁻¹ * cc) * ((a' : ENNReal) * (b : ENNReal)))
      = 8 * ((K : ENNReal) * ((a' : ENNReal) * (b : ENNReal))) := by
    rw [hcoe, show 8 * (C : ENNReal) ^ 3 * cc⁻¹ * (K : ENNReal)
          * ((((C : ENNReal) ^ 3)⁻¹ * cc) * ((a' : ENNReal) * (b : ENNReal)))
        = (8 * ((K : ENNReal) * ((a' : ENNReal) * (b : ENNReal))))
          * (((C : ENNReal) ^ 3 * ((C : ENNReal) ^ 3)⁻¹) * (cc⁻¹ * cc)) from by ring,
      ENNReal.mul_inv_cancel hC3ne hC3top, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top,
      mul_one, mul_one]
  have hstep : (8 : ENNReal) * ((a₂ : ENNReal) * (b₂ : ENNReal))
      ≤ 8 * ((K : ENNReal) * ((a' : ENNReal) * (b : ENNReal))) := by
    refine mul_le_mul' le_rfl ?_
    exact_mod_cast hcmp
  calc volume ((P₂.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = 8 * (a₂ : ENNReal) * (b₂ : ENNReal) * ((1 : ℝ≥0) : ENNReal) := P₂.volume_carrier
    _ = 8 * ((a₂ : ENNReal) * (b₂ : ENNReal)) := by push_cast; ring
    _ ≤ 8 * ((K : ENNReal) * ((a' : ENNReal) * (b : ENNReal))) := hstep
    _ = ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal)
          * ((((C : ENNReal) ^ 3)⁻¹ * cc) * ((a' : ENNReal) * (b : ENNReal))) := hcancel.symm
    _ ≤ ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal) * volume (W.carrier : Set _) := by
        refine mul_le_mul' le_rfl ?_
        calc (((C : ENNReal) ^ 3)⁻¹ * cc) * ((a' : ENNReal) * (b : ENNReal))
            = ((C : ENNReal) ^ 3)⁻¹ * cc * ((a' : ENNReal) * (b : ENNReal)) := by ring
          _ ≤ volume (W.carrier : Set _) := hlow


/-! ### The datum-level plank reading -/

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

omit [DecidableEq κ] in
/-- A cell hull with the dimensions of an `a' × b × 1` plank has positive volume. -/
theorem volume_cellBody_ne_zero {C a' : ℝ≥0} {part : Finset κ}
    (ha' : 0 < a') (hb0 : 0 < b)
    (hdimW : IsPlankOfDimensions C a' b (cellBody part Rt)) :
    volume ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
  have hlow := hdimW.volume_lower (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
  have hpos : ((C : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal)
      * ((a' : ENNReal) * (b : ENNReal)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
    · exact mul_ne_zero (ENNReal.coe_ne_zero.mpr ha'.ne')
        (ENNReal.coe_ne_zero.mpr hb0.ne')
  exact fun h => hpos (le_antisymm (h ▸ hlow) bot_le)

include Fz in
/-- **Clause (ii) against an arbitrary outer body, at an explicit volume cost.** -/
theorem isFrostmanIn_of_volume_le {part : Finset κ} (hpart : part ∈ Fz.parts)
    {L₀ : ENNReal} {L : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hWL : cellBody part Rt ≤ L)
    (h0 : volume ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0)
    (hvol : volume (L.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ L₀ * volume ((cellBody part Rt).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) L ((C₀ : ENNReal) * L₀) :=
  isFrostmanIn_of_le_of_volume_le (Fz.isFrostmanIn_cellBody hpart)
    (fun _ hk => Finset.le_convexHull_biUnion (fun j => (Rt j).toConvexSpaceBody) hk) hWL h0 hvol

include Fz in
/-- **`def:Factors` clause (ii) in GWZ's reading, produced from the tree's hull reading.**

If the cell hull has the dimensions of an `a' × b × 1` plank up to `C`, and `P₂` is an exact
`a₂ × b₂ × 1` plank containing it whose transverse area is at most `K` times `a' * b`, then the
coarse fibre of the cell is Frostman **in `P₂`** with constant
`C₀ * plankFrostmanLoss C * K`.

This is exactly the field `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman`, so the whole
gap between `Kakeya.GlobalPlankFactorization` and the tree's Part-(B) datum, as far as clause (ii)
is concerned, is the *tightness* hypothesis `hcmp`. -/
theorem isFrostmanIn_plank_of_isPlankOfDimensions {part : Finset κ} (hpart : part ∈ Fz.parts)
    {C a' a₂ b₂ K : ℝ≥0} {hab₂ : a₂ ≤ b₂} {hb₂1 : b₂ ≤ 1}
    (hC : 1 ≤ C) (ha' : 0 < a') (hb0 : 0 < b)
    (hdimW : IsPlankOfDimensions C a' b (cellBody part Rt))
    (P₂ : Plank a₂ b₂ hab₂ hb₂1) (hP₂ : cellBody part Rt ≤ P₂.toConvexSpaceBody)
    (hcmp : a₂ * b₂ ≤ K * (a' * b)) :
    IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) P₂.toConvexSpaceBody
      ((C₀ : ENNReal) * ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal)) :=
  Fz.isFrostmanIn_of_volume_le hpart hP₂ (volume_cellBody_ne_zero ha' hb0 hdimW)
    (volume_plank_le_mul_volume_of_isPlankOfDimensions hC hdimW P₂ hcmp)

include Fz in
/-- **The same clause against the plank that `le_plank` actually hands over**, where the tightness
hypothesis becomes the explicit comparison `a ≤ Cthin * a'` between the *declared* thin half-width
`a` of GWZ 6.6(B) and the *actual* thin thickness `a'` of the cell hull.

The datum bounds `a'` only from above by `a` (`Kakeya.GlobalPlankFactorization.ethickness_two_le`),
so `Cthin` is **not** supplied by the hypotheses of 6.6(B); it is the residual obligation, and
`Kakeya.HasPlankEnvelope` below is the way to discharge it without bounding `a / a'` at all. -/
theorem exists_isFrostmanIn_le_plank_of_thin_comparable {part : Finset κ} (hpart : part ∈ Fz.parts)
    {C a' Cthin : ℝ≥0} (hC : 1 ≤ C) (ha' : 0 < a') (hb0 : 0 < b)
    (hdimW : IsPlankOfDimensions C a' b (cellBody part Rt))
    (hthin : a ≤ Cthin * a') :
    ∃ P : Plank a b hab hb1, cellBody part Rt ≤ P.toConvexSpaceBody ∧
      IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) P.toConvexSpaceBody
        ((C₀ : ENNReal) * ((plankFrostmanLoss C * Cthin : ℝ≥0) : ENNReal)) := by
  obtain ⟨P, hP⟩ := Fz.le_plank part hpart
  refine ⟨P, hP, Fz.isFrostmanIn_plank_of_isPlankOfDimensions hpart hC ha' hb0 hdimW P hP ?_⟩
  calc a * b ≤ (Cthin * a') * b := by gcongr
    _ = Cthin * (a' * b) := by ring

end GlobalPlankFactorization

/-! ### The residual geometric obligation: a tight outer plank -/

/-- **A tight `a' × b × 1` plank envelope of a convex body.**

`W` sits inside an exact plank whose transverse area is at most `K * (a' * b)` and whose
eccentricity is at most `K` times `a' / b`.  Both clauses are written multiplicatively so that no
division is involved.

This is the *only* thing that separates the GWZ 6.6(B) datum from the coarse-fibre Frostman clause
of `Kakeya.Section6PartBFactorisation`: by
`Kakeya.GlobalPlankFactorization.isFrostmanIn_plank_of_isPlankOfDimensions`, an envelope with
constant `K` gives that clause with constant `C₀ * plankFrostmanLoss C * K`, which is
sub-polynomial as soon as `C` and `K` are.

Against the plank supplied by `Kakeya.GlobalPlankFactorization.le_plank` the best available `K` is
`a / a'`, which the datum does not bound; a tight envelope avoids that ratio entirely. -/
def HasPlankEnvelope (K a' b : ℝ≥0) (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ (a₂ b₂ : ℝ≥0) (hab₂ : a₂ ≤ b₂) (hb₂1 : b₂ ≤ 1) (P : Plank a₂ b₂ hab₂ hb₂1),
    W ≤ P.toConvexSpaceBody ∧ a₂ * b₂ ≤ K * (a' * b) ∧ a₂ * b ≤ K * (a' * b₂)

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

include Fz in
/-- **A tight plank envelope discharges the coarse-fibre Frostman clause with a constant that does
not see the scales `a`, `b` at all.**

The eccentricity clause of `Kakeya.HasPlankEnvelope` is carried along, since the Part-(B) pipeline
is then run at `(a₂, b₂)` and its conclusion has to be weakened back to `(a, b)` through
`a₂ * b ≤ K * (a' * b₂)` together with `a' ≤ a`. -/
theorem exists_isFrostmanIn_plank_envelope {part : Finset κ} (hpart : part ∈ Fz.parts)
    {C a' K : ℝ≥0} (hC : 1 ≤ C) (ha' : 0 < a') (hb0 : 0 < b)
    (hdimW : IsPlankOfDimensions C a' b (cellBody part Rt))
    (henv : HasPlankEnvelope K a' b (cellBody part Rt)) :
    ∃ (a₂ b₂ : ℝ≥0) (hab₂ : a₂ ≤ b₂) (hb₂1 : b₂ ≤ 1) (P : Plank a₂ b₂ hab₂ hb₂1),
      cellBody part Rt ≤ P.toConvexSpaceBody ∧ a₂ * b ≤ K * (a' * b₂) ∧
        IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) P.toConvexSpaceBody
          ((C₀ : ENNReal) * ((plankFrostmanLoss C * K : ℝ≥0) : ENNReal)) := by
  obtain ⟨a₂, b₂, hab₂, hb₂1, P, hWP, hcmp, hecc⟩ := henv
  exact ⟨a₂, b₂, hab₂, hb₂1, P, hWP, hecc,
    Fz.isFrostmanIn_plank_of_isPlankOfDimensions hpart hC ha' hb0 hdimW P hWP hcmp⟩

end GlobalPlankFactorization


/-! ### Constructing a tight plank envelope

A body whose *longest* thickness — the circumradius `Metric.thickness ℝ W 0` — is at most `1` has a
tight envelope on the nose: the exact prism `Kakeya.outerPrism W`, whose half-widths are the three
thicknesses of `W`, becomes an `a₂ × b₂ × 1` plank after the long half-width is relaxed from
`thickness ℝ W 0` up to `1`.

`Metric.thickness ℝ W 0 ≤ 1` is **not** a consequence of the GWZ 6.6(B) datum: `le_plank` gives only
`thickness ℝ W 0 ≤ a + b + 1`, and a body genuinely spanning a diagonal of its `a × b × 1` plank has
circumradius up to `√(a² + b² + 1) > 1`. This
section discharges the case that does not need one. -/

/-- The `k`-th thickness of a convex body, as a nonnegative real. -/
def thicknessNN (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (k : ℕ) : ℝ≥0 :=
  ⟨Metric.thickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k,
    Metric.thickness_nonneg _ _⟩

theorem coe_thicknessNN (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :
    ((thicknessNN W k : ℝ≥0) : ENNReal)
      = Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k := by
  rw [Metric.ethickness_thickness' W.isCompact'.isBounded k, thicknessNN,
    ENNReal.ofReal_eq_coe_nnreal (Metric.thickness_nonneg _ _)]
  rfl

theorem thicknessNN_le_of_ethickness_le {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {k : ℕ}
    {rr : ℝ≥0}
    (h : Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k ≤ (rr : ENNReal)) :
    thicknessNN W k ≤ rr := by
  rw [← ENNReal.coe_le_coe, coe_thicknessNN]
  exact h

theorem le_thicknessNN_of_le_ethickness {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {k : ℕ}
    {rr : ℝ≥0}
    (h : (rr : ENNReal) ≤ Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) k) :
    rr ≤ thicknessNN W k := by
  rw [← ENNReal.coe_le_coe, coe_thicknessNN]
  exact h

theorem thicknessNN_antitone (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {m n : ℕ}
    (h : m ≤ n) : thicknessNN W n ≤ thicknessNN W m :=
  Metric.thickness_antitone W.isCompact'.isBounded h

/-- The exact outer prism of a convex body of `ℝ³`: the box whose half-widths are the three
thicknesses of the body (`Kakeya.outerPrism`). -/
def rawPrism (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  outerPrism (by simp) W.isCompact' W.nonempty'

/-- The exact `τ₂ × τ₁ × 1` plank spanned by the frame of `Kakeya.rawPrism`. -/
def thicknessPlank (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (h21 : thicknessNN W 2 ≤ thicknessNN W 1) (h11 : thicknessNN W 1 ≤ 1) :
    Plank (thicknessNN W 2) (thicknessNN W 1) h21 h11 where
  toPrismNDim := PrismNDim.mk' (rawPrism W).center
    ((rawPrism W).basis.reindex Fin.revPerm)
    ![thicknessNN W 2, thicknessNN W 1, 1]
  thicknesses_eq := by
    simpa using PrismNDim.thicknesses_mk' (rawPrism W).center
      ((rawPrism W).basis.reindex Fin.revPerm)
      ![thicknessNN W 2, thicknessNN W 1, 1]

/-- **A body of circumradius at most `1` lies in its own thickness plank.** -/
theorem le_thicknessPlank {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (h21 : thicknessNN W 2 ≤ thicknessNN W 1) (h11 : thicknessNN W 1 ≤ 1)
    (hzero : thicknessNN W 0 ≤ 1) :
    W ≤ (thicknessPlank W h21 h11).toConvexSpaceBody := by
  have hself : (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (rawPrism W).carrier :=
    outerPrism.self_subset (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
      W.isCompact' W.nonempty'
  refine hself.trans ?_
  intro x hx
  change x ∈ (thicknessPlank W h21 h11).carrier
  rw [(thicknessPlank W h21 h11).mem_carrier_iff]
  intro i
  have hraw := ((rawPrism W).mem_carrier_iff x).mp hx (Fin.revPerm.symm i)
  change
    |((rawPrism W).basis.reindex Fin.revPerm).repr (x - (rawPrism W).center) i| ≤
      (![thicknessNN W 2, thicknessNN W 1, 1] : Fin 3 → NNReal) i
  rw [OrthonormalBasis.repr_reindex]
  fin_cases i <;> simp [rawPrism, outerPrism.thicknesses_eq] at hraw ⊢
  · exact hraw
  · exact hraw
  · exact le_trans hraw hzero

/-- **The tight plank envelope, in the case where the body's circumradius is at most `1`.**

Every clause of `Kakeya.HasPlankEnvelope` holds at `K = C ^ 2`:
the envelope's half-widths are the actual thicknesses `τ₂ ≤ C a'` and `τ₁ ≤ C b` of the body, and
its eccentricity clause uses the lower half `b ≤ C τ₁` of `Kakeya.IsPlankOfDimensions`. -/
theorem hasPlankEnvelope_of_thicknessNN_zero_le_one {C a' b : ℝ≥0} (hC : 1 ≤ C)
    {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hdimW : IsPlankOfDimensions C a' b W) (hzero : thicknessNN W 0 ≤ 1) :
    HasPlankEnvelope (C ^ 2) a' b W := by
  have h21 : thicknessNN W 2 ≤ thicknessNN W 1 := thicknessNN_antitone W (by norm_num)
  have h11 : thicknessNN W 1 ≤ 1 := le_trans (thicknessNN_antitone W (by norm_num)) hzero
  have ha2 : thicknessNN W 2 ≤ C * a' := by
    refine thicknessNN_le_of_ethickness_le ?_
    rw [ENNReal.coe_mul]
    exact hdimW.2.2.2
  have hb2 : thicknessNN W 1 ≤ C * b := by
    refine thicknessNN_le_of_ethickness_le ?_
    rw [ENNReal.coe_mul]
    exact hdimW.2.1.2
  have hb2lo : b ≤ C * thicknessNN W 1 := by
    have hC0 : (C : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hC).ne'
    have hlow : (C : ENNReal)⁻¹ * (b : ENNReal)
        ≤ Metric.ethickness ℝ (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) 1 := hdimW.2.1.1
    have : (b : ENNReal) ≤ (C : ENNReal) * ((thicknessNN W 1 : ℝ≥0) : ENNReal) := by
      rw [coe_thicknessNN]
      calc (b : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (b : ENNReal)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 ENNReal.coe_ne_top, one_mul]
        _ ≤ (C : ENNReal) * Metric.ethickness ℝ (W.carrier : Set _) 1 := by
            exact mul_le_mul' le_rfl hlow
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
    exact this
  refine ⟨thicknessNN W 2, thicknessNN W 1, h21, h11, thicknessPlank W h21 h11,
    le_thicknessPlank h21 h11 hzero, ?_, ?_⟩
  · calc thicknessNN W 2 * thicknessNN W 1 ≤ (C * a') * (C * b) := mul_le_mul' ha2 hb2
      _ = C ^ 2 * (a' * b) := by ring
  · calc thicknessNN W 2 * b ≤ (C * a') * b := mul_le_mul' ha2 le_rfl
      _ ≤ (C * a') * (C * thicknessNN W 1) := mul_le_mul' le_rfl hb2lo
      _ = C ^ 2 * (a' * thicknessNN W 1) := by ring



/-! ### The circumradius side condition is checkable, and satisfied by tube blocks -/

/-- A body inside a ball of radius `R` has circumradius at most `R`.  This is the form in which
the side condition `hcirc` of
`Kakeya.GlobalPlankFactorization.exists_coarseFibreFrostman` is checked. -/
theorem thicknessNN_zero_le_of_subset_closedBall {W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {c : EuclideanSpace ℝ (Fin 3)} {R : ℝ≥0}
    (h : (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.closedBall c (R : ℝ)) :
    thicknessNN W 0 ≤ R :=
  Metric.thickness_le_of_subset_closedBall h R.coe_nonneg 0

/-- **The side condition is non-vacuous.**  A cell collecting a single coarse `ρ`-tube has
circumradius at most `1 / 2 + ρ`, because the core of a tube is a *unit* segment
(`Kakeya.Tube.ethickness_zero_le_half_add`).  So every singleton cell of a
`Kakeya.GlobalPlankFactorization` at a scale `ρ ≤ 1 / 2` satisfies it. -/
theorem thicknessNN_zero_cellBody_singleton_le {κ : Type*} [DecidableEq κ] {ρ : ℝ≥0}
    (Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (k : κ) :
    thicknessNN (GlobalPlankFactorization.cellBody {k} Rt) 0 ≤ 1 / 2 + ρ := by
  refine thicknessNN_le_of_ethickness_le ?_
  rw [show GlobalPlankFactorization.cellBody ({k} : Finset κ) Rt = (Rt k).toConvexSpaceBody from
    Finset.convexHull_biUnion_singleton (fun j => (Rt j).toConvexSpaceBody) k]
  exact Tube.ethickness_zero_le_half_add (Rt k)

/-! ### The headline: the Part-(B) coarse-fibre Frostman clause, from the 6.6(B) datum -/

namespace GlobalPlankFactorization

variable {κ : Type*} [DecidableEq κ] {Cw a b ρ C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {r : Finset κ} {Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}

variable (Fz : GlobalPlankFactorization Cw a b hab hb1 r
  (fun k => (Rt k).toConvexSpaceBody) C₀)

/-- The Frostman constant of the plank reading of a `Kakeya.GlobalPlankFactorization`: a fixed
polynomial in the datum's own constants `Cw` and `C₀`, with no dependence on the scales
`δ, ρ, a, b`.  With `Cw ≤ δ ^ (-η)` and `C₀ ≤ δ ^ (-η)` — the budget GWZ 6.6(B) already spends — it
is `≤ 48 · 3⁵ · δ ^ (-5 η)`, hence sub-polynomial. -/
def coarseFibreFrostmanConst (Cw C₀ : ℝ≥0) : ℝ≥0 :=
  C₀ * (plankFrostmanLoss (plankReadingConst Cw C₀) * plankReadingConst Cw C₀ ^ 2)

include Fz in
/-- **The coarse-fibre Frostman clause of `Kakeya.Section6PartBFactorisation`, produced from the
GWZ 6.6(B) datum.**

For a *single* thin half-width `a'` with `ρ ≤ a' ≤ a`, every cell of the factorisation has an exact
outer plank `P` of half-widths `(a₂, b₂, 1)` such that

* the cell hull lies in `P`;
* `P` is *tight*: its eccentricity satisfies `a₂ * b ≤ K² * (a' * b₂)` with
  `K = Kakeya.plankReadingConst Cw C₀`, so `a₂ / b₂ ≲ a' / b ≤ a / b` and the conclusion of
  6.6(B) run at `(a₂, b₂)` weakens back to the conclusion at `(a, b)`;
* the coarse fibre of the cell is **Frostman in `P`** with the constant
  `Kakeya.GlobalPlankFactorization.coarseFibreFrostmanConst Cw C₀`, which depends on nothing but
  `Cw` and `C₀`.

That is exactly `Kakeya.Section6PartBFactorisation.coarse_fibre_frostman` — clause (ii) of
`def:Factors` in GWZ's own reading, against the plank — and it is obtained here from the tree's hull
reading with **no** appeal to the unbounded ratio `a / a'`.

The one side condition is `hcirc`: each cell hull has circumradius at most `1`.  The datum gives
only `Metric.thickness ℝ W 0 ≤ a + b + 1` (`Kakeya.GlobalPlankFactorization.ethickness_zero_le`),
so `hcirc` is a genuine extra hypothesis; it is what a tight envelope costs when it is produced from
`Kakeya.outerPrism` rather than by a rotation. -/
theorem exists_coarseFibreFrostman (hb0 : 0 < b) (hρ : 0 < ρ) (hne : Fz.parts.Nonempty)
    (hcirc : ∀ part ∈ Fz.parts, thicknessNN (cellBody part Rt) 0 ≤ 1) :
    ∃ a' : ℝ≥0, ρ ≤ a' ∧ a' ≤ a ∧
      ∀ part ∈ Fz.parts, ∃ (a₂ b₂ : ℝ≥0) (hab₂ : a₂ ≤ b₂) (hb₂1 : b₂ ≤ 1)
        (P : Plank a₂ b₂ hab₂ hb₂1),
        cellBody part Rt ≤ P.toConvexSpaceBody ∧
          a₂ * b ≤ plankReadingConst Cw C₀ ^ 2 * (a' * b₂) ∧
          IsFrostmanIn part (fun k => (Rt k).toConvexSpaceBody) P.toConvexSpaceBody
            ((coarseFibreFrostmanConst Cw C₀ : ℝ≥0) : ENNReal) := by
  obtain ⟨a', hρa', ha'a, hfam⟩ :=
    Fz.exists_isPlankFamilyOfDimensions Fz.one_le_Cw hb1 hne
  have ha'0 : 0 < a' := lt_of_lt_of_le hρ hρa'
  have hK1 : (1 : ℝ≥0) ≤ plankReadingConst Cw C₀ := one_le_plankReadingConst Cw C₀
  refine ⟨a', hρa', ha'a, ?_⟩
  intro part hpart
  obtain ⟨a₂, b₂, hab₂, hb₂1, P, hWP, hecc, hFr⟩ :=
    Fz.exists_isFrostmanIn_plank_envelope hpart hK1 ha'0 hb0 (hfam part hpart)
      (hasPlankEnvelope_of_thicknessNN_zero_le_one hK1 (hfam part hpart) (hcirc part hpart))
  refine ⟨a₂, b₂, hab₂, hb₂1, P, hWP, hecc, ?_⟩
  simpa only [coarseFibreFrostmanConst, ENNReal.coe_mul, mul_assoc] using hFr

end GlobalPlankFactorization

end Kakeya

end

end
