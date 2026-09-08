/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factorization
public import Kakeya.Factoring.CoreLossEnvelope
public import Kakeya.Factoring.SelectScale
public import Kakeya.DimensionThree.IsometryTransport
public import Kakeya.DimensionThree.Plank.ComparableEnvelope
public import Kakeya.DimensionThree.Plank.DilatedParentCount
public import Kakeya.DimensionThree.Plank.EDWeightedExtraction
public import Kakeya.DimensionThree.Plank.EDParentCount
public import Kakeya.DimensionThree.Plank.FlatPrismInnerEstimate
public import Kakeya.DimensionThree.Plank.FrostmanPlankAuxScale
public import Kakeya.DimensionThree.Plank.PlankFactorizationEstimate
public import Kakeya.DimensionThree.Plank.ThickenedGeometry
public import Kakeya.DimensionThree.Plank.TubeEnclosure
public import Kakeya.PartialEstimates
public import Kakeya.ShadedUniform
public import Kakeya.Uniform

/-!
# Factoring through flat prisms

This file records GWZ Proposition 6.6(A) in the form that Section 8 of the adapted blueprint
consumes: the multiplicity bound for a family of `σ`-tubes that factors, over every tube of a
coarse family at some scale `ρ`, through a family of `a × b × 1` planks.

* `Kakeya.IsPlankOfDimensions` and `Kakeya.IsPlankFamilyOfDimensions` are the vocabulary of
  "a convex body has the dimensions of an `a × b × 1` plank, up to a factor `C`" (blueprint
  `def:plank`, whose affine thicknesses are only asserted up to constants).
* `Kakeya.IsFlatPrismUniform` (and its tube-level `Kakeya.IsFlatPrismUniformTubeSet`) is the
  one-sided half of GWZ Definition 2.2 — the clauses that survive passing to a subfamily.  It is
  a **deliberate duplicate** of `Kakeya.ml1Boot.IsOneSidedUniform`, which cannot be imported here
  because it lives in Section 8; see the section docstring below.
* `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` is blueprint
  `prop:ml1bootFlatPrismsCorrected`: GWZ Proposition 6.6(A) with the scale ordering written as
  `σ ≤ a ≤ b ≤ ρ ≤ 1`, the plank scales sitting *below* the coarse scale.  It is the **only**
  Lean record of that proposition and is proved below;
  the former second copy in `Kakeya/DimensionThree/Plank/Factorization.lean`, which asserted the
  same bound in the opposite regime `ρ ≤ a`, has been removed.  [GWZ] imposes no ordering
  between `ρ` and `a, b`, so the form below is a restriction of the proposition; see blueprint
  `note:ml1bootFlatPrismScales`.

## Divergence from the informal statement

The blueprint says "a family of `a × b × 1` planks factors `𝕍[V_{ρ,m}]`".  Three readings have
to be pinned down in Lean.

* *Factors* is `ConvexSpaceBody.Factorization` (blueprint `def:Factors`) with constant `2`,
  which is the constant that `lemmafactmax` produces and that
  `Kakeya.ml1Boot.exists_plankDimensions` supplies.
* *`a × b × 1` plank* is `Kakeya.IsPlankOfDimensions Cw a b`, i.e. the three affine
  thicknesses are comparable to `1`, `b`, `a` with a constant `Cw ≥ 1`.  The comparability
  constant is a parameter, quantified before the fullness threshold `η'`, because the planks
  produced by `Kakeya.ml1Boot.exists_plankDimensions` have their dimensions only up to the
  constant `Kakeya.ml1Boot.plankPigeonhole.C`.
* *`𝕍[V_{ρ,m}]`* is the **parent-map fibre** `s[m] = {i ∈ s : p i = m}` of blueprint
  `def:ml1bootParentFamily`, written here as `s.filter fun i => p i = m` — the same index set
  as `Kakeya.ml1Boot.fibre s p m`, which cannot be named in this file because it lives in
  Section 8.  It is *not* the containment fibre `𝕍⟨V_{ρ,m}⟩ = {i ∈ s : V i ≤ V_{ρ,m}}`, i.e.
  not `Kakeya.familyIn s _ (Vρ m).toConvexSpaceBody`: the containment fibres overlap and each
  properly contains the corresponding parent-map fibre, so a factorization hypothesis over the
  containment fibres would be strictly stronger than what the plank pigeonhole produces.
  Reading it as the parent-map fibre is what makes the hypothesis match the producer
  `Kakeya.ml1Boot.exists_plankDimensions` and the consumer
  `Kakeya.ml1Boot.flatPrism_dichotomy`, both of which use `Kakeya.ml1Boot.fibre _ pρ m`.

The coarse family is given as a bare map `p : ι → κ` into an index set `t` of `ρ`-tubes with
`V i ≤ V_{ρ,p i}`, rather than through `Kakeya.ml1Boot.IsParentFamily`, so that this file does
not depend on Section 8.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

section Planks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A convex body with the dimensions of an `a × b × 1` plank** (blueprint `def:plank`).

In `ℝ³` an `a × b × 1` plank has affine thicknesses `τ₀ ∼ 1`, `τ₁ ∼ b`, `τ₂ ∼ a`; the
blueprint definition asserts the first two only up to constants, so the predicate carries an
explicit comparability constant `C ≥ 1` and asserts all three two-sidedly.  Here
`τₖ(W) = Metric.ethickness ℝ W.carrier k`, which is *decreasing* in `k`, matching
`τ₀ ≥ τ₁ ≥ τ₂` for `a ≤ b ≤ 1`. -/
def IsPlankOfDimensions (C a b : NNReal) (W : ConvexSpaceBody E) : Prop :=
  ((C : ENNReal)⁻¹ ≤ Metric.ethickness ℝ W.carrier 0 ∧
      Metric.ethickness ℝ W.carrier 0 ≤ (C : ENNReal)) ∧
    ((C : ENNReal)⁻¹ * (b : ENNReal) ≤ Metric.ethickness ℝ W.carrier 1 ∧
      Metric.ethickness ℝ W.carrier 1 ≤ (C : ENNReal) * (b : ENNReal)) ∧
    ((C : ENNReal)⁻¹ * (a : ENNReal) ≤ Metric.ethickness ℝ W.carrier 2 ∧
      Metric.ethickness ℝ W.carrier 2 ≤ (C : ENNReal) * (a : ENNReal))

/-- **A family of `a × b × 1` planks**: every member of the family has the dimensions of an
`a × b × 1` plank, with the *same* `a` and `b` and the same comparability constant `C`. -/
def IsPlankFamilyOfDimensions {ι : Type*} (C a b : NNReal) (s : Finset ι)
    (W : ι → ConvexSpaceBody E) : Prop :=
  ∀ i ∈ s, IsPlankOfDimensions C a b (W i)

end Planks

section FlatPrisms

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Two shaded bodies are equal when their ambient convex bodies and their shadings agree. -/
theorem ShadedBody.ext_of_toConvexSpaceBody_eq {A B : ShadedBody E}
    (hbody : A.toConvexSpaceBody = B.toConvexSpaceBody) (hshade : A.shade = B.shade) :
    A = B := by
  cases A
  cases B
  simp_all

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Plank-dimension comparability is invariant under a linear isometry. -/
theorem IsPlankOfDimensions.mapLinearIsometryEquiv
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C a b : NNReal} {W : ConvexSpaceBody E}
    (hW : IsPlankOfDimensions C a b W) (f : E ≃ₗᵢ[ℝ] F) :
    IsPlankOfDimensions C a b (W.mapLinearIsometryEquiv f) := by
  rw [IsPlankOfDimensions] at hW ⊢
  change
    ((C : ENNReal)⁻¹ ≤ Metric.ethickness ℝ (f '' W.carrier) 0 ∧
        Metric.ethickness ℝ (f '' W.carrier) 0 ≤ (C : ENNReal)) ∧
      ((C : ENNReal)⁻¹ * (b : ENNReal) ≤ Metric.ethickness ℝ (f '' W.carrier) 1 ∧
        Metric.ethickness ℝ (f '' W.carrier) 1 ≤ (C : ENNReal) * (b : ENNReal)) ∧
      ((C : ENNReal)⁻¹ * (a : ENNReal) ≤ Metric.ethickness ℝ (f '' W.carrier) 2 ∧
        Metric.ethickness ℝ (f '' W.carrier) 2 ≤ (C : ENNReal) * (a : ENNReal))
  simpa only [Metric.ethickness_image_linearIsometryEquiv] using hW

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Enlarging the comparison constant weakens the three plank-dimension brackets. -/
theorem IsPlankOfDimensions.mono_constant {C C' a b : NNReal}
    {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W)
    (hCC' : C ≤ C') : IsPlankOfDimensions C' a b W := by
  have hcoe : (C : ENNReal) ≤ (C' : ENNReal) := by exact_mod_cast hCC'
  have hinv : (C' : ENNReal)⁻¹ ≤ (C : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr hcoe
  rcases hW with ⟨⟨h0lo, h0hi⟩, ⟨⟨h1lo, h1hi⟩, ⟨h2lo, h2hi⟩⟩⟩
  exact ⟨⟨hinv.trans h0lo, h0hi.trans hcoe⟩,
    ⟨⟨(mul_le_mul_left hinv _).trans h1lo,
      h1hi.trans (mul_le_mul_left hcoe _)⟩,
      ⟨(mul_le_mul_left hinv _).trans h2lo,
        h2hi.trans (mul_le_mul_left hcoe _)⟩⟩⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- Thickening a plank-like convex body by at most its shortest scale preserves all three
dimension brackets, at the cost of doubling the comparison constant. -/
theorem IsPlankOfDimensions.cthickening {C a b : NNReal} {W : ConvexSpaceBody E}
    [Nontrivial E] (hW : IsPlankOfDimensions C a b W) (r : NNReal) (hr : (r : ℝ) ≤ W.scale) :
    IsPlankOfDimensions (2 * C) a b (W.cthickening r) := by
  have hmono : ∀ k : ℕ, Metric.ethickness ℝ W.carrier k ≤
      Metric.ethickness ℝ (W.cthickening r).carrier k :=
    fun k ↦ Metric.ethickness_monotone (ConvexSpaceBody.self_le_cthickening W r) k
  have hupper := ConvexSpaceBody.ethickness_cthickening_le_two W r hr
  have hupper' : ∀ k : ℕ, Metric.ethickness ℝ (W.cthickening r).carrier k ≤
      2 * Metric.ethickness ℝ W.carrier k := by
    intro k
    simpa [Pi.smul_apply, two_nsmul, two_mul] using hupper k
  have hC : (C : ENNReal) ≤ (2 * C : NNReal) := by
    have hCnn : C ≤ 2 * C := by rw [two_mul]; exact le_self_add
    exact_mod_cast hCnn
  have hinv : ((2 * C : NNReal) : ENNReal)⁻¹ ≤ (C : ENNReal)⁻¹ :=
    ENNReal.inv_le_inv.mpr hC
  rcases hW with ⟨⟨h0lo, h0hi⟩, ⟨⟨h1lo, h1hi⟩, ⟨h2lo, h2hi⟩⟩⟩
  refine ⟨⟨hinv.trans h0lo |>.trans (hmono 0), ?_⟩, ?_, ?_⟩
  · calc
      Metric.ethickness ℝ (W.cthickening r).carrier 0
          ≤ 2 * Metric.ethickness ℝ W.carrier 0 := hupper' 0
      _ ≤ 2 * (C : ENNReal) := by gcongr
      _ = ((2 * C : NNReal) : ENNReal) := by norm_num [ENNReal.coe_mul]
  · refine ⟨?_, ?_⟩
    · calc
        ((2 * C : NNReal) : ENNReal)⁻¹ * (b : ENNReal)
            ≤ (C : ENNReal)⁻¹ * (b : ENNReal) := by gcongr
        _ ≤ Metric.ethickness ℝ W.carrier 1 := h1lo
        _ ≤ Metric.ethickness ℝ (W.cthickening r).carrier 1 := hmono 1
    · calc
        Metric.ethickness ℝ (W.cthickening r).carrier 1
            ≤ 2 * Metric.ethickness ℝ W.carrier 1 := hupper' 1
        _ ≤ 2 * ((C : ENNReal) * (b : ENNReal)) := by gcongr
        _ = ((2 * C : NNReal) : ENNReal) * (b : ENNReal) := by
          norm_num [ENNReal.coe_mul]
          ring
  · refine ⟨?_, ?_⟩
    · calc
        ((2 * C : NNReal) : ENNReal)⁻¹ * (a : ENNReal)
            ≤ (C : ENNReal)⁻¹ * (a : ENNReal) := by gcongr
        _ ≤ Metric.ethickness ℝ W.carrier 2 := h2lo
        _ ≤ Metric.ethickness ℝ (W.cthickening r).carrier 2 := hmono 2
    · calc
        Metric.ethickness ℝ (W.cthickening r).carrier 2
            ≤ 2 * Metric.ethickness ℝ W.carrier 2 := hupper' 2
        _ ≤ 2 * ((C : ENNReal) * (a : ENNReal)) := by gcongr
        _ = ((2 * C : NNReal) : ENNReal) * (a : ENNReal) := by
          norm_num [ENNReal.coe_mul]
          ring

/-- A three-dimensional body with `a × b × 1` plank dimensions has volume bounded below by
the product of its three lower ethickness bounds.  The dimensional coefficient is the existing
convex-hull volume constant `Metric.lt_volume_convexHull.c 3`; no new comparison constant is
introduced here. -/
theorem IsPlankOfDimensions.volume_lower (hdim : Module.finrank ℝ E = 3)
    {C a b : NNReal} {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W) :
    ((C : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
        ((a : ENNReal) * (b : ENNReal)) ≤ volume W.carrier := by
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨⟨h0, _⟩, ⟨⟨h1, _⟩, ⟨h2, _⟩⟩⟩ := hW
  have hprod : ∏ i ∈ Finset.range (Module.finrank ℝ E),
      Metric.ethickness ℝ W.carrier i =
        Metric.ethickness ℝ W.carrier 0 * Metric.ethickness ℝ W.carrier 1 *
          Metric.ethickness ℝ W.carrier 2 := by
    rw [hdim]
    simp [Finset.prod_range_succ]
  calc
    ((C : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((a : ENNReal) * (b : ENNReal)) =
        (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((C : ENNReal)⁻¹ * ((C : ENNReal)⁻¹ * (b : ENNReal)) *
            ((C : ENNReal)⁻¹ * (a : ENNReal))) := by
      rw [ENNReal.inv_pow]
      ring
    _ ≤ (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          (Metric.ethickness ℝ W.carrier 0 * Metric.ethickness ℝ W.carrier 1 *
            Metric.ethickness ℝ W.carrier 2) := by
      gcongr
    _ = (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), Metric.ethickness ℝ W.carrier i := by
      rw [hprod]
    _ = (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), Metric.ethickness ℝ W.carrier i := by
      rw [hdim]
    _ ≤ volume W.carrier := W.convex'.convex.ethickness_prod_le_volume

/-- A three-dimensional body with `a × b × 1` plank dimensions has volume bounded above by
the product of its three upper ethickness bounds.  The factor `8 = 2 ^ 3` is the dimensional
constant in `volume_le_prod_ethickness`. -/
theorem IsPlankOfDimensions.volume_upper (hdim : Module.finrank ℝ E = 3)
    {C a b : NNReal} {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W) :
    volume W.carrier ≤ 8 * (C : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal)) := by
  obtain ⟨⟨_, h0⟩, ⟨⟨_, h1⟩, ⟨_, h2⟩⟩⟩ := hW
  have hprod : ∏ i ∈ Finset.range (Module.finrank ℝ E),
      Metric.ethickness ℝ W.carrier i =
        Metric.ethickness ℝ W.carrier 0 * Metric.ethickness ℝ W.carrier 1 *
          Metric.ethickness ℝ W.carrier 2 := by
    rw [hdim]
    simp [Finset.prod_range_succ]
  calc
    volume W.carrier ≤ 2 ^ (Module.finrank ℝ E) *
        ∏ i ∈ Finset.range (Module.finrank ℝ E), Metric.ethickness ℝ W.carrier i :=
      volume_le_prod_ethickness _
    _ = 8 * (Metric.ethickness ℝ W.carrier 0 * Metric.ethickness ℝ W.carrier 1 *
          Metric.ethickness ℝ W.carrier 2) := by
      rw [hprod, hdim]
      norm_num
    _ ≤ 8 * ((C : ENNReal) * ((C : ENNReal) * (b : ENNReal)) *
          ((C : ENNReal) * (a : ENNReal))) := by
      gcongr
    _ = 8 * (C : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal)) := by
      ring

/-- The fixed volume-comparison constant for two bodies with the same comparable plank
dimensions. -/
noncomputable def flatPrismBodyVolumeRatio.C (Cw : NNReal) : NNReal :=
  max 1 (8 * Cw ^ 6 * (Metric.lt_volume_convexHull.c 3)⁻¹)

theorem flatPrismBodyVolumeRatio.one_le (Cw : NNReal) :
    1 ≤ flatPrismBodyVolumeRatio.C Cw := le_max_left _ _

/-- Fixed volume loss between the shrunken scale collar and its exact plank envelope. -/
noncomputable def flatPrismEnvelopeVolumeRatio.C (Cw : NNReal) : NNReal :=
  max 1 (8 * ((comparablePlankEnvelope.shrink Cw) ^ 3)⁻¹ * Cw ^ 3 *
    (Metric.lt_volume_convexHull.c 3)⁻¹)

theorem flatPrismEnvelopeVolumeRatio.one_le (Cw : NNReal) :
    1 ≤ flatPrismEnvelopeVolumeRatio.C Cw := le_max_left _ _

/-- Constant in the within-parent dilated-plank count after the common envelope homothety. -/
noncomputable def flatPrismOuterSplit.C (Cw C_NC : NNReal) : NNReal :=
  max 1 (16 * C_NC ^ 3 * (comparablePlankEnvelope.shrink Cw)⁻¹ ^ 3 * Cw ^ 3 *
    (Metric.lt_volume_convexHull.c 3)⁻¹)

theorem flatPrismOuterSplit.one_le (Cw C_NC : NNReal) :
    1 ≤ flatPrismOuterSplit.C Cw C_NC := le_max_left _ _

/-- Katz--Tao inside one parent bounds the number of comparable actual bodies whose common
homothetic envelope lies in a dilated thick-plank test body. -/
theorem card_le_of_isKatzTao_scaledComparableBodies
    {κ' : Type*} {a b Cw : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (hCw : 1 ≤ Cw) (ha : 0 < a) (hb : 0 < b) (fibre : Finset κ')
    (K : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hKT : IsKatzTao fibre K 2)
    (hdim : ∀ x ∈ fibre, IsPlankOfDimensions Cw a b (K x))
    (C_NC : NNReal) (Ptest : ShadedPlank a b hab hb1)
    {θ : NNReal} (hθ1 : θ ≤ 1) :
    (((fibre.filter fun x ↦
        ((K x).homothety 0 (comparablePlankEnvelope.shrink Cw : ℝ)) ≤
          ((Plank.thickened Ptest.toPrism3D θ hθ1).toPrismNDim.dilation
            C_NC).toConvexSpaceBody).card :
        NNReal)) ≤ flatPrismOuterSplit.C Cw C_NC * (b / a) * θ := by
  classical
  let r : NNReal := comparablePlankEnvelope.shrink Cw
  let test : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ((Plank.thickened Ptest.toPrism3D θ hθ1).toPrismNDim.dilation C_NC).toConvexSpaceBody
  let selected := fibre.filter fun x ↦ (K x).homothety 0 (r : ℝ) ≤ test
  have hr : 0 < r := comparablePlankEnvelope.shrink_pos hCw
  have hKT' : IsKatzTao fibre (fun x ↦ (K x).homothety 0 (r : ℝ)) 2 :=
    hKT.homothety 0 (by exact_mod_cast hr.ne')
  let vmin : NNReal := r ^ 3 * Cw⁻¹ ^ 3 * Metric.lt_volume_convexHull.c 3 * (a * b)
  have hvol : ∀ x ∈ selected, (vmin : ENNReal) ≤
      volume ((K x).homothety 0 (r : ℝ)).carrier := by
    intro x hx
    have hxF : x ∈ fibre := Finset.mem_filter.mp hx |>.1
    have hlower := (hdim x hxF).volume_lower (by simp)
    rw [ConvexSpaceBody.volume_homothety]
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp,
      abs_of_pos (pow_pos hrR 3), ENNReal.ofReal_pow hrR.le,
      ENNReal.ofReal_coe_nnreal]
    dsimp only [vmin]
    simp only [ENNReal.coe_mul, ENNReal.coe_pow]
    rw [ENNReal.coe_inv (zero_lt_one.trans_le hCw).ne']
    calc
      (r : ENNReal) ^ 3 * (Cw : ENNReal)⁻¹ ^ 3 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal) *
            ((a : ENNReal) * (b : ENNReal)) =
          (r : ENNReal) ^ 3 * (((Cw : ENNReal) ^ 3)⁻¹ *
            (Metric.lt_volume_convexHull.c 3 : ENNReal) *
            ((a : ENNReal) * (b : ENNReal))) := by rw [ENNReal.inv_pow]; ring
      _ ≤ (r : ENNReal) ^ 3 * volume (K x).carrier :=
        mul_le_mul_of_nonneg_left hlower (show (0 : ENNReal) ≤ (r : ENNReal) ^ 3 from bot_le)
  have hselSub : selected ⊆ fibre := by
    exact Finset.filter_subset _ _
  have hKTsel := hKT'.subset hselSub
  have hsub : ∀ x ∈ selected, (K x).homothety 0 (r : ℝ) ≤ test := by
    intro x hx
    exact Finset.mem_filter.mp hx |>.2
  have hcard := hKTsel.card_mul_le hsub hvol
  have htest : volume test.carrier =
      (C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b) := by
    dsimp only [test]
    rw [PrismNDim.volume_dilation, Plank.volume_thickened]
  have henn : (selected.card : ENNReal) * (vmin : ENNReal) ≤
      2 * ((C_NC : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b)) := by
    simpa only [htest] using hcard
  have hnn : (selected.card : NNReal) * vmin ≤
      2 * (C_NC ^ 3 * (8 * θ * b * b)) := by
    exact_mod_cast henn
  have hvmin : 0 < vmin := by
    dsimp only [vmin]
    positivity
  calc
    (selected.card : NNReal) ≤
        (2 * (C_NC ^ 3 * (8 * θ * b * b))) / vmin := by
      rw [le_div_iff₀ hvmin]
      exact hnn
    _ = 16 * C_NC ^ 3 * r⁻¹ ^ 3 * Cw ^ 3 *
          (Metric.lt_volume_convexHull.c 3)⁻¹ * (b / a) * θ := by
      dsimp only [vmin]
      field_simp [hr.ne', ha.ne', hb.ne', (Metric.lt_volume_convexHull.c_pos 3).ne']
      <;> ring
    _ ≤ flatPrismOuterSplit.C Cw C_NC * (b / a) * θ := by
      gcongr
      exact le_max_right _ _

/-- The exact common envelope has at most a fixed multiple of the shrunken scale-collar volume. -/
theorem IsPlankOfDimensions.volume_plank_le_mul_scaledCollar
    {Cw a b : NNReal} (hCw : 1 ≤ Cw) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hK : IsPlankOfDimensions Cw a b K) :
    volume (comparablePlankEnvelope.plank Cw a b hab hb1 K).carrier ≤
      (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
        volume (comparablePlankEnvelope.scaledCollar Cw K).carrier := by
  let r : NNReal := comparablePlankEnvelope.shrink Cw
  let vmin : ENNReal := ((Cw : ENNReal) ^ 3)⁻¹ *
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * ((a : ENNReal) * (b : ENNReal))
  have hr : 0 < r := comparablePlankEnvelope.shrink_pos hCw
  have hKlower : vmin ≤ volume K.carrier := hK.volume_lower (by simp)
  have hKcollar : volume K.carrier ≤
      volume (K.cthickening (comparablePlankEnvelope.scaleRadius K : ℝ)).carrier :=
    measure_mono (ConvexSpaceBody.self_le_cthickening K _)
  have hscaled : (r : ENNReal) ^ 3 * vmin ≤
      volume (comparablePlankEnvelope.scaledCollar Cw K).carrier := by
    rw [comparablePlankEnvelope.scaledCollar, ConvexSpaceBody.volume_homothety]
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp]
    have hof : ENNReal.ofReal |(r : ℝ) ^ 3| = (r : ENNReal) ^ 3 := by
      rw [abs_of_pos (pow_pos hrR 3), ENNReal.ofReal_pow hrR.le,
        ENNReal.ofReal_coe_nnreal]
    rw [hof]
    gcongr
    exact hKlower.trans hKcollar
  have hCw0 : (Cw : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCw)).ne'
  have hr0 : (r : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hr).ne'
  have hc0 : (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
  have hraw : volume (comparablePlankEnvelope.plank Cw a b hab hb1 K).carrier ≤
      (8 * ((r : ENNReal) ^ 3)⁻¹ * (Cw : ENNReal) ^ 3 *
        (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          volume (comparablePlankEnvelope.scaledCollar Cw K).carrier := by
    calc
      volume (comparablePlankEnvelope.plank Cw a b hab hb1 K).carrier =
          8 * ((a : ENNReal) * (b : ENNReal)) := by
        rw [Prism3D.volume_carrier]
        simp
        ring
      _ = (8 * ((r : ENNReal) ^ 3)⁻¹ * (Cw : ENNReal) ^ 3 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          ((r : ENNReal) ^ 3 * vmin) := by
        dsimp only [vmin]
        have hrpow : ((r : ENNReal) ^ 3)⁻¹ * (r : ENNReal) ^ 3 = 1 :=
          ENNReal.inv_mul_cancel (pow_ne_zero 3 hr0) (by finiteness)
        have hCwpow : (Cw : ENNReal) ^ 3 * ((Cw : ENNReal) ^ 3)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (pow_ne_zero 3 hCw0) (by finiteness)
        have hc : (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
            (Metric.lt_volume_convexHull.c 3 : ENNReal) = 1 :=
          ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top
        calc
          8 * ((a : ENNReal) * (b : ENNReal)) =
              8 * ((((r : ENNReal) ^ 3)⁻¹ * (r : ENNReal) ^ 3) *
                ((Cw : ENNReal) ^ 3 * ((Cw : ENNReal) ^ 3)⁻¹) *
                ((Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
                  (Metric.lt_volume_convexHull.c 3 : ENNReal))) *
                ((a : ENNReal) * (b : ENNReal)) := by rw [hrpow, hCwpow, hc]; simp
          _ = _ := by ring
      _ ≤ (8 * ((r : ENNReal) ^ 3)⁻¹ * (Cw : ENNReal) ^ 3 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          volume (comparablePlankEnvelope.scaledCollar Cw K).carrier := by gcongr
  exact hraw.trans (mul_le_mul_of_nonneg_right (by
    have hnn : 8 * (r ^ 3)⁻¹ * Cw ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹ ≤
        flatPrismEnvelopeVolumeRatio.C Cw := le_max_right _ _
    have hcoe := ENNReal.coe_le_coe.mpr hnn
    simp only [ENNReal.coe_mul, ENNReal.coe_pow,
      ENNReal.coe_inv (pow_ne_zero 3 hr.ne'),
      ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne'] at hcoe
    norm_num at hcoe ⊢
    exact hcoe) bot_le)

/-- The exact common envelope has at most a fixed multiple of the volume of the actual body
after the same common homothety.  This is the volume comparison used to transport outer
Frostman control to the representative planks. -/
theorem IsPlankOfDimensions.volume_plank_le_mul_scaledBody
    {Cw a b : NNReal} (hCw : 1 ≤ Cw) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hK : IsPlankOfDimensions Cw a b K) :
    volume (comparablePlankEnvelope.plank Cw a b hab hb1 K).carrier ≤
      (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
        volume (K.homothety 0 (comparablePlankEnvelope.shrink Cw : ℝ)).carrier := by
  let r : NNReal := comparablePlankEnvelope.shrink Cw
  let vmin : ENNReal := ((Cw : ENNReal) ^ 3)⁻¹ *
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * ((a : ENNReal) * (b : ENNReal))
  have hr : 0 < r := comparablePlankEnvelope.shrink_pos hCw
  have hKlower : vmin ≤ volume K.carrier := hK.volume_lower (by simp)
  have hscaled : (r : ENNReal) ^ 3 * vmin ≤
      volume (K.homothety 0 (r : ℝ)).carrier := by
    rw [ConvexSpaceBody.volume_homothety]
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by simp]
    have hof : ENNReal.ofReal |(r : ℝ) ^ 3| = (r : ENNReal) ^ 3 := by
      rw [abs_of_pos (pow_pos hrR 3), ENNReal.ofReal_pow hrR.le,
        ENNReal.ofReal_coe_nnreal]
    rw [hof]
    gcongr
  have hCw0 : (Cw : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCw)).ne'
  have hr0 : (r : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hr).ne'
  have hc0 : (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
  have hraw : volume (comparablePlankEnvelope.plank Cw a b hab hb1 K).carrier ≤
      (8 * ((r : ENNReal) ^ 3)⁻¹ * (Cw : ENNReal) ^ 3 *
        (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          volume (K.homothety 0 (r : ℝ)).carrier := by
    calc
      volume (comparablePlankEnvelope.plank Cw a b hab hb1 K).carrier =
          8 * ((a : ENNReal) * (b : ENNReal)) := by
        rw [Prism3D.volume_carrier]
        simp
        ring
      _ = (8 * ((r : ENNReal) ^ 3)⁻¹ * (Cw : ENNReal) ^ 3 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          ((r : ENNReal) ^ 3 * vmin) := by
        dsimp only [vmin]
        have hrpow : ((r : ENNReal) ^ 3)⁻¹ * (r : ENNReal) ^ 3 = 1 :=
          ENNReal.inv_mul_cancel (pow_ne_zero 3 hr0) (by finiteness)
        have hCwpow : (Cw : ENNReal) ^ 3 * ((Cw : ENNReal) ^ 3)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (pow_ne_zero 3 hCw0) (by finiteness)
        have hc : (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
            (Metric.lt_volume_convexHull.c 3 : ENNReal) = 1 :=
          ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top
        calc
          8 * ((a : ENNReal) * (b : ENNReal)) =
              8 * ((((r : ENNReal) ^ 3)⁻¹ * (r : ENNReal) ^ 3) *
                ((Cw : ENNReal) ^ 3 * ((Cw : ENNReal) ^ 3)⁻¹) *
                ((Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
                  (Metric.lt_volume_convexHull.c 3 : ENNReal))) *
                ((a : ENNReal) * (b : ENNReal)) := by rw [hrpow, hCwpow, hc]; simp
          _ = _ := by ring
      _ ≤ (8 * ((r : ENNReal) ^ 3)⁻¹ * (Cw : ENNReal) ^ 3 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          volume (K.homothety 0 (r : ℝ)).carrier := by gcongr
  exact hraw.trans (mul_le_mul_of_nonneg_right (by
    have hnn : 8 * (r ^ 3)⁻¹ * Cw ^ 3 * (Metric.lt_volume_convexHull.c 3)⁻¹ ≤
        flatPrismEnvelopeVolumeRatio.C Cw := le_max_right _ _
    have hcoe := ENNReal.coe_le_coe.mpr hnn
    simp only [ENNReal.coe_mul, ENNReal.coe_pow,
      ENNReal.coe_inv (pow_ne_zero 3 hr.ne'),
      ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne'] at hcoe
    norm_num at hcoe ⊢
    exact hcoe) bot_le)

open Classical in
/-- Katz--Tao control survives replacing each body by a larger uniformly
volume-comparable envelope. -/
theorem ConvexSpaceBody.IsKatzTao.of_envelope
    {I : Type*} {s : Finset I} {U P : I → ConvexSpaceBody E} {C A : ENNReal}
    (hKT : ConvexSpaceBody.IsKatzTao s U C)
    (hUP : ∀ i ∈ s, U i ≤ P i)
    (hvol : ∀ i ∈ s, volume (P i).carrier ≤ A * volume (U i).carrier) :
    ConvexSpaceBody.IsKatzTao s P (A * C) := by
  rw [ConvexSpaceBody.IsKatzTao_def, Kakeya.maxDensity_le_iff]
  intro K
  rw [Kakeya.densityIn_le_iff]
  calc
    ∑ i ∈ s with P i ≤ K, volume (P i).carrier ≤
        ∑ i ∈ s with P i ≤ K, A * volume (U i).carrier := by
      exact Finset.sum_le_sum fun i hi ↦ hvol i (Finset.mem_filter.mp hi).1
    _ = A * ∑ i ∈ s with P i ≤ K, volume (U i).carrier := by
      rw [Finset.mul_sum]
    _ ≤ A * ∑ i ∈ s with U i ≤ K, volume (U i).carrier := by
      gcongr with i hi
      exact hUP i hi
    _ ≤ A * (C * volume K.carrier) := by
      gcongr
      exact (ConvexSpaceBody.isKatzTao_iff s U C).mp hKT K
    _ = (A * C) * volume K.carrier := by ring

/-- Two actual factor bodies with the same `Cw`-comparable `a × b × 1` dimensions have
volumes comparable by a constant depending only on `Cw`. -/
theorem IsPlankOfDimensions.volume_le_mul_volume (hdim : Module.finrank ℝ E = 3)
    {Cw a b : NNReal} (hCw : 1 ≤ Cw) (ha : 0 < a) (hb : 0 < b)
    {K K' : ConvexSpaceBody E} (hK : IsPlankOfDimensions Cw a b K)
    (hK' : IsPlankOfDimensions Cw a b K') :
    volume K.carrier ≤
      (flatPrismBodyVolumeRatio.C Cw : ENNReal) * volume K'.carrier := by
  have hupper := hK.volume_upper hdim
  have hlower := hK'.volume_lower hdim
  have hCw0 : (Cw : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCw)).ne'
  have hc0 : (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
  have hab0 : (a : ENNReal) * (b : ENNReal) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr ha.ne') (ENNReal.coe_ne_zero.mpr hb.ne')
  have hpow : (Cw : ENNReal) ^ 6 * ((Cw : ENNReal) ^ 3)⁻¹ =
      (Cw : ENNReal) ^ 3 := by
    rw [ENNReal.inv_pow]
    calc
      (Cw : ENNReal) ^ 6 * (Cw : ENNReal)⁻¹ ^ 3 =
          (Cw : ENNReal) ^ 3 * ((Cw : ENNReal) * (Cw : ENNReal)⁻¹) ^ 3 := by ring
      _ = (Cw : ENNReal) ^ 3 := by
        rw [ENNReal.mul_inv_cancel hCw0 ENNReal.coe_ne_top]
        simp
  have hc : (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
      (Metric.lt_volume_convexHull.c 3 : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top
  have hraw : volume K.carrier ≤
      (8 * (Cw : ENNReal) ^ 6 *
        (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) * volume K'.carrier := by
    calc
      volume K.carrier ≤ 8 * (Cw : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal)) := hupper
      _ = (8 * (Cw : ENNReal) ^ 6 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
          (((Cw : ENNReal) ^ 3)⁻¹ *
            (Metric.lt_volume_convexHull.c 3 : ENNReal) *
            ((a : ENNReal) * (b : ENNReal))) := by
        calc
          8 * (Cw : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal)) =
              8 * ((Cw : ENNReal) ^ 6 * ((Cw : ENNReal) ^ 3)⁻¹) *
                ((Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
                  (Metric.lt_volume_convexHull.c 3 : ENNReal)) *
                ((a : ENNReal) * (b : ENNReal)) := by rw [hpow, hc, mul_one]
          _ = _ := by ring
      _ ≤ (8 * (Cw : ENNReal) ^ 6 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) * volume K'.carrier := by
        gcongr
  exact hraw.trans (mul_le_mul_of_nonneg_right (by
    have hnn : 8 * Cw ^ (6 : ℕ) * (Metric.lt_volume_convexHull.c 3)⁻¹ ≤
        flatPrismBodyVolumeRatio.C Cw := le_max_right _ _
    have hcoe := ENNReal.coe_le_coe.mpr hnn
    simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat,
      ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne'] using hcoe) bot_le)

/-- The fixed Frostman loss when an inner fibre is re-normalised inside the exact plank envelope
of its actual factor body.  It depends only on the plank comparison constant. -/
noncomputable def flatPrismInnerFrostman.C (Cw : NNReal) : NNReal :=
  max 1 (16 * Cw ^ 5 * (Metric.lt_volume_convexHull.c 3)⁻¹)

theorem flatPrismInnerFrostman.one_le (Cw : NNReal) :
    1 ≤ flatPrismInnerFrostman.C Cw := by
  exact le_max_left _ _

/-- A Frostman fibre inside an actual `Cw`-comparable block remains Frostman in the unscaled
exact plank envelope.  The proof records the volume-ratio loss explicitly; no scale- or
family-dependent quantity enters the resulting constant. -/
theorem IsPlankOfDimensions.frostmanIn_bodyPlank
    {Cw a b : NNReal} (hCw : 1 ≤ Cw) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hCa : Cw * a ≤ 1)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hK : IsPlankOfDimensions Cw a b K)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall)
    {I : Type*} {q : Finset I}
    {T : I → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hTK : ∀ i ∈ q, T i ≤ K)
    (hFr : IsFrostmanIn q T K 2) :
    IsFrostmanIn q T
      (comparablePlankEnvelope.bodyPlank Cw a b hab hCa K).toConvexSpaceBody
      (flatPrismInnerFrostman.C Cw : ENNReal) := by
  let W := (comparablePlankEnvelope.bodyPlank Cw a b hab hCa K).toConvexSpaceBody
  have hKW : K ≤ W := comparablePlankEnvelope.body_le_bodyPlank hab hCa
    hK.2.1.2 hK.2.2.2 hKball
  have hTW : ∀ i ∈ q, T i ≤ W := fun i hi ↦ (hTK i hi).trans hKW
  have hKlower : ((Cw : ENNReal) ^ 3)⁻¹ *
        (Metric.lt_volume_convexHull.c 3 : ENNReal) *
        ((a : ENNReal) * (b : ENNReal)) ≤ volume K.carrier :=
    hK.volume_lower (by simp)
  have hK0 : volume K.carrier ≠ 0 := by
    have hlow0 : ((Cw : ENNReal) ^ 3)⁻¹ *
        (Metric.lt_volume_convexHull.c 3 : ENNReal) *
        ((a : ENNReal) * (b : ENNReal)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      · exact ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
      · exact mul_ne_zero (ENNReal.coe_ne_zero.mpr ha.ne')
          (ENNReal.coe_ne_zero.mpr hb.ne')
    exact (pos_iff_ne_zero.mpr hlow0).trans_le hKlower |>.ne'
  have hW0 : volume W.carrier ≠ 0 := by
    rw [show volume W.carrier =
        8 * (comparablePlankEnvelope.bodyThin Cw a : ENNReal) *
          (comparablePlankEnvelope.bodyWide Cw b : ENNReal) * 1 by
      exact Prism3D.volume_carrier
        (comparablePlankEnvelope.bodyPlank Cw a b hab hCa K)]
    simp only [mul_one]
    have hwide : 0 < comparablePlankEnvelope.bodyWide Cw b := by
      rw [comparablePlankEnvelope.bodyWide]
      exact lt_min (mul_pos (zero_lt_one.trans_le hCw) hb) zero_lt_one
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr
        (mul_pos (zero_lt_one.trans_le hCw) ha).ne'))
      (ENNReal.coe_ne_zero.mpr hwide.ne')
  have hWupper : volume W.carrier ≤
      8 * (Cw : ENNReal) ^ 2 * ((a : ENNReal) * (b : ENNReal)) := by
    rw [show volume W.carrier =
        8 * (comparablePlankEnvelope.bodyThin Cw a : ENNReal) *
          (comparablePlankEnvelope.bodyWide Cw b : ENNReal) * 1 by
      exact Prism3D.volume_carrier
        (comparablePlankEnvelope.bodyPlank Cw a b hab hCa K)]
    simp only [mul_one, comparablePlankEnvelope.bodyThin, ENNReal.coe_mul]
    calc
      8 * ((Cw : ENNReal) * (a : ENNReal)) *
            (comparablePlankEnvelope.bodyWide Cw b : ENNReal)
          ≤ 8 * ((Cw : ENNReal) * (a : ENNReal)) *
              ((Cw : ENNReal) * (b : ENNReal)) := by
            gcongr
            exact_mod_cast comparablePlankEnvelope.bodyWide_le_mul Cw b
      _ = 8 * (Cw : ENNReal) ^ 2 * ((a : ENNReal) * (b : ENNReal)) := by ring
  have hratio : 2 * (volume W.carrier / volume K.carrier) ≤
      (flatPrismInnerFrostman.C Cw : ENNReal) := by
    have hCw0 : (Cw : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCw)).ne'
    have hc0 : (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Metric.lt_volume_convexHull.c_pos 3)).ne'
    have hab0 : (a : ENNReal) * (b : ENNReal) ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.mpr ha.ne') (ENNReal.coe_ne_zero.mpr hb.ne')
    have hCpow : (Cw : ENNReal) ^ 5 * ((Cw : ENNReal) ^ 3)⁻¹ =
        (Cw : ENNReal) ^ 2 := by
      rw [ENNReal.inv_pow]
      calc
        (Cw : ENNReal) ^ 5 * (Cw : ENNReal)⁻¹ ^ 3 =
            (Cw : ENNReal) ^ 2 *
              ((Cw : ENNReal) * (Cw : ENNReal)⁻¹) ^ 3 := by ring
        _ = (Cw : ENNReal) ^ 2 := by
          rw [ENNReal.mul_inv_cancel hCw0 ENNReal.coe_ne_top]
          simp
    have hc : (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
        (Metric.lt_volume_convexHull.c 3 : ENNReal) = 1 :=
      ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top
    have hbase : 2 * volume W.carrier ≤
        (16 * (Cw : ENNReal) ^ 5 *
            (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) * volume K.carrier := by
      calc
        2 * volume W.carrier ≤
            2 * (8 * (Cw : ENNReal) ^ 2 * ((a : ENNReal) * (b : ENNReal))) := by
              gcongr
        _ = (16 * (Cw : ENNReal) ^ 5 *
              (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) *
              (((Cw : ENNReal) ^ 3)⁻¹ *
                (Metric.lt_volume_convexHull.c 3 : ENNReal) *
                ((a : ENNReal) * (b : ENNReal))) := by
              rw [show (16 : ENNReal) = 2 * 8 by norm_num]
              calc
                2 * (8 * (Cw : ENNReal) ^ 2 * ((a : ENNReal) * (b : ENNReal))) =
                    (2 * 8) * (Cw : ENNReal) ^ 2 *
                      ((a : ENNReal) * (b : ENNReal)) := by ring
                _ =
                    (2 * 8) * ((Cw : ENNReal) ^ 5 * ((Cw : ENNReal) ^ 3)⁻¹) *
                      ((Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ *
                        (Metric.lt_volume_convexHull.c 3 : ENNReal)) *
                      ((a : ENNReal) * (b : ENNReal)) := by rw [hCpow, hc, mul_one]
                _ = _ := by ring
        _ ≤ (16 * (Cw : ENNReal) ^ 5 *
              (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹) * volume K.carrier := by
              gcongr
    have hdiv : 2 * (volume W.carrier / volume K.carrier) ≤
        16 * (Cw : ENNReal) ^ 5 *
          (Metric.lt_volume_convexHull.c 3 : ENNReal)⁻¹ := by
      rw [← mul_div_assoc,
        ENNReal.div_le_iff hK0 K.isCompact.measure_ne_top]
      simpa [mul_assoc] using hbase
    exact hdiv.trans (by
      have hnn : (16 * Cw ^ (5 : ℕ) *
          (Metric.lt_volume_convexHull.c 3)⁻¹ : NNReal) ≤
          flatPrismInnerFrostman.C Cw := by
        exact le_max_right _ _
      have hcoe := ENNReal.coe_le_coe.mpr hnn
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_inv (Metric.lt_volume_convexHull.c_pos 3).ne'] at hcoe
      exact hcoe)
  exact (hFr.change_ambient hTK hTW hK0 hW0).mono hratio

/-- Fixed constant for changing a factor fibre's Frostman ambient body from its actual
`Cw`-comparable plank body to the unit ball.  The scale-dependent part of that change is kept
separately as `(a*b)⁻¹`. -/
noncomputable def flatPrismUnitBallFrostman.C (Cw : NNReal) : ENNReal :=
  max 1 (2 * volume
      (ConvexSpaceBody.closedUnitBall :
        ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier /
    ((Metric.lt_volume_convexHull.c 3 : ENNReal) * (Cw : ENNReal)⁻¹ ^ 3))

theorem flatPrismUnitBallFrostman.one_le (Cw : NNReal) :
    1 ≤ flatPrismUnitBallFrostman.C Cw := le_max_left _ _

/-- A factorisation fibre which is `2`-Frostman in an actual `Cw`-comparable `a × b × 1`
body is Frostman in the unit ball with the explicit scale loss `(a*b)⁻¹`.

The loss is only the ratio between the unit-ball volume and the lower volume bound for the
actual factor body.  It is later paid by the transverse factors already present in the
Proposition 6.6(A) target. -/
theorem IsPlankOfDimensions.frostmanIn_closedUnitBall
    {Cw a b : NNReal} (hCw : 1 ≤ Cw) (ha : 0 < a) (hb : 0 < b)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hK : IsPlankOfDimensions Cw a b K)
    (hKball : K ≤ ConvexSpaceBody.closedUnitBall)
    {I : Type*} {q : Finset I}
    {T : I → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hTK : ∀ i ∈ q, T i ≤ K)
    (hFr : IsFrostmanIn q T K 2) :
    IsFrostmanIn q T ConvexSpaceBody.closedUnitBall
      (flatPrismUnitBallFrostman.C Cw *
        (((a : ENNReal) * (b : ENNReal))⁻¹)) := by
  let B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ConvexSpaceBody.closedUnitBall
  let base : ENNReal :=
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * (Cw : ENNReal)⁻¹ ^ 3
  have hbase0 : base ≠ 0 := by
    dsimp [base]
    exact mul_ne_zero
      (ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne')
      (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top))
  have hbaseTop : base ≠ ⊤ := by
    dsimp [base]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr
        (zero_lt_one.trans_le hCw).ne')))
  have hab0 : (a : ENNReal) * (b : ENNReal) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr ha.ne') (ENNReal.coe_ne_zero.mpr hb.ne')
  have habTop : (a : ENNReal) * (b : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hKlower : base * ((a : ENNReal) * (b : ENNReal)) ≤ volume K.carrier := by
    simpa only [base, ENNReal.inv_pow, mul_assoc, mul_left_comm, mul_comm] using
      hK.volume_lower (by simp)
  have hK0 : volume K.carrier ≠ 0 :=
    (pos_iff_ne_zero.mpr (mul_ne_zero hbase0 hab0)).trans_le hKlower |>.ne'
  have hB0 : volume B.carrier ≠ 0 := by
    dsimp [B]
    exact ConvexSpaceBody.closedUnitBall_volume_pos.ne'
  have hTB : ∀ i ∈ q, T i ≤ B := fun i hi ↦ (hTK i hi).trans hKball
  apply (hFr.change_ambient hTK hTB hK0 hB0).mono
  calc
    2 * (volume B.carrier / volume K.carrier) ≤
        2 * (volume B.carrier /
          (base * ((a : ENNReal) * (b : ENNReal)))) := by
      gcongr
    _ = (2 * volume B.carrier / base) *
          (((a : ENNReal) * (b : ENNReal))⁻¹) := by
      rw [div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hbase0) (Or.inl hbaseTop)]
      ring
    _ ≤ flatPrismUnitBallFrostman.C Cw *
          (((a : ENNReal) * (b : ENNReal))⁻¹) := by
      gcongr
      exact le_max_right _ _

/-- The transverse factors in the Part-(A) inner target pay for changing a fibre's Frostman
ambient body from an `a × b × 1` factor body to the unit ball. -/
theorem flatPrism_inner_scale_pays_unitBallFrostman
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {σ a b : NNReal} (hσ : 0 < σ) (hσa : σ ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2) ≤
      ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
        ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
        (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) := by
  have ha : 0 < a := hσ.trans_le hσa
  have hb : 0 < b := ha.trans_le hab
  have hp : 0 ≤ 1 - β / 2 := by linarith
  have h1b : 0 ≤ 1 - β := by linarith
  have hβhalf : 0 ≤ β / 2 := by positivity
  have ha0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have hb0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
  have hat : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbt : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hratio : (1 : ENNReal) ≤
      ((b : ENNReal) / (a : ENNReal)) ^ (β / 2) := by
    have hba : (1 : ENNReal) ≤ (b : ENNReal) / (a : ENNReal) :=
      (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).2 (by
        simpa using (show (a : ENNReal) ≤ b by exact_mod_cast hab))
    calc
      (1 : ENNReal) = 1 ^ (β / 2) := by rw [ENNReal.one_rpow]
      _ ≤ ((b : ENNReal) / (a : ENNReal)) ^ (β / 2) :=
        ENNReal.rpow_le_rpow hba hβhalf
  have htrans : (1 : ENNReal) ≤
      ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) := by
    rw [show -2 * β = -(2 * β) by ring, ENNReal.rpow_neg]
    apply ENNReal.one_le_inv.mpr
    apply ENNReal.rpow_le_one
    · rw [mul_comm, ← div_eq_mul_inv]
      exact (ENNReal.div_le_iff ha0 hat).2 (by
        simpa using (show (σ : ENNReal) ≤ a by exact_mod_cast hσa))
    · linarith
  have hcore : (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2) ≤
      ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
        (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) := by
    have ha2 : (((a : ENNReal) ^ 2) ^ (-(1 - β / 2))) =
        (a : ENNReal) ^ (-2 * (1 - β / 2)) := by
      calc
        (((a : ENNReal) ^ 2) ^ (-(1 - β / 2))) =
            (((a : ENNReal) ^ (2 : ℝ)) ^ (-(1 - β / 2))) := by
          congr 1
          exact (ENNReal.rpow_natCast (a : ENNReal) 2).symm
        _ = (a : ENNReal) ^ ((2 : ℝ) * (-(1 - β / 2))) := by
          rw [ENNReal.rpow_mul]
        _ = (a : ENNReal) ^ (-2 * (1 - β / 2)) := by
          congr 1
          ring
    calc
      (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2) =
          (a : ENNReal) ^ (-(1 - β / 2)) *
            (b : ENNReal) ^ (-(1 - β / 2)) := by
        rw [ENNReal.inv_rpow, ENNReal.mul_rpow_of_nonneg _ _ hp,
          ENNReal.mul_inv
            (a := (a : ENNReal) ^ (1 - β / 2))
            (b := (b : ENNReal) ^ (1 - β / 2))
            (Or.inl (by positivity)) (Or.inl (by finiteness)),
          ← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
      _ =
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
            (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) *
            (((b : ENNReal) / (a : ENNReal)) ^ (β / 2))⁻¹ := by
        rw [ENNReal.div_rpow_of_nonneg _ _ h1b, ENNReal.inv_rpow,
          ENNReal.div_rpow_of_nonneg _ _ hβhalf]
        rw [ENNReal.inv_div (Or.inl (by finiteness)) (Or.inl (by positivity))]
        simp only [div_eq_mul_inv]
        repeat' rw [← ENNReal.rpow_neg]
        rw [show β * 2⁻¹ = β / 2 by ring]
        rw [ha2]
        calc
          (a : ENNReal) ^ (-(1 - β / 2)) * (b : ENNReal) ^ (-(1 - β / 2)) =
              ((a : ENNReal) ^ (1 - β) *
                  (a : ENNReal) ^ (-2 * (1 - β / 2)) *
                  (a : ENNReal) ^ (β / 2)) *
                ((b : ENNReal) ^ (-(1 - β)) *
                  (b : ENNReal) ^ (-(β / 2))) := by
            repeat' rw [← ENNReal.rpow_add _ _ ha0 hat]
            repeat' rw [← ENNReal.rpow_add _ _ hb0 hbt]
            congr 1 <;> ring
          _ = _ := by ring
      _ ≤ ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
            (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) * 1 := by
        gcongr
        exact ENNReal.inv_le_one.mpr hratio
      _ = _ := by ring
  calc
    (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2) ≤
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) := hcore
    _ ≤ ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
        ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
        (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) := by
      calc
        _ = ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) * 1 *
            (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) := by ring
        _ ≤ _ := by gcongr

/-
/-- The Frostman partial estimate applied directly to one complete flat-prism fibre.

There is no middle-width threshold in this lemma.  The fibre is still a family of fine
`σ`-tubes, so the partial estimate is applied before anisotropic normalisation.  The preceding
two lemmas show that changing its factor-body Frostman ambient to the unit ball costs only a
fixed constant and `(a*b)⁻¹`, and that the latter is already dominated by the transverse factors
in the Part-(A) inner target. -/
theorem FrostmanEstimate.flatPrismInnerFiber {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (Cw : NNReal) (hCw : 1 ≤ Cw) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (q : Finset ι)
        (T : ι → ShadedTube σ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (q : Set ι).Pairwise
          (fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (σ : ENNReal) ^ η ≤ fullness q (fun i ↦ (T i).toShadedBody) →
        ∀ {a b : NNReal}, σ ≤ a → a ≤ b → b ≤ 1 →
        ∀ (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
          IsPlankOfDimensions Cw a b K → K ≤ ConvexSpaceBody.closedUnitBall →
          (∀ i ∈ q, (T i).toConvexSpaceBody ≤ K) →
          IsFrostmanIn q (fun i ↦ (T i).toConvexSpaceBody) K 2 →
          multiplicity q (fun i ↦ (T i).toShadedBody) ≤
            (σ : ENNReal) ^ (-ε) *
              ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
              ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
              (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                (q.card : ENNReal)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ :=
    FrostmanEstimate.multiplicity_bound_of_mem (E := EuclideanSpace ℝ (Fin 3))
      hβ0 hβ1 (by norm_num) hKF (ε / 2) (by positivity)
  let C₀ : ENNReal := flatPrismUnitBallFrostman.C Cw
  have hC₀1 : 1 ≤ C₀ := flatPrismUnitBallFrostman.one_le Cw
  have hC₀0 : C₀ ≠ 0 := (zero_lt_one.trans_le hC₀1).ne'
  have hC₀top : C₀ ≠ ⊤ := by
    dsimp [C₀, flatPrismUnitBallFrostman.C]
    apply max_ne_top
    constructor
    · norm_num
    · exact ENNReal.div_ne_top (by finiteness) (by
        exact mul_ne_zero
          (ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne')
          (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)))
  let Cnn : NNReal := C₀.toNNReal
  have hCnn1 : 1 ≤ Cnn := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hC₀top]
    exact hC₀1
  obtain ⟨σ₀, hσ₀, hCabs⟩ :=
    rpowConstAbsorb Cnn hCnn1 (show 0 ≤ 1 - β / 2 by linarith)
      (show 0 < ε / 2 by positivity)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT hσ₀] with σ hbound hσrange
  intro ι q T hball hED hfull a b hσa hab hb1 K hKdim hKball hTK hFr
  have hσ : 0 < σ := hσrange.1
  have ha : 0 < a := hσ.trans_le hσa
  have hb : 0 < b := ha.trans_le hab
  have hfull' : σ ^ η ≤ fullness q (fun i ↦ (T i).toShadedBody) := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg _ hη.le]
    exact hfull
  have hdirect := hbound q T hball hED hfull'
  have hFrBall := hKdim.frostmanIn_closedUnitBall hCw ha hb hKball hTK hFr
  have hCF : frostmanConstIn q (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤
      C₀ * (((a : ENNReal) * (b : ENNReal))⁻¹) := by
    simpa only [C₀] using ConvexSpaceBody.frostmanConstIn_le hFrBall
  have hp : 0 ≤ 1 - β / 2 := by linarith
  have hCFpow :
      (frostmanConstIn q (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2) ≤
      C₀ ^ (1 - β / 2) *
        (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2) := by
    calc
      _ ≤ (C₀ * (((a : ENNReal) * (b : ENNReal))⁻¹)) ^ (1 - β / 2) :=
        ENNReal.rpow_le_rpow hCF hp
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hp
  have hscale := flatPrism_inner_scale_pays_unitBallFrostman hβ0 hβ1 hσ hσa hab hb1
  have hconst : C₀ ^ (1 - β / 2) ≤ (σ : ENNReal) ^ (-(ε / 2)) := by
    have hcoe : (Cnn : ENNReal) = C₀ := ENNReal.coe_toNNReal hC₀top
    rw [← hcoe]
    exact hCabs σ hσ hσrange.2.le
  have hσmul : (σ : ENNReal) ^ (-(ε / 2)) *
      (σ : ENNReal) ^ (-(ε / 2)) = (σ : ENNReal) ^ (-ε) := by
    rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne') ENNReal.coe_ne_top]
    congr 1
    ring
  have hcard :
      (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2) *
          (((q.card : ENNReal) * (σ : ENNReal) ^ 2) ^ (1 - β / 2)) =
        (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
          (q.card : ENNReal)) ^ (1 - β / 2) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp]
    congr 1
    ring
  calc
    multiplicity q (fun i ↦ (T i).toShadedBody) ≤
        (σ : ENNReal) ^ (-(ε / 2)) *
          (frostmanConstIn q (fun i ↦ (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2) *
          (σ : ENNReal) ^ (-2 * β) *
          ((q.card : ENNReal) * (σ : ENNReal) ^ 2) ^ (1 - β / 2) := by
      simpa only [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by norm_num,
        Nat.reduceSub, mul_assoc] using hdirect
    _ ≤ (σ : ENNReal) ^ (-(ε / 2)) *
        (C₀ ^ (1 - β / 2) *
          (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2)) *
        (σ : ENNReal) ^ (-2 * β) *
        ((q.card : ENNReal) * (σ : ENNReal) ^ 2) ^ (1 - β / 2) := by gcongr
    _ ≤ (σ : ENNReal) ^ (-(ε / 2)) *
        ((σ : ENNReal) ^ (-(ε / 2)) *
          (((a : ENNReal) * (b : ENNReal))⁻¹) ^ (1 - β / 2)) *
        (σ : ENNReal) ^ (-2 * β) *
        ((q.card : ENNReal) * (σ : ENNReal) ^ 2) ^ (1 - β / 2) := by gcongr
    _ ≤ (σ : ENNReal) ^ (-(ε / 2)) *
        ((σ : ENNReal) ^ (-(ε / 2)) *
          (((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
            ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
            (((a : ENNReal) ^ 2)⁻¹) ^ (1 - β / 2))) *
        (σ : ENNReal) ^ (-2 * β) *
        ((q.card : ENNReal) * (σ : ENNReal) ^ 2) ^ (1 - β / 2) := by gcongr
    _ = (σ : ENNReal) ^ (-ε) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
          (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
            (q.card : ENNReal)) ^ (1 - β / 2) := by
      rw [← hcard, ← hσmul]
      ring
-/

/-- A part of a factorization cannot have more volume than `C` times the total volume of its
inner bodies.  The point is the `maxDensity_le_mul` field: the maximal density is at least one,
while the density of the part in its own convex hull is exactly inner mass divided by hull
volume. -/
theorem factorization_part_volume_le_mul_sum_volume
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {W : ι → ConvexSpaceBody E} {C : NNReal}
    (F : ConvexSpaceBody.Factorization s W C)
    (hpos : ∀ i ∈ s, 0 < volume (W i).carrier)
    {part : Finset ι} (hpart : part ∈ F.parts) :
    volume (part.convexHull_biUnion W).carrier ≤
      (C : ENNReal) * ∑ i ∈ part, volume (W i).carrier := by
  have hmax : 1 ≤ maxDensity s W := by
    obtain ⟨i, hi⟩ := F.nonempty_of_mem_parts hpart
    exact one_le_maxDensity ⟨i, F.subset hpart hi, hpos i (F.subset hpart hi)⟩
  have hdens : 1 ≤ (C : ENNReal) * densityIn part W (part.convexHull_biUnion W) :=
    hmax.trans (F.maxDensity_le_mul part hpart)
  calc
    volume (part.convexHull_biUnion W).carrier =
        1 * volume (part.convexHull_biUnion W).carrier := by simp
    _ ≤ ((C : ENNReal) * densityIn part W (part.convexHull_biUnion W)) *
        volume (part.convexHull_biUnion W).carrier := by gcongr
    _ = (C : ENNReal) *
        (densityIn part W (part.convexHull_biUnion W) *
          volume (part.convexHull_biUnion W).carrier) := by rw [mul_assoc]
    _ = (C : ENNReal) * ∑ i ∈ part, volume (W i).carrier := by
      rw [← sum_volume_eq_densityIn_mul_volume' (part.le_convexHull_biUnion W)]

/-- Summed form of
`Kakeya.factorization_part_volume_le_mul_sum_volume`: uniform lower
volume of the outer hulls and uniform upper volume of the inner bodies bound the number of
parts. -/
theorem factorization_card_mul_volumeLower_le
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {W : ι → ConvexSpaceBody E} {C : NNReal}
    (F : ConvexSpaceBody.Factorization s W C)
    (hpos : ∀ i ∈ s, 0 < volume (W i).carrier)
    {vmin vmax : ENNReal}
    (hlower : ∀ part ∈ F.parts, vmin ≤ volume (part.convexHull_biUnion W).carrier)
    (hupper : ∀ i ∈ s, volume (W i).carrier ≤ vmax) :
    (F.parts.card : ENNReal) * vmin ≤ (C : ENNReal) * (s.card : ENNReal) * vmax := by
  calc
    (F.parts.card : ENNReal) * vmin = F.parts.card • vmin := by simp
    _ ≤ ∑ part ∈ F.parts, volume (part.convexHull_biUnion W).carrier :=
      Finset.card_nsmul_le_sum F.parts _ vmin hlower
    _ ≤ ∑ part ∈ F.parts, (C : ENNReal) * ∑ i ∈ part, volume (W i).carrier := by
      exact Finset.sum_le_sum fun part hpart ↦
        factorization_part_volume_le_mul_sum_volume F hpos hpart
    _ = (C : ENNReal) * ∑ part ∈ F.parts, ∑ i ∈ part, volume (W i).carrier := by
      simp only [Finset.mul_sum]
    _ = (C : ENNReal) * ∑ i ∈ s, volume (W i).carrier := by
      rw [← F.sum_eq_sum_parts_sum]
    _ ≤ (C : ENNReal) * ((s.card : ENNReal) * vmax) := by
      gcongr
      simpa only [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul s (fun i ↦ volume (W i).carrier) vmax hupper)
    _ = (C : ENNReal) * (s.card : ENNReal) * vmax := by ring

/-- A division-free count obtained from a Frostman family with uniform member-volume bounds.
The test body need not lie in the ambient body: it is intersected with the ambient body when the
Frostman hypothesis is applied. -/
theorem frostman_count_mul_volumeLower_mul_ambientVolume_le
    {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {B K : ConvexSpaceBody E} {CF vmin vmax : ENNReal}
    (hFrost : IsFrostmanIn s W B CF) (hWB : ∀ i ∈ s, W i ≤ B)
    (hlower : ∀ i ∈ s, vmin ≤ volume (W i).carrier)
    (hupper : ∀ i ∈ s, volume (W i).carrier ≤ vmax) :
    (((s.filter fun i => W i ≤ K).card : ENNReal) * vmin) * volume B.carrier ≤
      CF * (s.card : ENNReal) * vmax * volume K.carrier := by
  classical
  let t := s.filter fun i => W i ≤ K
  by_cases ht : t = ∅
  · simp [t, ht]
  have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
  obtain ⟨i, hi⟩ := htne
  have his : i ∈ s := (Finset.mem_filter.mp hi).1
  have hiK : W i ≤ K := (Finset.mem_filter.mp hi).2
  have hne : (K.carrier ∩ B.carrier).Nonempty := by
    obtain ⟨x, hx⟩ := (W i).nonempty'
    exact ⟨x, hiK hx, hWB i his hx⟩
  let L := ConvexSpaceBody.inter K B hne
  have hLB : L ≤ B := by
    intro x hx
    exact hx.2
  have hdensity : densityIn s W K ≤ CF * densityIn s W B :=
    (ConvexSpaceBody.densityIn_le_densityIn_inter hWB hne).trans (hFrost L hLB)
  have hcount : (t.card : ENNReal) * vmin ≤ densityIn s W K * volume K.carrier := by
    calc
      (t.card : ENNReal) * vmin ≤ ∑ i ∈ t, volume (W i).carrier := by
        simpa only [nsmul_eq_mul] using
          (Finset.card_nsmul_le_sum t (fun i ↦ volume (W i).carrier) vmin
            (fun i hi ↦ hlower i (Finset.mem_filter.mp hi).1))
      _ = ∑ i ∈ s with W i ≤ K, volume (W i).carrier := by rfl
      _ = densityIn s W K * volume K.carrier :=
        sum_volume_eq_densityIn_mul_volume s W K
  have htotal : densityIn s W B * volume B.carrier ≤ (s.card : ENNReal) * vmax := by
    rw [← sum_volume_eq_densityIn_mul_volume' hWB]
    simpa only [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul s (fun i ↦ volume (W i).carrier) vmax hupper)
  change ((t.card : ENNReal) * vmin) * volume B.carrier ≤ _
  calc
    ((t.card : ENNReal) * vmin) * volume B.carrier ≤
        (densityIn s W K * volume K.carrier) * volume B.carrier := by gcongr
    _ ≤ (CF * densityIn s W B * volume K.carrier) * volume B.carrier := by gcongr
    _ = CF * (densityIn s W B * volume B.carrier) * volume K.carrier := by ring
    _ ≤ CF * ((s.card : ENNReal) * vmax) * volume K.carrier := by gcongr
    _ = CF * (s.card : ENNReal) * vmax * volume K.carrier := by ring

/-- The absolute `θ b`-neighbourhood of an `a × b × 1` plank-like body has the expected
`O(θ b²)` volume whenever `a ≤ θ b` and `θ, b ≤ 1`.  This is the true-neighbourhood geometry
needed for the parentwise `M θ` count; it does not use a relative dilation. -/
theorem IsPlankOfDimensions.volume_cthickening_mul_le (hdim : Module.finrank ℝ E = 3)
    {C a b θ : NNReal} {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W)
    (haθb : a ≤ θ * b) (hθ1 : θ ≤ 1) (hb1 : b ≤ 1) :
    volume (W.cthickening (θ * b)).carrier ≤
      8 * ((C : ENNReal) + 1) ^ 3 * (θ : ENNReal) * (b : ENNReal) ^ 2 := by
  obtain ⟨⟨_, h0⟩, ⟨⟨_, h1⟩, ⟨_, h2⟩⟩⟩ := hW
  have hdim0 : 0 < Module.finrank ℝ E := by omega
  have hdim1 : 1 < Module.finrank ℝ E := by omega
  have hdim2 : 2 < Module.finrank ℝ E := by omega
  have he0 := ConvexSpaceBody.ethickness_cthickening_eq W (θ * b) hdim0
  have he1 := ConvexSpaceBody.ethickness_cthickening_eq W (θ * b) hdim1
  have he2 := ConvexSpaceBody.ethickness_cthickening_eq W (θ * b) hdim2
  have he0' : Metric.ethickness ℝ (W.cthickening ((θ : ℝ) * (b : ℝ))).carrier 0 =
      (θ : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ W.carrier 0 := by
    simpa only [NNReal.coe_mul, ENNReal.coe_mul] using he0
  have he1' : Metric.ethickness ℝ (W.cthickening ((θ : ℝ) * (b : ℝ))).carrier 1 =
      (θ : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ W.carrier 1 := by
    simpa only [NNReal.coe_mul, ENNReal.coe_mul] using he1
  have he2' : Metric.ethickness ℝ (W.cthickening ((θ : ℝ) * (b : ℝ))).carrier 2 =
      (θ : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ W.carrier 2 := by
    simpa only [NNReal.coe_mul, ENNReal.coe_mul] using he2
  have hθE : (θ : ENNReal) ≤ 1 := by exact_mod_cast hθ1
  have hbE : (b : ENNReal) ≤ 1 := by exact_mod_cast hb1
  have haθbE : (a : ENNReal) ≤ (θ : ENNReal) * (b : ENNReal) := by
    exact_mod_cast haθb
  have hu0 : Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 0 ≤
      (C : ENNReal) + 1 := by
    rw [he0']
    calc
      (θ : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ W.carrier 0
          ≤ (θ : ENNReal) * (b : ENNReal) + (C : ENNReal) := add_le_add_right h0 _
      _ ≤ 1 + (C : ENNReal) := by
        gcongr
        calc
          (θ : ENNReal) * (b : ENNReal) ≤ 1 * 1 :=
            mul_le_mul hθE hbE (by simp) (by simp)
          _ = 1 := one_mul _
      _ = (C : ENNReal) + 1 := add_comm _ _
  have hu1 : Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 1 ≤
      ((C : ENNReal) + 1) * (b : ENNReal) := by
    rw [he1']
    calc
      (θ : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ W.carrier 1
          ≤ (θ : ENNReal) * (b : ENNReal) + (C : ENNReal) * (b : ENNReal) :=
            add_le_add_right h1 _
      _ = ((θ : ENNReal) + (C : ENNReal)) * (b : ENNReal) := by ring
      _ ≤ (1 + (C : ENNReal)) * (b : ENNReal) := by gcongr
      _ = ((C : ENNReal) + 1) * (b : ENNReal) := by rw [add_comm 1]
  have hu2 : Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 2 ≤
      ((C : ENNReal) + 1) * ((θ : ENNReal) * (b : ENNReal)) := by
    rw [he2']
    calc
      (θ : ENNReal) * (b : ENNReal) + Metric.ethickness ℝ W.carrier 2
          ≤ (θ : ENNReal) * (b : ENNReal) + (C : ENNReal) * (a : ENNReal) :=
            add_le_add_right h2 _
      _ ≤ (θ : ENNReal) * (b : ENNReal) +
          (C : ENNReal) * ((θ : ENNReal) * (b : ENNReal)) := by gcongr
      _ = ((C : ENNReal) + 1) * ((θ : ENNReal) * (b : ENNReal)) := by ring
  have hprod : ∏ i ∈ Finset.range (Module.finrank ℝ E),
      Metric.ethickness ℝ (W.cthickening (θ * b)).carrier i =
        Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 0 *
          Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 1 *
            Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 2 := by
    rw [hdim]
    simp [Finset.prod_range_succ]
  calc
    volume (W.cthickening (θ * b)).carrier ≤
        2 ^ (Module.finrank ℝ E) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E),
            Metric.ethickness ℝ (W.cthickening (θ * b)).carrier i :=
      volume_le_prod_ethickness _
    _ = 8 * (Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 0 *
          Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 1 *
            Metric.ethickness ℝ (W.cthickening (θ * b)).carrier 2) := by
      rw [hprod, hdim]
      norm_num
    _ ≤ 8 * (((C : ENNReal) + 1) * (((C : ENNReal) + 1) * (b : ENNReal)) *
          (((C : ENNReal) + 1) * ((θ : ENNReal) * (b : ENNReal)))) := by
      gcongr
    _ = 8 * ((C : ENNReal) + 1) ^ 3 * (θ : ENNReal) * (b : ENNReal) ^ 2 := by
      ring

/-- The global absolute-neighbourhood count supplied by a Frostman bound for the outer bodies.
Unlike the parentwise Katz--Tao count below, this estimate pools all indices, but its right-hand
side necessarily contains both the Frostman constant and the total outer cardinality. -/
theorem flatPrismGlobalBlock_count_cthickening_mul_le
    {ι : Type*} {u : Finset ι} {W : ι → ConvexSpaceBody E}
    {Cw a b θ : NNReal} {CF : ENNReal}
    (hdim : Module.finrank ℝ E = 3) (hW : IsPlankFamilyOfDimensions Cw a b u W)
    (hFrost : IsFrostmanIn u W ConvexSpaceBody.closedUnitBall CF)
    (hWB : ∀ i ∈ u, W i ≤ ConvexSpaceBody.closedUnitBall)
    (haθb : a ≤ θ * b) (hθ1 : θ ≤ 1) (hb1 : b ≤ 1)
    (anchor : ι) (hanchor : anchor ∈ u) :
    ((((u.filter fun i => W i ≤ (W anchor).cthickening (θ * b)).card : ENNReal) *
          (((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
            ((a : ENNReal) * (b : ENNReal)))) *
        volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
      CF * (u.card : ENNReal) *
        (8 * (Cw : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal))) *
        (8 * ((Cw : ENNReal) + 1) ^ 3 * (θ : ENNReal) * (b : ENNReal) ^ 2) := by
  have hcount := frostman_count_mul_volumeLower_mul_ambientVolume_le
    (s := u) (W := W) (K := (W anchor).cthickening (θ * b))
    (vmin := ((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
      ((a : ENNReal) * (b : ENNReal)))
    (vmax := 8 * (Cw : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal)))
    hFrost hWB (fun i hi ↦ (hW i hi).volume_lower hdim)
    (fun i hi ↦ (hW i hi).volume_upper hdim)
  have hvol := (hW anchor hanchor).volume_cthickening_mul_le hdim haθb hθ1 hb1
  exact hcount.trans (by gcongr)

/-! ### One-sided uniformity

`ShadedTube.ShadedUniformTubeSet` is two-sided, and restricting the index set shrinks every
`ShadedTube.shadeClass`, so exactly the two clauses that bound a *shrinking* quantity from below
fail to descend to a subfamily: `le_card_shadeClass` and `branchingN_le`.  The other two do
descend, for two different reasons — `card_shadeClass_le` because it is an upper bound on the
shrinking class, and `le_branchingN` because it never mentions the index set.  At the tube level
the same split leaves `tube_injOn`, `boundedOverlap` and `card_class_le` and drops
`le_card_class`.

`Kakeya.IsFlatPrismUniformTubeSet` and `Kakeya.IsFlatPrismUniform` are those surviving halves.
They restrict to an arbitrary subfamily with the data inherited verbatim, at no loss in the
constant and with no pigeonholing, and every two-sided hierarchy projects onto them, so
"project, then restrict" replaces a re-uniformization.

**These duplicate `Kakeya.ml1Boot.IsOneSidedUniform` and
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet`**, field for field and proof for proof.  The
duplication is deliberate, and it is forced: that file is Section 8 material, while this file
must not depend on Section 8 (see the module docstring), so the predicate cannot be imported
here.  The two copies are convertible field by field; anything changed in one has to be changed
in the other.
-/

/-- **The shaded class is monotone in the index set.**

`ShadedTube.shadeClass` is a filter of `Tube.coverClass`, so it inherits
`Tube.coverClass_subset_of_subset`.  This is the reason the *upper* class bracket of
`ShadedTube.ShadedUniformTubeSet` survives restriction.  The Section-8 twin is
`Kakeya.ml1Boot.shadeClass_subset_of_subset`. -/
theorem flatPrismShadeClass_subset_of_subset {ι : Type*} {δ : NNReal} {s s' : Finset ι}
    (hs : s' ⊆ s) (V : ι → ShadedTube δ E) (assign : ι → ι) (j : ι) (x : E) :
    ShadedTube.shadeClass s' V assign j x ⊆ ShadedTube.shadeClass s V assign j x := by
  classical
  intro i hi
  simp only [ShadedTube.shadeClass, Finset.mem_filter] at hi ⊢
  exact ⟨Tube.coverClass_subset_of_subset hs assign j hi.1, hi.2⟩

/-- **A nested cover system restricts to a subfamily verbatim.**

Every field of `Tube.GridCoverSystem` is either free data (`indexSet`, `assign`, `tube`) or a
statement quantified over the members of the family, so the node data is kept unchanged and each
clause is read on a smaller set.  `indexSet` is deliberately *not* shrunk: no clause asserts that
a node is inhabited.  The Section-8 twin is `Kakeya.ml1Boot.gridCoverRestrict`. -/
def flatPrismGridCoverRestrict {ι : Type*} {δ : NNReal} {s s' : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (cover : Tube.GridCoverSystem s T N) (hs : s' ⊆ s) :
    Tube.GridCoverSystem s' T N where
  indexSet := cover.indexSet
  assign := cover.assign
  tube := cover.tube
  assign_mem k hk i hi := cover.assign_mem k hk i (hs hi)
  le_tube_assign k hk i hi := cover.le_tube_assign k hk i (hs hi)
  nested k hk i hi j hj := cover.nested k hk i (hs hi) j (hs hj)
  tube_nested k hk i hi := cover.tube_nested k hk i (hs hi)

/-- **The half of `Tube.UniformTubeSet` that restricts** (the one-sided reading of GWZ
Definition 2.1).

Definition 2.1 with the *lower* class bracket `Tube.UniformTubeSet.le_card_class` deleted.  What
remains is the hierarchy, the injective indexing of the nodes, bounded overlap and the upper
class bracket, every clause of which is either independent of the index set or an upper bound on
a quantity monotone in it.  The Section-8 twin is
`Kakeya.ml1Boot.IsOneSidedUniformTubeSet`. -/
structure IsFlatPrismUniformTubeSet {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (N : ℕ) (C : NNReal) where
  /-- The nested system of covers along the grid `ρ_k = δ^{k/N}`. -/
  cover : Tube.GridCoverSystem s T N
  /-- The branching number at each grid scale, a free datum. -/
  branchingN : ℕ → NNReal
  /-- Distinct node indices name distinct node tubes. -/
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  /-- **Definition 2.1(ii) (Bounded overlap).** -/
  boundedOverlap : ∀ k ≤ N, ∀ W : Tube (Tube.gridScale δ N k) E,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody)).card ≤ C
  /-- **Definition 2.1(iii), upper half only.** -/
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((Tube.coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k

/-- Every two-sided hierarchy is one-sided: forget `Tube.UniformTubeSet.le_card_class`. -/
def IsFlatPrismUniformTubeSet.of_uniformTubeSet {ι : Type*} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) :
    IsFlatPrismUniformTubeSet s T N C where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := 𝒰.boundedOverlap
  card_class_le := 𝒰.card_class_le

/-- **One-sided tube uniformity restricts to an arbitrary subfamily, at the same constant.**

The node data is inherited verbatim by `Kakeya.flatPrismGridCoverRestrict`; `boundedOverlap`
descends because its filter predicate weakens, and `card_class_le` because
`Tube.coverClass_subset_of_subset` shrinks the class it bounds. -/
def IsFlatPrismUniformTubeSet.mono_index {ι : Type*} {δ : NNReal} {s s' : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : IsFlatPrismUniformTubeSet s T N C)
    (hs : s' ⊆ s) : IsFlatPrismUniformTubeSet s' T N C where
  cover := flatPrismGridCoverRestrict 𝒰.cover hs
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := by
    classical
    intro k hk V
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (𝒰.boundedOverlap k hk V)
    intro j hj
    simp only [flatPrismGridCoverRestrict, Finset.mem_filter] at hj ⊢
    obtain ⟨hjmem, i, hi, h1, h2⟩ := hj
    exact ⟨hjmem, i, hs hi, h1, h2⟩
  card_class_le := by
    intro k hk j hj
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (𝒰.card_class_le k hk j ?_)
    · exact Tube.coverClass_subset_of_subset hs (𝒰.cover.assign k) j
    · simpa only [flatPrismGridCoverRestrict] using hj

/-- **The half of `ShadedTube.ShadedUniformTubeSet` that restricts** (the one-sided reading of
GWZ Definition 2.2).

Definition 2.2 with the two clauses that bound a *shrinking* quantity from below deleted:
`le_card_shadeClass` and `branchingN_le` are gone, `card_shadeClass_le` and `le_branchingN`
remain, and the ambient tube hierarchy is the one-sided `Kakeya.IsFlatPrismUniformTubeSet`.

What the two survivors say together is that no node the fibre of `x` meets carries more than
`C · localN x k` members of that fibre, and that `localN x k` is no larger than
`C · branchingN k`: a uniform *upper* bound on the local branching, with `branchingN`
independent of `x`.  A consumer needing a member of *every* class is not served.  The Section-8
twin is `Kakeya.ml1Boot.IsOneSidedUniform`. -/
structure IsFlatPrismUniform {ι : Type*} {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E)
    (N : ℕ) (C : NNReal) where
  /-- The underlying tubes carry a one-sided uniform hierarchy. -/
  tubeUniform : IsFlatPrismUniformTubeSet s (fun i => (V i).toTube) N C
  /-- The per-scale branching count shared across all points of the shade union. -/
  branchingN : ℕ → NNReal
  /-- The branching count of the fibre at a single point. -/
  localN : E → ℕ → NNReal
  /-- Each node met by the fibre of `x` contributes at most `C · localN x k` of its members. -/
  card_shadeClass_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k)
      (tubeUniform.cover.assign k i) x).card : NNReal) ≤ C * localN x k
  /-- Each local count is at most a factor `C` above the shared count. -/
  le_branchingN : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, localN x k ≤ C * branchingN k

/-- **Every two-sided shaded hierarchy is one-sided**: forget
`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` and
`ShadedTube.ShadedUniformTubeSet.branchingN_le`.

The two retained clauses transfer verbatim, the ambient hierarchy being projected by
`Kakeya.IsFlatPrismUniformTubeSet.of_uniformTubeSet`, which keeps `cover` unchanged, so the
occurrences of `tubeUniform.cover.assign` on either side are the same function. -/
def IsFlatPrismUniform.of_shadedUniformTubeSet {ι : Type*} {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C) : IsFlatPrismUniform s V N C where
  tubeUniform := IsFlatPrismUniformTubeSet.of_uniformTubeSet 𝒱.tubeUniform
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_branchingN := 𝒱.le_branchingN

/-- **One-sided shaded uniformity restricts to an arbitrary subfamily, at the same constant.**

The counting functions `branchingN` and `localN` are free fields and are inherited unchanged; the
ambient hierarchy restricts by `Kakeya.IsFlatPrismUniformTubeSet.mono_index`; the shade union
shrinks, which weakens both `∀ x` clauses; `card_shadeClass_le` descends because
`Kakeya.flatPrismShadeClass_subset_of_subset` shrinks the class it bounds; and `le_branchingN`
descends because it does not mention the index set. -/
def IsFlatPrismUniform.mono_index {ι : Type*} {δ : NNReal} {s s' : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : IsFlatPrismUniform s V N C)
    (hs : s' ⊆ s) : IsFlatPrismUniform s' V N C where
  tubeUniform := 𝒱.tubeUniform.mono_index hs
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := by
    intro x hx k hk i hi hxi
    have hxs : x ∈ (⋃ i ∈ s, (V i).shade) := by
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨j, hj, hxj⟩ := hx
      exact ⟨j, hs hj, hxj⟩
    refine le_trans ?_ (𝒱.card_shadeClass_le x hxs k hk i (hs hi) hxi)
    exact Nat.cast_le.mpr (Finset.card_le_card
      (flatPrismShadeClass_subset_of_subset hs V (𝒱.tubeUniform.cover.assign k)
        (𝒱.tubeUniform.cover.assign k i) x))
  le_branchingN := by
    intro x hx k hk
    have hxs : x ∈ (⋃ i ∈ s, (V i).shade) := by
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨j, hj, hxj⟩ := hx
      exact ⟨j, hs hj, hxj⟩
    exact 𝒱.le_branchingN x hxs k hk

/-- **Project, then restrict.**

A two-sided hierarchy at `s` yields one-sided uniformity at every `s' ⊆ s`, at the same constant
and with no loss.  This is what a producer of `Kakeya.IsFlatPrismFamily` at a refined index set
uses in place of a re-uniformization.  The Section-8 twin is
`Kakeya.ml1Boot.IsOneSidedUniform.of_shadedUniformTubeSet_subset`. -/
def IsFlatPrismUniform.of_shadedUniformTubeSet_subset {ι : Type*} {δ : NNReal} {s s' : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (𝒱 : ShadedTube.ShadedUniformTubeSet s V N C) (hs : s' ⊆ s) : IsFlatPrismUniform s' V N C :=
  (IsFlatPrismUniform.of_shadedUniformTubeSet 𝒱).mono_index hs

/-- **The family GWZ Proposition 6.6(A) is applied to** (blueprint
`prop:ml1bootFlatPrismsCorrected`, the hypotheses on `(𝕍, Z)`).

A nonempty `C_unif`-uniform family of shaded `σ`-tubes in `B₁` whose fullness is at least
`σ ^ η'`: the exact input that `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` runs on,
before any plank data is mentioned.

This is the local analogue of `Kakeya.ml1Boot.IsCaseFamily`, which cannot be reused because it
lives in Section 8 and this file must not depend on it.  The one difference from that package is
that the Frostman constant is not bounded above, since it appears as the factor
`C_F(𝕍, B₁) ^ (1 - β/2)` on the right-hand side of the conclusion rather than as a hypothesis.

## Why essential distinctness is a field

An earlier version of this package omitted it, on the reading that GWZ Proposition 6.6(A) does
not use it.  That reading is wrong twice over.

* Its proof does use it: the count
  `#{T ∈ 𝕋_W : T ⊆ a δ × (θb/a) δ × 1 prism} ≲ (θb/a) ^ 2` is justified in [GWZ] by the tubes of
  `𝕋` being essentially distinct, and uniformity does not supply that — uniformity constrains the
  parents at coarse scales by bounded overlap and says nothing about self-overlap of the leaves
  at their own scale.
* Without it the conclusion is **false** for every `β > 0`, by the duplication mechanism that
  also forces the essential-distinctness hypothesis of `Kakeya.FrostmanEstimate`.  Replace each
  member by `M` copies at fresh indices.  `Kakeya.ShadedBody.multiplicity` is
  `∑ |Z i| / |⋃ Z i|`, so it scales by `M`; `Kakeya.frostmanConstIn` is a ratio of densities and
  is invariant; `Kakeya.ShadedBody.fullness` is `∑ |Z i| / ∑ |V i|` and is invariant; and
  `s.card` scales by `M`, so the right-hand side scales only by `M ^ (1 - β/2)`.  All the
  remaining hypotheses survive: assigning every copy to its original's node keeps
  `Tube.UniformTubeSet` with the same constant (the nodes, and hence `tube_injOn` and
  `boundedOverlap`, are unchanged, and every class grows by the same factor `M`), and duplicating
  the parts of a `ConvexSpaceBody.Factorization` leaves the plank hulls — hence `isKatzTao`,
  `simDims` and `Kakeya.IsPlankFamilyOfDimensions` — untouched while scaling both sides of
  `maxDensity_le_mul` by `M`.  So the ratio of the two sides of the conclusion grows like
  `M ^ (β/2)`.

The hypothesis is free for the consumer: `Kakeya.ml1Boot.flatPrism_dichotomy`, the only place
this proposition is applied, already assumes its family pairwise essentially distinct.

## Uniformity is only one-sided

The `unif` field asks for `Kakeya.IsFlatPrismUniform`, not for the two-sided
`ShadedTube.ShadedUniformTubeSet` it used to ask for.  The two dropped clauses,
`le_card_shadeClass` and `branchingN_le`, are exactly the ones that do not survive passing to a
subfamily, and a producer of this package generally has them only at a larger index set; the two
retained ones do survive, so the demand can now be met by "project, then restrict"
(`Kakeya.IsFlatPrismUniform.of_shadedUniformTubeSet_subset`) with no re-uniformization and no
loss in the constant.  Nothing in this file reads a bracket, so the change is invisible here —
its cost is charged to `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`, whose docstring
records it.

Uniformity is carried as `Nonempty (…)` because the predicate is data-valued; since the
conclusion it feeds is a `Prop`, this loses nothing. -/
structure IsFlatPrismFamily {ι : Type*} {σ : NNReal} (η' : ℝ) (Cunif : NNReal) (s : Finset ι)
    (V : ι → ShadedTube σ E) : Prop where
  /-- The family is nonempty. -/
  nonempty : s.Nonempty
  /-- It is `C_unif`-uniform along the grid of Definition 2.2, in the **one-sided** sense: only
  the two clauses of GWZ Definition 2.2 that survive passing to a subfamily are asked for.  See
  the discussion above. -/
  unif : Nonempty (IsFlatPrismUniform s V (Tube.ssfGridLen σ) Cunif)
  /-- Its members lie in the unit ball. -/
  ball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1
  /-- Its members are pairwise essentially distinct.  Without this the conclusion is false for
  every `β > 0`; see the discussion above. -/
  essDistinct : (s : Set ι).Pairwise
    (fun i i' => IsEssentiallyDistinct (V i).carrier (V i').carrier)
  /-- `λ(𝕍, Z) ≥ σ ^ η'`: the fullness threshold below which the bound is vacuous. -/
  fullness : (σ : ENNReal) ^ η' ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)

/-- The pointwise cardinality estimate underlying the flat-prism loss envelope. -/
theorem flatPrism_card_le_rpow_neg_seven (hdim : Module.finrank ℝ E = 3)
    {δ σ : NNReal} (hδ0 : 0 < δ) (hδσ : δ ≤ σ)
    (hδC : (δ : ℝ) * Tube.card_le_of_EssDistinct.C 3 ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → Tube σ E)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise
      (fun i j ↦ IsEssentiallyDistinct (V i).carrier (V j).carrier)) :
    (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hσ0 : 0 < σ := hδ0.trans_le hδσ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hσR : 0 < (σ : ℝ) := by exact_mod_cast hσ0
  have hC0 : 0 ≤ Tube.card_le_of_EssDistinct.C 3 :=
    (Tube.card_le_of_EssDistinct.C_pos (n := 3)).le
  have hcard0 : (s.card : ℝ) ≤
      Tube.card_le_of_EssDistinct.C 3 * (1 / (σ : ℝ)) ^ 6 := by
    have h := Tube.card_le_of_EssDistinct (E := E) (δ := σ) hσ0 (1 : ℝ) s V hball hED
    rw [hdim] at h
    simpa using h
  have hinv : (1 : ℝ) / (σ : ℝ) ≤ (1 : ℝ) / (δ : ℝ) := by
    rw [div_le_div_iff₀ hσR hδR]
    simpa using (NNReal.coe_le_coe.mpr hδσ)
  have hpow : ((1 : ℝ) / (σ : ℝ)) ^ 6 ≤ ((1 : ℝ) / (δ : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hinv 6
  have hCinv : Tube.card_le_of_EssDistinct.C 3 ≤ (δ : ℝ)⁻¹ := by
    rw [← one_div, le_div_iff₀ hδR]
    simpa [mul_comm] using hδC
  calc
    (s.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C 3 * (1 / (σ : ℝ)) ^ 6 := hcard0
    _ ≤ Tube.card_le_of_EssDistinct.C 3 * (1 / (δ : ℝ)) ^ 6 := by gcongr
    _ ≤ (δ : ℝ)⁻¹ * (1 / (δ : ℝ)) ^ 6 := by gcongr
    _ = (δ : ℝ) ^ (-(7 : ℝ)) := by
      rw [one_div, ← pow_succ', ← Real.rpow_neg_one, ← Real.rpow_natCast,
        ← Real.rpow_mul hδR.le]
      congr 1
      norm_num

/-- Pairwise essentially distinct `σ`-tubes in the unit ball have cardinality at most
`σ⁻⁷`, eventually at the master scale. -/
theorem eventually_flatPrism_card_le_rpow_neg_seven
    (hdim : Module.finrank ℝ E = 3) :
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0, ∀ {ι : Type*} (s : Finset ι) (V : ι → Tube σ E),
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct (V i).carrier (V j).carrier) →
      (s.card : ℝ) ≤ (σ : ℝ) ^ (-(7 : ℝ)) := by
  let c : NNReal :=
    ⟨(Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹, by
      exact inv_nonneg.mpr (Tube.card_le_of_EssDistinct.C_pos (n := 3)).le⟩
  have hc : 0 < c := by
    change 0 < (Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast (Tube.card_le_of_EssDistinct.C_pos (n := 3)))
  apply Filter.eventually_of_mem (Ioo_mem_nhdsGT hc)
  intro σ hσ
  intro ι s V hball hED
  have hCpos : 0 < (Tube.card_le_of_EssDistinct.C 3 : ℝ) := by
    exact_mod_cast (Tube.card_le_of_EssDistinct.C_pos (n := 3))
  have hσC : (σ : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) ≤ 1 := by
    calc
      (σ : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) ≤
          (c : ℝ) * (Tube.card_le_of_EssDistinct.C 3 : ℝ) := by
        gcongr
        exact hσ.2.le
      _ = 1 := by
        change (Tube.card_le_of_EssDistinct.C 3 : ℝ)⁻¹ *
          (Tube.card_le_of_EssDistinct.C 3 : ℝ) = 1
        exact inv_mul_cancel₀ hCpos.ne'
  exact flatPrism_card_le_rpow_neg_seven hdim hσ.1 le_rfl hσC s V hball hED

/-! ### Aggregating the parentwise factorizations

Proposition 6.6(A) supplies one factorization on every fibre of the coarse-parent map.  Proposition
5.1 instead consumes one `FactorFamily`.  The definitions below form the dependent sum of all
parentwise parts.  The parent label is retained in the outer index even though two parts attached
to different coarse parents happen to be equal as finsets; this is essential because the
parentwise Katz--Tao and non-concentration estimates are proved separately before they are summed.
-/

/-- A used coarse parent, with its proof of membership in the coarse index set. -/
abbrev FlatPrismParent {κ : Type*} (t : Finset κ) := {k : κ // k ∈ t}

/-- The dependent sum of all parts in the parentwise factorizations. -/
abbrev FlatPrismBlock {ι κ : Type*} (t : Finset κ) :=
  Σ _ : FlatPrismParent t, Finset ι

/-- The coarse-parent data actually supplied by the Section 8 merge.

The assignment is a labelled parent map, not a geometric partition: a fine tube may lie in
several dilated coarse tubes.  What replaces uniqueness is pairwise essential distinctness of the
*assigned* parent family.  This is precisely the hypothesis used by
`Kakeya.edParentCount.card_assignedParents_le` to show that only a dimension-dependent number of
labels can contribute to a fixed plank-shaped test body.

No containment-fibre equality is asserted.  All factorizations below continue to use the
parent-map fibre `s.filter fun i => p i = k`. -/
structure FlatPrismParentPresentation {ι κ : Type*} {σ ρ D : NNReal}
    (s : Finset ι) (V : ι → ShadedTube σ E) (t : Finset κ)
    (Vρ : κ → Tube ρ E) (p : ι → κ) : Prop where
  /-- The fixed parent dilation is an enlargement. -/
  one_le : 1 ≤ D
  /-- Every selected fine index has an assigned selected parent. -/
  mapsTo : ∀ i ∈ s, p i ∈ t
  /-- Fine tubes lie in the fixed dilation of their assigned parent. -/
  le_parent_dilate : ∀ i ∈ s,
    (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) (D : ℝ)
  /-- The actual selected parent tubes are pairwise essentially distinct. -/
  pairwise : (t : Set κ).Pairwise fun k l =>
    IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier

section ParentwiseFactorFamily

variable [Nontrivial E] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {σ : NNReal} {s : Finset ι} {t : Finset κ}
  (V : ι → ShadedTube σ E) (p : ι → κ)
  (hp : ∀ i ∈ s, p i ∈ t)
  (Fz : ∀ k : FlatPrismParent t,
    ConvexSpaceBody.Factorization (s.filter fun i => p i = k.1)
      (fun i => (V i).toConvexSpaceBody) 2)
  (hs : s.Nonempty)

/-- A total parent assignment into the dependent sum.  Outside the active set it uses the part
of one fixed active tube; `FactorFamily` imposes no condition on those inactive values. -/
noncomputable def flatPrismBlockOf (i : ι) :
    FlatPrismBlock (ι := ι) t :=
  if hi : i ∈ s then
    let k : FlatPrismParent t := ⟨p i, hp i hi⟩
    ⟨k, (Fz k).part i⟩
  else
    let i₀ := hs.choose
    let k : FlatPrismParent t := ⟨p i₀, hp i₀ hs.choose_spec⟩
    ⟨k, (Fz k).part i₀⟩

/-- All parts in all used parentwise factorizations. -/
noncomputable def flatPrismBlocks :
    Finset (FlatPrismBlock (ι := ι) t) :=
  t.attach.sigma fun k => (Fz k).parts

/-- The convex hull represented by a dependent-sum block. -/
noncomputable def flatPrismBlockBody
    (x : FlatPrismBlock (ι := ι) t) : ConvexSpaceBody E :=
  x.2.convexHull_biUnion fun i => (V i).toConvexSpaceBody

omit [Nontrivial E] in
/-- The dependent-sum aggregation preserves the plank-dimension certificate supplied separately
on every coarse-parent factorization. -/
theorem flatPrismBlockBody_isPlankOfDimensions {Cw a b : NNReal}
    (hFz : ∀ k : FlatPrismParent t,
      IsPlankFamilyOfDimensions Cw a b (Fz k).parts
        (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)))
    (x : FlatPrismBlock (ι := ι) t) (hx : x ∈ flatPrismBlocks V p Fz) :
    IsPlankOfDimensions Cw a b (flatPrismBlockBody V x) := by
  obtain ⟨k, part⟩ := x
  have hpart : part ∈ (Fz k).parts := by
    simpa [flatPrismBlocks] using hx
  exact hFz k part hpart

/-- The dimensional upper-volume constant in the global block-cardinality ledger.  The factor
`2` is the factorization constant and `Tube.volume_le.C 3` is the upper volume of one fine tube. -/
noncomputable def flatPrismBlockCount.C : NNReal := 2 * Tube.volume_le.C 3

include hp in
/-- The number of plank blocks in all labelled parent fibres is paid for by the total fine-tube
carrier mass.  In division-free form,

`#blocks · c(Cw) · a b ≤ C_block · #s · σ²`.

This is stronger than merely summing the parentwise Katz--Tao count over parent labels.  It uses
`Factorization.maxDensity_le_mul` to force every part whose hull has `a × b × 1` dimensions to
carry its proportional share of fine-tube mass, and then uses that the parent-map fibres form an
exact partition of `s`. -/
theorem flatPrismBlocks_card_mul_volumeLower_le
    (hdim : Module.finrank ℝ E = 3) {Cw a b : NNReal} {hσ : 0 < σ}
    (hσ1 : σ ≤ 1)
    (hFz : ∀ k : FlatPrismParent t,
      IsPlankFamilyOfDimensions Cw a b (Fz k).parts
        (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))) :
    ((flatPrismBlocks V p Fz).card : ENNReal) *
        (((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((a : ENNReal) * (b : ENNReal))) ≤
      (flatPrismBlockCount.C : ENNReal) * (s.card : ENNReal) * (σ : ENNReal) ^ 2 := by
  let vmin : ENNReal := ((Cw : ENNReal) ^ 3)⁻¹ *
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * ((a : ENNReal) * (b : ENNReal))
  let vmax : ENNReal := (Tube.volume_le.C 3 : ENNReal) * (σ : ENNReal) ^ 2
  have hpos : ∀ i ∈ s, 0 < volume (V i).carrier := by
    intro i hi
    have hlo := Tube.le_volume (V i).toTube
    have hc0 : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)).ne'
    have hσe0 : (σ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hσ).ne'
    have hpow0 : (σ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
      pow_ne_zero _ hσe0
    have hlowpos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
        (σ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
      exact lt_of_le_of_ne zero_le (Ne.symm (mul_ne_zero hc0 hpow0))
    exact hlowpos.trans_le hlo
  have hupper : ∀ i ∈ s, volume (V i).carrier ≤ vmax := by
    intro i hi
    have hv := Tube.volume_le hσ1 (V i).toTube
    simpa only [vmax, hdim, Nat.reduceSub] using hv
  have hlower : ∀ k : FlatPrismParent t, ∀ part ∈ (Fz k).parts,
      vmin ≤ volume (part.convexHull_biUnion
        (fun i => (V i).toConvexSpaceBody)).carrier := by
    intro k part hpart
    exact (hFz k part hpart).volume_lower hdim
  have hk (k : FlatPrismParent t) :
      ((Fz k).parts.card : ENNReal) * vmin ≤
        2 * (((s.filter fun i => p i = k.1).card : ENNReal)) * vmax := by
    apply factorization_card_mul_volumeLower_le (Fz k)
    · intro i hi
      exact hpos i (Finset.mem_filter.mp hi).1
    · exact hlower k
    · intro i hi
      exact hupper i (Finset.mem_filter.mp hi).1
  change ((flatPrismBlocks V p Fz).card : ENNReal) * vmin ≤ _
  calc
    ((flatPrismBlocks V p Fz).card : ENNReal) * vmin =
        ∑ k ∈ t.attach, ((Fz k).parts.card : ENNReal) * vmin := by
      simp only [flatPrismBlocks, Finset.card_sigma, Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ k ∈ t.attach,
        2 * (((s.filter fun i => p i = k.1).card : ENNReal)) * vmax := by
      exact Finset.sum_le_sum fun k _ => hk k
    _ = 2 * (∑ k ∈ t.attach,
        ((s.filter fun i => p i = k.1).card : ENNReal)) * vmax := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_mul]
    _ = 2 * (s.card : ENNReal) * vmax := by
      congr 2
      calc
        ∑ k ∈ t.attach, ((s.filter fun i => p i = k.1).card : ENNReal) =
            ∑ k ∈ t, ((s.filter fun i => p i = k).card : ENNReal) := by
          simpa using (Finset.sum_attach t
            (fun k => ((s.filter fun i => p i = k).card : ENNReal)))
        _ = (s.card : ENNReal) := by
          exact_mod_cast (Finset.card_eq_sum_card_fiberwise hp).symm
    _ = (flatPrismBlockCount.C : ENNReal) * (s.card : ENNReal) * (σ : ENNReal) ^ 2 := by
      simp only [flatPrismBlockCount.C, vmax, ENNReal.coe_mul]
      norm_num
      ring

omit [Nontrivial E] in
/-- The true-container count available inside one labelled coarse-parent fibre.  This is the
division-free form of the `M θ` estimate: the factorization's Katz--Tao clause controls the sum
of the actual cell volumes in an arbitrary convex test body, while the two-sided plank dimensions
give the uniform lower volume of every retained cell.

The statement is deliberately parentwise.  Summing it over different values of the external
label `p` would require a separate bound on how many labelled coarse parents contribute to the
same test body; no such bound is asserted here. -/
theorem flatPrismParentBlock_count_mul_volumeLower_le {Cw a b : NNReal}
    (hdim : Module.finrank ℝ E = 3)
    (hFz : ∀ k : FlatPrismParent t,
      IsPlankFamilyOfDimensions Cw a b (Fz k).parts
        (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)))
    (k : FlatPrismParent t) (K : ConvexSpaceBody E) :
    ((((Fz k).parts.filter fun part =>
          part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) ≤ K).card : ENNReal) *
        (((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((a : ENNReal) * (b : ENNReal)))) ≤ 2 * volume K.carrier := by
  let selected := (Fz k).parts.filter fun part =>
    part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) ≤ K
  have hselected : selected ⊆ (Fz k).parts := Finset.filter_subset _ _
  have hKT : IsKatzTao selected
      (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))
      (2 : ENNReal) := (Fz k).isKatzTao.subset hselected
  have hsub : ∀ part ∈ selected,
      part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) ≤ K := by
    intro part hpart
    exact (Finset.mem_filter.mp hpart).2
  have hvol : ∀ part ∈ selected,
      ((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((a : ENNReal) * (b : ENNReal)) ≤
        volume (part.convexHull_biUnion
          (fun i => (V i).toConvexSpaceBody)).carrier := by
    intro part hpart
    exact (hFz k part (hselected hpart)).volume_lower hdim
  simpa only [selected] using hKT.card_mul_le hsub hvol

/-- The explicit constant in the parentwise absolute-neighbourhood count.  It depends only on
the plank dimension-comparison constant `Cw`: the factor `8 * (Cw + 1)^3` is the volume of the
`θ b` collar and the remaining factor `2` is the Katz--Tao constant of the factorization. -/
noncomputable def flatPrismParentNeighborhoodCount.C (Cw : NNReal) : NNReal :=
  16 * (Cw + 1) ^ 3

omit [Nontrivial E] in
/-- Parentwise `M θ` count in the actual absolute neighbourhood of an anchor cell.  The count is
written without division so it remains valid at zero parameters; in the intended positive-scale
regime, cancelling the common plank-volume lower bound gives a constant multiple of
`(b / a) * θ`.

This closes the geometry and Katz--Tao part *within one value of the external parent label*.  It
does not pool different labels. -/
theorem flatPrismParentBlock_count_cthickening_mul_volumeLower_le {Cw a b θ : NNReal}
    (hdim : Module.finrank ℝ E = 3)
    (hFz : ∀ k : FlatPrismParent t,
      IsPlankFamilyOfDimensions Cw a b (Fz k).parts
        (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)))
    (haθb : a ≤ θ * b) (hθ1 : θ ≤ 1) (hb1 : b ≤ 1)
    (k : FlatPrismParent t) (anchor : Finset ι) (hanchor : anchor ∈ (Fz k).parts) :
    ((((Fz k).parts.filter fun part =>
          part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) ≤
            (anchor.convexHull_biUnion
              (fun i => (V i).toConvexSpaceBody)).cthickening (θ * b)).card : ENNReal) *
        (((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((a : ENNReal) * (b : ENNReal)))) ≤
      (flatPrismParentNeighborhoodCount.C Cw : ENNReal) * (θ : ENNReal) *
        (b : ENNReal) ^ 2 := by
  let W := anchor.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)
  have hcount := flatPrismParentBlock_count_mul_volumeLower_le V p Fz hdim hFz k
    (W.cthickening (θ * b))
  have hW : IsPlankOfDimensions Cw a b W := hFz k anchor hanchor
  have hvol := hW.volume_cthickening_mul_le hdim haθb hθ1 hb1
  calc
    ((((Fz k).parts.filter fun part =>
          part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody) ≤
            W.cthickening (θ * b)).card : ENNReal) *
        (((Cw : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
          ((a : ENNReal) * (b : ENNReal)))) ≤
        2 * volume (W.cthickening (θ * b)).carrier := hcount
    _ ≤ 2 * (8 * ((Cw : ENNReal) + 1) ^ 3 * (θ : ENNReal) *
          (b : ENNReal) ^ 2) := by gcongr
    _ = (flatPrismParentNeighborhoodCount.C Cw : ENNReal) * (θ : ENNReal) *
        (b : ENNReal) ^ 2 := by
      simp only [flatPrismParentNeighborhoodCount.C, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_add, ENNReal.coe_ofNat]
      norm_num
      ring

omit [Nontrivial E] in
theorem flatPrismBlockOf_mem (i : ι) (hi : i ∈ s) :
    flatPrismBlockOf V p hp Fz hs i ∈ flatPrismBlocks V p Fz := by
  let k : FlatPrismParent t := ⟨p i, hp i hi⟩
  have hblock : flatPrismBlockOf V p hp Fz hs i = ⟨k, (Fz k).part i⟩ := by
    simp [flatPrismBlockOf, hi, k]
  rw [hblock]
  simp only [flatPrismBlocks, Finset.mem_sigma, Finset.mem_attach, true_and]
  exact (Fz k).part_mem.mpr (Finset.mem_filter.mpr ⟨hi, rfl⟩)

omit [Nontrivial E] in
theorem flatPrismTube_le_blockBody (i : ι) (hi : i ∈ s) :
    (V i).toConvexSpaceBody ≤
      flatPrismBlockBody V (flatPrismBlockOf V p hp Fz hs i) := by
  let k : FlatPrismParent t := ⟨p i, hp i hi⟩
  have hblock : flatPrismBlockOf V p hp Fz hs i = ⟨k, (Fz k).part i⟩ := by
    simp [flatPrismBlockOf, hi, k]
  rw [hblock]
  exact Finset.le_convexHull_biUnion (fun i => (V i).toConvexSpaceBody)
    ((Fz k).mem_part (Finset.mem_filter.mpr ⟨hi, rfl⟩))

/-- The single factor family to which corrected Proposition 5.1 is applied in Proposition
6.6(A). -/
noncomputable def flatPrismFactorFamily :
    ShadedBody.FactorFamily E ι (FlatPrismBlock (ι := ι) t) where
  innerSet := s
  innerBody := fun i => (V i).toShadedBody
  outerSet := flatPrismBlocks V p Fz
  outerBody := flatPrismBlockBody V
  parent := flatPrismBlockOf V p hp Fz hs
  parent_mem := flatPrismBlockOf_mem V p hp Fz hs
  inner_le_parent := flatPrismTube_le_blockBody V p hp Fz hs

omit [Nontrivial E] in
@[simp] theorem flatPrismFactorFamily_innerSet :
    (flatPrismFactorFamily V p hp Fz hs).innerSet = s := rfl

omit [Nontrivial E] in
@[simp] theorem flatPrismFactorFamily_innerBody :
    (flatPrismFactorFamily V p hp Fz hs).innerBody = fun i => (V i).toShadedBody := rfl

/-- The tube family is discretized at its own radius. -/
theorem flatPrismFactorFamily_innerDiscretized
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) :
    (flatPrismFactorFamily V p hp Fz hs).InnerIsDiscretizedAtScale σ where
  subset_unitBall := hball
  le_scale i _ := Tube.le_ethickness_scale (V i).toTube

omit [Nontrivial E] in
/-- Equal-radius tubes have comparable affine thicknesses, so the aggregated family satisfies
the shape hypothesis of corrected Proposition 5.1. -/
theorem flatPrismFactorFamily_innerHasSimilarShape (hσ : (σ : ℝ) ≤ 1 / 2) :
    (flatPrismFactorFamily V p hp Fz hs).InnerHasSimilarShape 2 := by
  intro i _ i' _ n
  exact Tube.thickness_le_two_mul_thickness hσ (V i).toTube (V i').toTube n

omit [Nontrivial E] in
/-- Every aggregate block stays in the coarse tube containing its parent-map fibre. -/
theorem flatPrismBlockBody_le_coarseTube {ρ : NNReal} (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody)
    (x : FlatPrismBlock (ι := ι) t)
    (hx : x ∈ flatPrismBlocks V p Fz) :
    flatPrismBlockBody V x ≤ (Vρ x.1).toConvexSpaceBody := by
  obtain ⟨k, part⟩ := x
  have hpart : part ∈ (Fz k).parts := by
    simpa [flatPrismBlocks] using hx
  refine ((Fz k).nonempty_of_mem_parts hpart).convexHull_biUnion_le_iff
    (fun i => (V i).toConvexSpaceBody) (Vρ k.1).toConvexSpaceBody |>.2 ?_
  intro i hi
  have hiFiber := (Fz k).le hpart hi
  have hi' := Finset.mem_filter.mp hiFiber
  simpa [hi'.2] using hle i hi'.1

omit [Nontrivial E] in
/-- Every aggregate block stays in the fixed dilation of its assigned coarse parent.

This is the form used after Section 8 deduplicates the parent family.  It still uses only the
parent-map fibre; no containment-fibre equality or geometric uniqueness is introduced. -/
theorem flatPrismBlockBody_le_parentDilate {ρ D : NNReal} (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s,
      (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) (D : ℝ))
    (x : FlatPrismBlock (ι := ι) t)
    (hx : x ∈ flatPrismBlocks V p Fz) :
    flatPrismBlockBody V x ≤ Tube.dilate (Vρ x.1) (D : ℝ) := by
  obtain ⟨k, part⟩ := x
  have hpart : part ∈ (Fz k).parts := by
    simpa [flatPrismBlocks] using hx
  refine ((Fz k).nonempty_of_mem_parts hpart).convexHull_biUnion_le_iff
    (fun i => (V i).toConvexSpaceBody) (Tube.dilate (Vρ k.1) (D : ℝ)) |>.2 ?_
  intro i hi
  have hiFiber := (Fz k).le hpart hi
  have hi' := Finset.mem_filter.mp hiFiber
  simpa [hi'.2] using hle i hi'.1

/-- A fixed dilation of a `ρ`-tube in dimension three has volume at most
`D³ C_volume`, uniformly for `ρ ≤ 1`.

Unlike `Tube.tubeDilateVolume`, this statement includes the edge cases `D = 0` and `D = 1`; it
uses the underlying Haar-measure homothety identity directly. -/
theorem flatPrismTubeDilate_volume_le {ρ D : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hρ1 : ρ ≤ 1) (T : Tube ρ E) :
    volume (Tube.dilate T (D : ℝ)).carrier ≤
      (D : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal) := by
  have hvolEq : volume (Tube.dilate T (D : ℝ)).carrier =
      (D : ENNReal) ^ 3 * volume T.carrier := by
    rw [Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety]
    rw [hdim]
    simp [abs_of_nonneg (NNReal.coe_nonneg D), ENNReal.ofReal_pow]
  rw [hvolEq]
  have hvol := Tube.volume_le hρ1 T
  rw [hdim] at hvol
  calc
    (D : ENNReal) ^ 3 * volume T.carrier ≤
        (D : ENNReal) ^ 3 *
          ((Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2) := by gcongr
    _ ≤ (D : ENNReal) ^ 3 * ((Tube.volume_le.C 3 : ENNReal) * 1) := by
      gcongr
      exact pow_le_one₀ (by positivity) (by exact_mod_cast hρ1)
    _ = (D : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal) := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- A body contained in the `D`-dilate of a `ρ`-tube has shortest scale at most `2D` when
`ρ ≤ 1`. -/
theorem scale_le_two_mul_of_le_tube_dilate {ρ D : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hρ1 : ρ ≤ 1) (T : Tube ρ E)
    (W : ConvexSpaceBody E) (hsub : W ≤ Tube.dilate T (D : ℝ)) : W.scale ≤ 2 * D := by
  have hzero : 0 < Module.finrank ℝ E := by omega
  have hescale : Metric.ethickness.scale ℝ W.carrier ≤ (D : ENNReal) * 2 :=
    (Metric.ethickness.scale_le _ hzero).trans
      ((Metric.ethickness_monotone hsub 0).trans <| by
        calc
          Metric.ethickness ℝ (Tube.dilate T (D : ℝ)).carrier 0
              ≤ (D : ENNReal) * Metric.ethickness ℝ T.carrier 0 := by
            rw [Tube.dilate_carrier]
            simpa using
              Metric.ethickness_homothety_image_le T.center (D : ℝ) T.carrier 0
          _ ≤ (D : ENNReal) * 2 := by
            gcongr
            exact Tube.ethickness_zero_le_two hρ1 T)
  rw [ConvexSpaceBody.ethickness_scale_eq_ofReal_scale] at hescale
  change W.scale ≤ ((2 * D : NNReal) : ℝ)
  have htarget : ENNReal.ofReal W.scale ≤ ENNReal.ofReal (((2 * D : NNReal) : ℝ)) := by
    simpa [ENNReal.coe_mul, mul_comm] using hescale
  exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg (2 * D))).mp htarget

omit [Nontrivial E] in
/-- Every aggregate block lies in the same convex window as all of its constituent fine
bodies.  Unlike `flatPrismBlockBody_le_coarseTube`, this statement does not use the coarse
parent tube and is the form needed for the global outer Frostman transfer. -/
theorem flatPrismBlockBody_le_of_inner_le (K : ConvexSpaceBody E)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ K)
    (x : FlatPrismBlock (ι := ι) t)
    (hx : x ∈ flatPrismBlocks V p Fz) :
    flatPrismBlockBody V x ≤ K := by
  obtain ⟨k, part⟩ := x
  have hpart : part ∈ (Fz k).parts := by
    simpa [flatPrismBlocks] using hx
  refine ((Fz k).nonempty_of_mem_parts hpart).convexHull_biUnion_le_iff
    (fun i ↦ (V i).toConvexSpaceBody) K |>.2 ?_
  intro i hi
  exact hle i (Finset.mem_filter.mp ((Fz k).le hpart hi)).1

/-- The aggregate outer hulls have a finite dyadic volume ratio to their fine tubes.  The
outer bound comes from containment in a coarse tube of radius at most one; the inner lower
bound is the standard discretized-body volume estimate. -/
noncomputable def flatPrismFactorFamily_volumeRatio {ρ : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hσ : 0 < σ) (hρ1 : ρ ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody) :
    ShadedBody.OuterInnerVolumeRatio (flatPrismFactorFamily V p hp Fz hs) := by
  classical
  letI : DecidableEq (FlatPrismBlock (ι := ι) t) :=
    Classical.typeDecidableEq _
  let outerBound : ENNReal := Tube.volume_le.C 3
  let innerBound : ENNReal :=
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * (σ : ENNReal) ^ (3 : ℕ)
  apply ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds
    (flatPrismFactorFamily V p hp Fz hs) outerBound innerBound
  · intro x hx
    calc
      volume (flatPrismBlockBody V x).carrier
          ≤ volume (Vρ x.1).carrier :=
        measure_mono (flatPrismBlockBody_le_coarseTube V p Fz Vρ hle x hx)
      _ ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
          (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) := Tube.volume_le hρ1 (Vρ x.1)
      _ ≤ outerBound := by
        simp only [hdim, Nat.reduceSub, outerBound]
        have hρe : (ρ : ENNReal) ≤ 1 := by exact_mod_cast hρ1
        calc
          (Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2
              ≤ (Tube.volume_le.C 3 : ENNReal) * 1 :=
            mul_le_mul_right (pow_le_one₀ bot_le hρe) _
          _ = Tube.volume_le.C 3 := mul_one _
  · intro j _ i hi
    rw [ShadedBody.FactorFamily.fiber] at hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hvol :=
      (flatPrismFactorFamily_innerDiscretized V p hp Fz hs hball).volume_innerBody_mem_Icc his
    simpa only [flatPrismFactorFamily_innerBody, hdim, innerBound] using hvol.1
  · exact ENNReal.coe_ne_top
  · positivity
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- The volume-ratio input for scale selection when the assigned parent relation is available
only up to a fixed dilation `D`. -/
noncomputable def flatPrismFactorFamily_volumeRatio_dilate {ρ D : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hσ : 0 < σ) (hρ1 : ρ ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s,
      (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) (D : ℝ)) :
    ShadedBody.OuterInnerVolumeRatio (flatPrismFactorFamily V p hp Fz hs) := by
  classical
  letI : DecidableEq (FlatPrismBlock (ι := ι) t) :=
    Classical.typeDecidableEq _
  let outerBound : ENNReal := (D : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal)
  let innerBound : ENNReal :=
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * (σ : ENNReal) ^ (3 : ℕ)
  apply ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds
    (flatPrismFactorFamily V p hp Fz hs) outerBound innerBound
  · intro x hx
    calc
      volume (flatPrismBlockBody V x).carrier
          ≤ volume (Tube.dilate (Vρ x.1) (D : ℝ)).carrier :=
        measure_mono (flatPrismBlockBody_le_parentDilate V p Fz Vρ hle x hx)
      _ ≤ outerBound := flatPrismTubeDilate_volume_le hdim hρ1 (Vρ x.1)
  · intro j _ i hi
    rw [ShadedBody.FactorFamily.fiber] at hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hvol :=
      (flatPrismFactorFamily_innerDiscretized V p hp Fz hs hball).volume_innerBody_mem_Icc his
    simpa only [flatPrismFactorFamily_innerBody, hdim, innerBound] using hvol.1
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ENNReal.coe_ne_top
  · positivity
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-- A family-independent upper bound for the dimension-three outer/inner volume ratio after
the master-scale factor `σ⁻³` has been removed. -/
noncomputable def flatPrismVolumeRatioBase (D : NNReal) : NNReal :=
  max 1 (D ^ 3 * Tube.volume_le.C 3 / Metric.lt_volume_convexHull.c 3)

/-- The explicit dyadic exponent used for the flat-prism volume-ratio input. -/
noncomputable def flatPrismVolumeRatioExponent (D σ : NNReal) : ℕ :=
  Nat.ceil (Real.logb 2
    ((flatPrismVolumeRatioBase D : ℝ) * (σ : ℝ) ^ (-(3 : ℝ))))

/-- Constant controlling the explicit dyadic volume exponent by `1 + log₂(1 / σ)`. -/
noncomputable def flatPrismVolumeRatioExponent.C (D : NNReal) : NNReal :=
  Real.toNNReal (Real.logb 2 (flatPrismVolumeRatioBase D : ℝ) + 5)

/-- The explicit flat-prism volume exponent grows at most logarithmically in the inverse master
scale. -/
theorem flatPrismVolumeRatioExponent_add_one_le (D : NNReal) {σ : NNReal}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : NNReal) ≤
      flatPrismVolumeRatioExponent.C D *
        Real.toNNReal (1 + Real.logb 2 (1 / (σ : ℝ))) := by
  have hbase1 : (1 : NNReal) ≤ flatPrismVolumeRatioBase D := le_max_left _ _
  have hbasepos : (0 : ℝ) < flatPrismVolumeRatioBase D := by
    exact_mod_cast zero_lt_one.trans_le hbase1
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hσ1R : (σ : ℝ) ≤ 1 := by exact_mod_cast hσ1
  let L : ℝ := Real.logb 2 (1 / (σ : ℝ))
  have hL0 : 0 ≤ L := by
    dsimp [L]
    apply Real.logb_nonneg (by norm_num)
    rw [one_le_div hσR]
    exact hσ1R
  have hbaseLog0 : 0 ≤ Real.logb 2 (flatPrismVolumeRatioBase D : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hbase1)
  have hxpos : 0 < (flatPrismVolumeRatioBase D : ℝ) * (σ : ℝ) ^ (-(3 : ℝ)) := by
    positivity
  have hxnonneg : 0 ≤ Real.logb 2
      ((flatPrismVolumeRatioBase D : ℝ) * (σ : ℝ) ^ (-(3 : ℝ))) :=
    Real.logb_nonneg (by norm_num) (by
      have hpow1 : (1 : ℝ) ≤ (σ : ℝ) ^ (-(3 : ℝ)) := by
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hσR hσ1R (by norm_num)
      nlinarith [show (1 : ℝ) ≤ flatPrismVolumeRatioBase D by exact_mod_cast hbase1])
  have hceil := Nat.ceil_lt_add_one hxnonneg
  have hlogσ : Real.logb 2 ((σ : ℝ) ^ (-(3 : ℝ))) = 3 * L := by
    rw [Real.logb_rpow_eq_mul_logb_of_pos hσR]
    have hinv : Real.logb 2 (σ : ℝ) = -L := by
      dsimp [L]
      rw [one_div, Real.logb_inv]
      ring
    rw [hinv]
    ring
  have hlogmul : Real.logb 2
      ((flatPrismVolumeRatioBase D : ℝ) * (σ : ℝ) ^ (-(3 : ℝ))) =
      Real.logb 2 (flatPrismVolumeRatioBase D : ℝ) + 3 * L := by
    rw [Real.logb_mul hbasepos.ne' (by positivity : (σ : ℝ) ^ (-(3 : ℝ)) ≠ 0),
      hlogσ]
  have hreal : ((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : ℝ) ≤
      (Real.logb 2 (flatPrismVolumeRatioBase D : ℝ) + 5) * (1 + L) := by
    have hceil' : (flatPrismVolumeRatioExponent D σ : ℝ) <
        Real.logb 2 (flatPrismVolumeRatioBase D : ℝ) + 3 * L + 1 := by
      simpa only [flatPrismVolumeRatioExponent, hlogmul] using hceil
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg hbaseLog0 hL0]
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [flatPrismVolumeRatioExponent.C, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by linarith)]
  norm_num only [Nat.cast_add, Nat.cast_one] at hreal
  simpa only [L] using hreal

/-- The explicit volume-ratio exponent is logarithmic and hence subpolynomial in the master
scale.  This is the family-independent exponent envelope used by the Proposition 5.1 loss
ledger. -/
theorem eventually_flatPrismVolumeRatioExponent_add_one_le_rpow_neg
    (D : NNReal) {e : ℝ} (he : 0 < e) :
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0,
      ((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : ENNReal) ≤
        (σ : ENNReal) ^ (-e) := by
  let C : ENNReal := max 1 (flatPrismVolumeRatioExponent.C D : ENNReal)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCtop : C ≠ ⊤ := by simp [C]
  have he2 : 0 < e / 2 := by positivity
  filter_upwards [ShadedBody.eventually_const_le_coe_rpow_neg hC1 hCtop he2,
    ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg he2 1]
      with σ hconst hlog
  have hσ : 0 < σ := hconst.1
  have hσ1 : σ ≤ 1 := hconst.2.1
  have hN := flatPrismVolumeRatioExponent_add_one_le D hσ hσ1
  have hN' : ((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : ENNReal) ≤
      C * ENNReal.ofReal (1 + Real.logb 2 (1 / (σ : ℝ))) := by
    calc
      ((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : ENNReal) =
          ((((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : NNReal) : ENNReal)) := by
            norm_cast
      _ ≤ ((flatPrismVolumeRatioExponent.C D *
          Real.toNNReal (1 + Real.logb 2 (1 / (σ : ℝ))) : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hN
      _ = (flatPrismVolumeRatioExponent.C D : ENNReal) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (σ : ℝ))) := by
        rw [ENNReal.coe_mul]
        exact congrArg ((flatPrismVolumeRatioExponent.C D : ENNReal) * ·)
          (ENNReal.ofNNReal_toNNReal _)
      _ ≤ C * ENNReal.ofReal (1 + Real.logb 2 (1 / (σ : ℝ))) := by
        gcongr
        exact le_max_right _ _
  calc
    ((flatPrismVolumeRatioExponent D σ + 1 : ℕ) : ENNReal) ≤
        C * ENNReal.ofReal (1 + Real.logb 2 (1 / (σ : ℝ))) := hN'
    _ ≤ (σ : ENNReal) ^ (-(e / 2)) * (σ : ENNReal) ^ (-(e / 2)) := by
      gcongr
      · exact hconst.2.2
      · simpa using hlog
    _ = (σ : ENNReal) ^ (-e) := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne') ENNReal.coe_ne_top]
      congr 1
      ring

/-- The flat-prism factor family with an explicit, logarithmically controlled dyadic volume
exponent. -/
noncomputable def flatPrismFactorFamily_volumeRatio_dilate_controlled {ρ D : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s,
      (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) (D : ℝ)) :
    ShadedBody.OuterInnerVolumeRatio (flatPrismFactorFamily V p hp Fz hs) := by
  classical
  letI : DecidableEq (FlatPrismBlock (ι := ι) t) := Classical.typeDecidableEq _
  let outerBound : ENNReal := (D : ENNReal) ^ 3 * (Tube.volume_le.C 3 : ENNReal)
  let innerBound : ENNReal :=
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * (σ : ENNReal) ^ (3 : ℕ)
  let N := flatPrismVolumeRatioExponent D σ
  apply ShadedBody.OuterInnerVolumeRatio.ofVolumeBounds
    (flatPrismFactorFamily V p hp Fz hs) N outerBound innerBound
  · intro x hx
    calc
      volume (flatPrismBlockBody V x).carrier
          ≤ volume (Tube.dilate (Vρ x.1) (D : ℝ)).carrier :=
        measure_mono (flatPrismBlockBody_le_parentDilate V p Fz Vρ hle x hx)
      _ ≤ outerBound := flatPrismTubeDilate_volume_le hdim hρ1 (Vρ x.1)
  · intro j _ i hi
    rw [ShadedBody.FactorFamily.fiber] at hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hvol :=
      (flatPrismFactorFamily_innerDiscretized V p hp Fz hs hball).volume_innerBody_mem_Icc his
    simpa only [flatPrismFactorFamily_innerBody, hdim, innerBound] using hvol.1
  · have hbase : D ^ 3 * Tube.volume_le.C 3 / Metric.lt_volume_convexHull.c 3 ≤
        flatPrismVolumeRatioBase D := le_max_right _ _
    have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
    have hσ1R : (σ : ℝ) ≤ 1 := by exact_mod_cast hσ1
    have hbase1 : (1 : NNReal) ≤ flatPrismVolumeRatioBase D := le_max_left _ _
    have hxpos : 0 < (flatPrismVolumeRatioBase D : ℝ) *
        (σ : ℝ) ^ (-(3 : ℝ)) := by positivity
    have hx1 : 1 ≤ (flatPrismVolumeRatioBase D : ℝ) *
        (σ : ℝ) ^ (-(3 : ℝ)) := by
      have hpow1 : (1 : ℝ) ≤ (σ : ℝ) ^ (-(3 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hσR hσ1R (by norm_num)
      nlinarith [show (1 : ℝ) ≤ flatPrismVolumeRatioBase D by exact_mod_cast hbase1]
    have hlog0 := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hx1
    have hceil : Real.logb 2 ((flatPrismVolumeRatioBase D : ℝ) *
        (σ : ℝ) ^ (-(3 : ℝ))) ≤ (N : ℝ) := by
      exact Nat.le_ceil _
    have hxpow : (flatPrismVolumeRatioBase D : ℝ) *
        (σ : ℝ) ^ (-(3 : ℝ)) ≤ (2 : ℝ) ^ (N : ℝ) :=
      (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hxpos).mp hceil
    have hratioNN : D ^ 3 * Tube.volume_le.C 3 /
        (Metric.lt_volume_convexHull.c 3 * σ ^ (3 : ℕ)) ≤ (2 ^ N : NNReal) := by
      rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_rpow]
      calc
        (D : ℝ) ^ 3 * (Tube.volume_le.C 3 : ℝ) /
            ((Metric.lt_volume_convexHull.c 3 : ℝ) * (σ : ℝ) ^ 3) =
            ((D : ℝ) ^ 3 * (Tube.volume_le.C 3 : ℝ) /
              (Metric.lt_volume_convexHull.c 3 : ℝ)) * (σ : ℝ) ^ (-(3 : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hσR)]
          field_simp [hσR.ne', (Metric.lt_volume_convexHull.c_pos 3).ne']
          all_goals norm_num [Real.rpow_natCast]
        _ ≤ (flatPrismVolumeRatioBase D : ℝ) * (σ : ℝ) ^ (-(3 : ℝ)) := by
          gcongr
          exact_mod_cast hbase
        _ ≤ (2 : ℝ) ^ (N : ℝ) := hxpow
        _ = (2 ^ N : NNReal) := by simp
    apply (ENNReal.div_le_iff (by positivity : innerBound ≠ 0)
      (by finiteness : innerBound ≠ ⊤)).mp
    have hden : Metric.lt_volume_convexHull.c 3 * σ ^ (3 : ℕ) ≠ 0 := by positivity
    have hcast := ENNReal.coe_le_coe.mpr hratioNN
    rw [ENNReal.coe_div hden, ENNReal.coe_mul, ENNReal.coe_pow,
      ENNReal.coe_mul, ENNReal.coe_pow] at hcast
    simpa only [outerBound, innerBound, Tube.volume_le.C, ENNReal.coe_pow,
      ENNReal.coe_ofNat] using hcast

/-- The explicit volume-ratio construction records the advertised logarithmic exponent. -/
theorem flatPrismFactorFamily_volumeRatio_dilate_controlled_exponent {ρ D : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s,
      (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) (D : ℝ)) :
    (flatPrismFactorFamily_volumeRatio_dilate_controlled V p hp Fz hs hdim hσ hσ1 hρ1
      hball Vρ hle).exponent = flatPrismVolumeRatioExponent D σ := by
  simp only [flatPrismFactorFamily_volumeRatio_dilate_controlled,
    ShadedBody.OuterInnerVolumeRatio.ofVolumeBounds_exponent]

/-- All aggregate outer bodies have shortest scale at most `2` when their containing coarse
tubes have radius at most `1`.  This is the uniform upper endpoint used by scale selection. -/
theorem flatPrismFactorFamily_outerScale_le_two {ρ : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hρ1 : ρ ≤ 1) (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody) :
    ∀ x ∈ (flatPrismFactorFamily V p hp Fz hs).innerSet.image
      (flatPrismFactorFamily V p hp Fz hs).parent,
      ((flatPrismFactorFamily V p hp Fz hs).outerBody x).scale ≤ (2 : NNReal) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hxmem := flatPrismBlockOf_mem V p hp Fz hs i hi
  have hsub := flatPrismBlockBody_le_coarseTube V p Fz Vρ hle
    (flatPrismBlockOf V p hp Fz hs i) hxmem
  have hzero : 0 < Module.finrank ℝ E := by omega
  have hescale : Metric.ethickness.scale ℝ
      (flatPrismBlockBody V (flatPrismBlockOf V p hp Fz hs i)).carrier ≤ 2 :=
    (Metric.ethickness.scale_le _ hzero).trans
      ((Metric.ethickness_monotone hsub 0).trans (Tube.ethickness_zero_le_two hρ1 _))
  have hscale0 : 0 ≤
      (flatPrismBlockBody V (flatPrismBlockOf V p hp Fz hs i)).scale :=
    Metric.thickness_nonneg _ _
  rw [ConvexSpaceBody.ethickness_scale_eq_ofReal_scale] at hescale
  change (flatPrismBlockBody V (flatPrismBlockOf V p hp Fz hs i)).scale ≤ (2 : ℝ)
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp (by simpa using hescale)

/-- Dilated-parent form of `flatPrismFactorFamily_outerScale_le_two`.  The scale-selection upper
endpoint changes from `2` to the explicit fixed bound `2D`. -/
theorem flatPrismFactorFamily_outerScale_le_two_mul {ρ D : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hρ1 : ρ ≤ 1) (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s,
      (V i).toConvexSpaceBody ≤ Tube.dilate (Vρ (p i)) (D : ℝ)) :
    ∀ x ∈ (flatPrismFactorFamily V p hp Fz hs).innerSet.image
      (flatPrismFactorFamily V p hp Fz hs).parent,
      ((flatPrismFactorFamily V p hp Fz hs).outerBody x).scale ≤ 2 * D := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have his : i ∈ s := by
    simpa only [flatPrismFactorFamily_innerSet] using hi
  have hxmem := flatPrismBlockOf_mem V p hp Fz hs i his
  have hsub := flatPrismBlockBody_le_parentDilate V p Fz Vρ hle
    (flatPrismBlockOf V p hp Fz hs i) hxmem
  have hfirst : (flatPrismBlockOf V p hp Fz hs i).1.1 = p i := by
    simp [flatPrismBlockOf, his]
  rw [hfirst] at hsub
  apply scale_le_two_mul_of_le_tube_dilate hdim hρ1 (Vρ (p i))
  exact hsub

omit [Nontrivial E] in
/-- Fibres of the aggregated family inherit the Frostman clause of their original
factorization, with the factorization constant `2`. -/
theorem flatPrismFactorFamily_hasFrostmanFibers :
    (flatPrismFactorFamily V p hp Fz hs).HasFrostmanFibers 2 := by
  intro x hx
  obtain ⟨k, part⟩ := x
  have hpart : part ∈ (Fz k).parts := by
    simpa [flatPrismFactorFamily, flatPrismBlocks] using hx
  have hfiber : (flatPrismFactorFamily V p hp Fz hs).fiber ⟨k, part⟩ = part := by
    ext i
    simp only [ShadedBody.FactorFamily.fiber, flatPrismFactorFamily_innerSet,
      Finset.mem_filter]
    constructor
    · rintro ⟨hi, hparent⟩
      change flatPrismBlockOf V p hp Fz hs i = ⟨k, part⟩ at hparent
      have hk : (⟨p i, hp i hi⟩ : FlatPrismParent t) = k := by
        have hfst := congrArg Sigma.fst hparent
        simpa [flatPrismBlockOf, hi] using hfst
      have hpi : p i = k.1 := congrArg Subtype.val hk
      have hpartEq : (Fz k).part i = part := by
        subst k
        have hsnd := congrArg Sigma.snd hparent
        simpa [flatPrismBlockOf, hi] using hsnd
      rw [← hpartEq]
      exact (Fz k).mem_part (Finset.mem_filter.mpr ⟨hi, hpi⟩)
    · intro hipart
      have hiFiber : i ∈ s.filter fun i => p i = k.1 :=
        (Fz k).le hpart hipart
      have hi := (Finset.mem_filter.mp hiFiber).1
      have hpi := (Finset.mem_filter.mp hiFiber).2
      refine ⟨hi, ?_⟩
      have hpartEq : (Fz k).part i = part := (Fz k).part_eq_of_mem hpart hipart
      change flatPrismBlockOf V p hp Fz hs i = ⟨k, part⟩
      have hk : (⟨p i, hp i hi⟩ : FlatPrismParent t) = k := Subtype.ext hpi
      subst k
      simp [flatPrismBlockOf, hi, hpartEq]
  change ConvexSpaceBody.IsFrostmanIn
    ((flatPrismFactorFamily V p hp Fz hs).fiber ⟨k, part⟩)
      (fun i => (V i).toConvexSpaceBody) (flatPrismBlockBody V ⟨k, part⟩) 2
  rw [hfiber]
  exact (Fz k).isFrostman part hpart

omit [Nontrivial E] in
/-- The density-selected aggregate blocks inherit global Frostman control with the explicit
selection/fullness loss.  This is the correct replacement for the false claim that Frostman
control restricts to the selected fine subfamily without loss. -/
theorem flatPrismSelectedOuter_isFrostmanIn
    {K : ConvexSpaceBody E} {C : ENNReal}
    (hFr : IsFrostmanIn s (fun i ↦ (V i).toConvexSpaceBody) K C)
    (hVpos : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hVK : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ K)
    {hσ : 0 < σ}
    (hdisc : (flatPrismFactorFamily V p hp Fz hs).InnerIsDiscretizedAtScale σ)
    (D : ShadedBody.OuterInnerVolumeRatio (flatPrismFactorFamily V p hp Fz hs))
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade)
    (R : ShadedBody.OuterDensitySelection (flatPrismFactorFamily V p hp Fz hs)
      hσ hdisc D (by simpa using hmass)) :
    IsFrostmanIn R.selected (flatPrismBlockBody V) K
      (2 * (C * (ShadedBody.outerDensitySelectionConstant s.card D.exponent : ENNReal) *
        ((ShadedBody.fullness s (fun i ↦ (V i).toShadedBody) : NNReal) : ENNReal)⁻¹)) := by
  let F := flatPrismFactorFamily V p hp Fz hs
  have hmassF : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
    simpa only [F, flatPrismFactorFamily_innerSet, flatPrismFactorFamily_innerBody] using hmass
  have hWK : ∀ j ∈ R.selected, F.outerBody j ≤ K := by
    intro j hj
    exact flatPrismBlockBody_le_of_inner_le V p Fz K hVK j
      (R.selected_subset.trans F.innerSet_image_parent_subset_outerSet hj)
  simpa only [F, flatPrismFactorFamily, flatPrismFactorFamily_innerSet,
    flatPrismFactorFamily_innerBody] using
      R.outer_isFrostmanIn F hσ hdisc D hmassF
        hFr hVpos hVK hWK

/-- The corrected Proposition 5.1, applied to the dependent sum of all parentwise flat-prism
factorizations.  Scale selection is essential here: different coarse parents need not produce
blocks with comparable shortest widths. -/
theorem flatPrismCoreSelectScale {ρ : NNReal}
    (hdim : Module.finrank ℝ E = 3) (hσ : 0 < σ) (hσhalf : (σ : ℝ) ≤ 1 / 2)
    (hσ2 : σ ≤ 2) (hρ1 : ρ ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (Vρ : κ → Tube ρ E)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    ShadedBody.FactoringAndMultPropCoreSelectScaleResult (C := 2)
      (flatPrismFactorFamily V p hp Fz hs) hσ
      (flatPrismFactorFamily_innerDiscretized V p hp Fz hs hball)
      (flatPrismFactorFamily_volumeRatio V p hp Fz hs hdim hσ hρ1 hball Vρ hle)
      hσ2 (flatPrismFactorFamily_outerScale_le_two V p hp Fz hs hdim hρ1 Vρ hle)
      (by
        simpa only [flatPrismFactorFamily_innerSet, flatPrismFactorFamily_innerBody] using hmass) :=
  ShadedBody.factoringAndMultPropCoreSelectScale
    (flatPrismFactorFamily V p hp Fz hs) hσ
    (flatPrismFactorFamily_innerDiscretized V p hp Fz hs hball)
    (flatPrismFactorFamily_volumeRatio V p hp Fz hs hdim hσ hρ1 hball Vρ hle)
    hσ2 (flatPrismFactorFamily_outerScale_le_two V p hp Fz hs hdim hρ1 Vρ hle)
    (by simpa only [flatPrismFactorFamily_innerSet, flatPrismFactorFamily_innerBody] using hmass)
    hdim (flatPrismFactorFamily_innerHasSimilarShape V p hp Fz hs hσhalf)
    (flatPrismFactorFamily_hasFrostmanFibers V p hp Fz hs)

end ParentwiseFactorFamily

/-- In the regime where the plank's shortest width is not too small relative to the tube scale,
the plank-ratio gain is paid for by half of the allowed small-scale loss.  This is the elementary
large-width branch of Proposition 6.6(A); it leaves the remaining factors in the abstract term
`X`, so the lemma is independent of the analytic estimate used to produce them. -/
theorem flatPrismLargeWidth_absorb {σ a b : NNReal} {β ε : ℝ} {μ X : ENNReal}
    (hσ : 0 < σ) (hβ : 0 < β) (hε : 0 < ε) (hσa : σ ≤ a)
    (hab : a ≤ b) (hb1 : b ≤ 1) (hlarge : σ ^ (ε / (3 * β)) ≤ a)
    (hμ : μ ≤ (σ : ENNReal) ^ (-(ε / 2)) * X) :
    μ ≤ (σ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * X := by
  have ha : 0 < a := hσ.trans_le hσa
  have hb : 0 < b := ha.trans_le hab
  have hσ0 : (σ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hσ.ne'
  have hσtop : (σ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb0 : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
  have hbtop : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have habdiv : (a : ENNReal) ≤ (a : ENNReal) / (b : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbtop)).2
    calc
      (a : ENNReal) * (b : ENNReal) ≤ (a : ENNReal) * 1 := by
        gcongr
        exact_mod_cast hb1
      _ = (a : ENNReal) := mul_one _
  have hlargeE : (σ : ENNReal) ^ (ε / (3 * β)) ≤ (a : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hσ.ne']
    exact_mod_cast hlarge
  have hpow : (σ : ENNReal) ^ (ε / 2) ≤
      ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) := by
    have hp : 0 ≤ 3 * β / 2 := by positivity
    calc
      (σ : ENNReal) ^ (ε / 2) =
          ((σ : ENNReal) ^ (ε / (3 * β))) ^ (3 * β / 2) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp [hβ.ne']
      _ ≤ (a : ENNReal) ^ (3 * β / 2) := ENNReal.rpow_le_rpow hlargeE hp
      _ ≤ ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) :=
        ENNReal.rpow_le_rpow habdiv hp
  have hloss : (σ : ENNReal) ^ (-(ε / 2)) ≤
      (σ : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) := by
    calc
      (σ : ENNReal) ^ (-(ε / 2)) =
          (σ : ENNReal) ^ (-ε) * (σ : ENNReal) ^ (ε / 2) := by
        rw [← ENNReal.rpow_add _ _ hσ0 hσtop]
        congr 1
        ring
      _ ≤ (σ : ENNReal) ^ (-ε) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) := by gcongr
  exact hμ.trans (by
    calc
      (σ : ENNReal) ^ (-(ε / 2)) * X ≤
          ((σ : ENNReal) ^ (-ε) *
            ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)) * X := by gcongr
      _ = (σ : ENNReal) ^ (-ε) *
          ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) * X := rfl)

/-- The large-width branch of Proposition 6.6(A), obtained directly from the canonical
Frostman multiplicity estimate.  No factorization data are used in this branch: when
`σ ^ (ε / (3β)) ≤ a`, half of the allowed `σ`-loss pays for the entire plank-ratio gain. -/
theorem FrostmanEstimate.flatPrismLargeWidth {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ : 0 < β) (hdim : Module.finrank ℝ E = 3) (hKF : FrostmanEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube σ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (σ : ENNReal) ^ η ≤ fullness s (fun i => (V i).toShadedBody) →
        ∀ a b : NNReal, σ ≤ a → a ≤ b → b ≤ 1 → σ ^ (ε / (3 * β)) ≤ a →
          multiplicity s (fun i => (V i).toShadedBody) ≤
            (σ : ENNReal) ^ (-ε)
              * frostmanConstIn s (fun i => (V i).toConvexSpaceBody) closedUnitBall ^
                  (1 - β / 2)
              * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
              * (σ : ENNReal) ^ (-2 * β)
              * ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^ (1 - β / 2) := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ :=
    FrostmanEstimate.multiplicity_bound_of_mem (E := E) hβ0 hβ1
      (by omega : 1 < Module.finrank ℝ E) hKF (ε / 2) (by positivity)
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with σ hbound hσ
  intro ι s V hball hED hfull a b hσa hab hb1 hlarge
  have hfull' : σ ^ η ≤ fullness s (fun i => (V i).toShadedBody) := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg _ hη.le]
    exact hfull
  have hdirect := hbound s V hball hED hfull'
  have hdirect' : multiplicity s (fun i => (V i).toShadedBody) ≤
      (σ : ENNReal) ^ (-(ε / 2)) *
        (frostmanConstIn s (fun i => (V i).toConvexSpaceBody) closedUnitBall ^
            (1 - β / 2) *
          (σ : ENNReal) ^ (-2 * β) *
          ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^ (1 - β / 2)) := by
    rw [frostmanConstIn_eq_frostmanConstant]
    simpa only [hdim, Nat.reduceSub, mul_assoc] using hdirect
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    flatPrismLargeWidth_absorb (σ := σ) (a := a) (b := b) hσ hβ hε hσa hab hb1 hlarge
      hdirect'

/-- At `β = 0` the plank-ratio factor is one, so Proposition 6.6(A)'s numerical conclusion is
exactly the canonical Frostman multiplicity estimate. -/
theorem FrostmanEstimate.flatPrismBetaZero (hdim : Module.finrank ℝ E = 3)
    (hKF : FrostmanEstimate.{u} E 0) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube σ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (σ : ENNReal) ^ η ≤ fullness s (fun i => (V i).toShadedBody) →
        ∀ a b : NNReal,
          multiplicity s (fun i => (V i).toShadedBody) ≤
            (σ : ENNReal) ^ (-ε)
              * frostmanConstIn s (fun i => (V i).toConvexSpaceBody) closedUnitBall ^
                  (1 - (0 : ℝ) / 2)
              * ((a : ENNReal) / (b : ENNReal)) ^ (3 * (0 : ℝ) / 2)
              * (σ : ENNReal) ^ (-2 * (0 : ℝ))
              * ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^
                  (1 - (0 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ :=
    FrostmanEstimate.multiplicity_bound_of_mem (E := E) le_rfl zero_le_one
      (by omega : 1 < Module.finrank ℝ E) hKF ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with σ hbound
  intro ι s V hball hED hfull a b
  have hfull' : σ ^ η ≤ fullness s (fun i => (V i).toShadedBody) := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_nonneg _ hη.le]
    exact hfull
  have hdirect := hbound s V hball hED hfull'
  rw [frostmanConstIn_eq_frostmanConstant]
  simpa only [hdim, Nat.reduceSub, zero_div, sub_zero, mul_zero, ENNReal.rpow_zero,
    mul_one, one_mul] using hdirect

open Classical in
/-- A dilated-thickening non-concentration bound with parameter `C · (b / a)` yields a
pairwise-essentially-distinct outer subfamily at a loss depending only on `C`.

The point is to test at the smallest admissible thickening `a / b`.  At that scale the thickened
plank is the original plank.  Hence every plank conflicting with the anchor lies in its
`11`-dilation, and is counted as soon as the non-concentration dilation is at least `11`.  The
factors `(b / a)` and `(a / b)` cancel before the graph-colouring extraction is invoked. -/
theorem exists_pairwise_plank_subset_of_isThickeningNonconcentrated
    {ι : Type*} {a b C C_NC : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha : 0 < a) (hb : 0 < b) (hCNC : 11 ≤ C_NC)
    (s : Finset ι) (P : ι → ShadedPlank a b hab hb1)
    (hNC : Plank.IsThickeningNonconcentrated s (fun i ↦ (P i).toPrism3D)
      C_NC (C * (b / a))) :
    let d := ⌈(C : ℝ)⌉₊
    ∃ s' ⊆ s,
      (s' : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      s.card ≤ (d + 1) * s'.card ∧
      (∑ i ∈ s, volume (P i).shade) ≤
        ((d : ENNReal) + 1) * ∑ i ∈ s', volume (P i).shade := by
  let d := ⌈(C : ℝ)⌉₊
  have hab1 : a / b ≤ 1 := (div_le_one hb).2 hab
  have hcancel : (C * (b / a)) * (a / b) = C := by
    field_simp [ha.ne', hb.ne']
  have hdeg : ∀ i ∈ s,
      edConflictDegree s (fun j ↦ (P j).carrier) i ≤ d := by
    intro i hi
    let counted := s.filter fun j ↦
      ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((Plank.thickened (P i).toPrism3D (a / b) hab1).toPrismNDim.dilation C_NC).carrier)
    have hbadSub :
        (s.filter fun j ↦ ¬ IsEssentiallyDistinct (P i).carrier (P j).carrier) ⊆ counted := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨hj'.1, ?_⟩
      have h11 := large_overlap_plank_subset_dilation (P i).toPrism3D (P j).toPrism3D hj'.2
      have hmono :
          ((P i).toPrism3D.toPrismNDim.dilation 11).carrier ⊆
            ((P i).toPrism3D.toPrismNDim.dilation C_NC).carrier :=
        PrismNDim.dilation_carrier_mono (P i).toPrism3D.toPrismNDim hCNC
      rw [Plank.plank_thickened_self_dilation_carrier hb hab1 (P i).toPrism3D C_NC]
      exact h11.trans hmono
    have hcount : (counted.card : NNReal) ≤ C := by
      have h := hNC i hi (a / b) hab1 le_rfl
      simpa only [counted, hcancel] using h
    have hbadNN :
        ((s.filter fun j ↦ ¬ IsEssentiallyDistinct (P i).carrier (P j).carrier).card : NNReal)
          ≤ C := by
      exact (by exact_mod_cast Finset.card_le_card hbadSub :
        ((s.filter fun j ↦ ¬ IsEssentiallyDistinct (P i).carrier (P j).carrier).card : NNReal)
          ≤ counted.card) |>.trans hcount
    have hbadR :
        ((s.filter fun j ↦ ¬ IsEssentiallyDistinct (P i).carrier (P j).carrier).card : ℝ)
          ≤ (C : ℝ) := by exact_mod_cast hbadNN
    have hceil : (C : ℝ) ≤ (d : ℝ) := by
      exact Nat.le_ceil (C : ℝ)
    exact_mod_cast hbadR.trans hceil
  simpa only [d] using exists_inner_plank_ED_subfamily_weighted s P hdeg

open Classical in
/-- The essentially-distinct extraction from a thickening-nonconcentrated plank family, packaged
as the mass refinement used by the multiplicity ledger.

This is only a bookkeeping corollary of
`exists_pairwise_plank_subset_of_isThickeningNonconcentrated`: the shades and carriers are not
changed, and the reciprocal of the conflict-degree bound is recorded as an explicit
`IsCRefinement` coefficient. -/
theorem exists_pairwise_plank_CRefinement_of_isThickeningNonconcentrated
    {ι : Type*} {a b C C_NC : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha : 0 < a) (hb : 0 < b) (hCNC : 11 ≤ C_NC)
    (s : Finset ι) (P : ι → ShadedPlank a b hab hb1)
    (hNC : Plank.IsThickeningNonconcentrated s (fun i ↦ (P i).toPrism3D)
      C_NC (C * (b / a))) :
    let d := ⌈(C : ℝ)⌉₊
    ∃ s' ⊆ s,
      (s' : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      s.card ≤ (d + 1) * s'.card ∧
      ShadedBody.IsCRefinement s' (fun i ↦ (P i).toShadedBody)
        s (fun i ↦ (P i).toShadedBody) ((d + 1 : ℕ) : NNReal)⁻¹ := by
  let d := ⌈(C : ℝ)⌉₊
  obtain ⟨s', hs', hED, hcard, hmass⟩ :=
    exists_pairwise_plank_subset_of_isThickeningNonconcentrated ha hb hCNC s P hNC
  refine ⟨s', hs', hED, hcard, ?_⟩
  apply ShadedBody.isCRefinement_of_isRefinement_of_sum_le
  · exact ⟨hs', fun _ _ ↦ ⟨rfl, Set.Subset.rfl⟩⟩
  · convert hmass using 1
    norm_cast

/-- Large `b` makes one rescaled unit-ball tube large enough to test every fine tube, so parent
essential distinctness bounds the total number of occupied assigned parent labels. -/
theorem flatPrismOccupiedParents_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {ι κ : Type*} [DecidableEq κ]
    {σ ρ D bSmall b : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hD : 1 ≤ D) (hbSmall0 : 0 < bSmall) (hbLarge : bSmall ≤ b)
    (hbρ : b ≤ D * ρ) (q : Finset ι) (T : ι → Tube σ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1)
    (r : Finset κ) (R : κ → Tube ρ E) (assign : ι → κ)
    (hED : (r : Set κ).Pairwise fun k l ↦ IsEssentiallyDistinct (R k).carrier (R l).carrier)
    (hassign : ∀ i ∈ q,
      assign i ∈ r ∧ (T i).toConvexSpaceBody ≤ Tube.dilate (R (assign i)) (D : ℝ)) :
    let Ctest : NNReal := max 1 (D * bSmall⁻¹)
    let parents := r.filter fun k ↦ ∃ i ∈ q, assign i = k
    (parents.card : ENNReal) ≤
      (edParentCount.C (Module.finrank ℝ E) D Ctest : ENNReal) := by
  classical
  dsimp only
  let Ctest : NNReal := max 1 (D * bSmall⁻¹)
  have hCtest : 1 ≤ Ctest := le_max_left _ _
  have hscale : 1 ≤ Ctest * ρ := by
    have hbDρ : bSmall ≤ D * ρ := hbLarge.trans hbρ
    calc
      1 = bSmall⁻¹ * bSmall := (inv_mul_cancel₀ hbSmall0.ne').symm
      _ ≤ bSmall⁻¹ * (D * ρ) := by gcongr
      _ = (D * bSmall⁻¹) * ρ := by ring
      _ ≤ Ctest * ρ := by gcongr; exact le_max_right _ _
  obtain ⟨Vone, hVone⟩ := exists_tube_one_superset_of_subset_unitBall q T hball
  let Vtest : Tube (Ctest * ρ) E := Vone.rescale (Ctest * ρ)
  have htest : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ Vtest.toConvexSpaceBody := by
    intro i hi
    calc
      (T i).toConvexSpaceBody ≤ Vone.toConvexSpaceBody := hVone i hi
      _ = (Vone.rescale 1).toConvexSpaceBody := (Tube.toConvexSpaceBody_rescale_self Vone).symm
      _ ≤ Vtest.toConvexSpaceBody := Tube.rescale_le_rescale_of_radius_le Vone hscale
  have hcount := edParentCount.card_assignedParents_le hρ0 hρ1 hD hCtest
    q T r R assign hED hassign Vtest
  let parents := r.filter fun k ↦ ∃ i ∈ q, assign i = k
  have heq :
      {k ∈ r | ∃ i ∈ q,
        assign i = k ∧ (T i).toConvexSpaceBody ≤ Vtest.toConvexSpaceBody} = parents := by
    ext k
    simp only [parents, Finset.mem_filter]
    constructor
    · rintro ⟨hk, i, hi, hik, _⟩
      exact ⟨hk, i, hi, hik⟩
    · rintro ⟨hk, i, hi, hik⟩
      exact ⟨hk, i, hi, hik, htest i hi⟩
  rw [heq] at hcount
  simpa only [Ctest, parents] using hcount

/-- A fixed-parent fibre of the labelled block sum injectively reindexes by its part. -/
theorem flatPrismParentFibre_isKatzTao
    {ι κ : Type*} [DecidableEq κ]
    {t : Finset κ} {q : Finset (FlatPrismBlock (ι := ι) t)} {k : κ}
    {parts : Finset (Finset ι)}
    {Kpart : Finset ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {U : FlatPrismBlock (ι := ι) t → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C : ENNReal}
    (hKT : ConvexSpaceBody.IsKatzTao parts Kpart C)
    (hpart : ∀ x ∈ q, x.1.1 = k → x.2 ∈ parts)
    (hbody : ∀ x ∈ q, x.1.1 = k → U x = Kpart x.2) :
    ConvexSpaceBody.IsKatzTao (q.filter fun x ↦ x.1.1 = k) U C := by
  classical
  let e : FlatPrismBlock (ι := ι) t → Finset ι := fun x ↦ x.2
  have he_mem : ∀ x ∈ q.filter (fun x ↦ x.1.1 = k), e x ∈ parts := by
    intro x hx
    exact hpart x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have he_inj : Set.InjOn e (q.filter fun x ↦ x.1.1 = k) := by
    intro x hx y hy hxy
    have hxk : x.1.1 = k := (Finset.mem_filter.mp hx).2
    have hyk : y.1.1 = k := (Finset.mem_filter.mp hy).2
    have hparent : x.1 = y.1 := Subtype.ext (hxk.trans hyk.symm)
    exact Sigma.ext hparent (heq_of_eq hxy)
  have hreindex := hKT.of_injOn_reindex he_mem he_inj
  rw [ConvexSpaceBody.IsKatzTao_def] at hreindex ⊢
  rw [Kakeya.maxDensity_congr (fun x hx ↦
    hbody x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)]
  simpa only [e] using hreindex

open Classical in
/-- Pool parentwise Katz--Tao estimates after a common volume-comparable envelope replacement. -/
theorem maxDensity_le_of_flatPrismParentwise_envelopes
    {ι κ : Type*} [DecidableEq κ]
    {s : Finset ι} {par : ι → κ} {parents : Finset κ}
    {U P : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C A : ENNReal}
    (hpar : ∀ i ∈ s, par i ∈ parents)
    (hKT : ∀ k ∈ parents, ConvexSpaceBody.IsKatzTao (s.filter fun i ↦ par i = k) U C)
    (hUP : ∀ i ∈ s, U i ≤ P i)
    (hvol : ∀ i ∈ s, volume (P i).carrier ≤ A * volume (U i).carrier) :
    maxDensity s P ≤ (parents.card : ENNReal) * (A * C) := by
  apply maxDensity_le_sum_of_parentwise hpar
  intro k hk
  exact ConvexSpaceBody.IsKatzTao.of_envelope (hKT k hk)
    (fun i hi ↦ hUP i (Finset.mem_filter.mp hi).1)
    (fun i hi ↦ hvol i (Finset.mem_filter.mp hi).1)

/-! ### Additional estimates

The two differ in exactly one direction:

* the parent data are packaged as `Kakeya.FlatPrismParentPresentation`, which *relaxes* the parent
  containment to a fixed dilation `D` and *adds* one hypothesis -- pairwise essential distinctness
  of the coarse `rho`-tubes indexed by `t` (`pairwise`).  That field is genuinely load-bearing: it
  is consumed by `Kakeya.flatPrismOccupiedParents_le` and by the inner essential-distinctness
  extraction, i.e. by the count of coarse parents that can meet one plank-shaped test body;
* the scale ordering is relaxed from `sigma <= a <= b <= rho <= 1` to
  `sigma <= a <= b <= 1`, `sigma <= rho <= 1`, `b <= D * rho`, which is *implied* by ship's ordering
  at `D = 1`.

`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_coarseEssDistinct`, below, discharges every
other difference mechanically: it is ship's statement verbatim plus the coarse-essential-distinctness
hypothesis, and it is proved from this theorem.  So the coarse-ED hypothesis is the *whole* residual
gap between this harvest and the open statement of 6.6(A).

Nothing else on that branch is a proof of 6.6(A).  Its
`Kakeya.tubeMultiplicityOfLocalPlankFactorisation_of_analyticAssembly` (see
`Kakeya/DimensionThree/Plank/PlankFactorizationEstimate.lean`) is conditional on the assumed interface `Kakeya.Section6PartAAnalyticAssembly`. -/

set_option maxHeartbeats 4000000 in
-- The two scale branches share a long explicit loss ledger and require extra elaboration time.

/-- **(GWZ Proposition 6.6(A)) with the plank scales below the coarse scale** (blueprint
`prop:ml1bootFlatPrismsCorrected`).

Suppose `K_KT(β)` and `K_F(β)` hold in `ℝ³` and let `Cw ≥ 1` be a plank comparability
constant.  For every `ε' > 0` there is a fullness threshold `η' > 0` such that, for all
sufficiently small `σ > 0`: if `(𝕍, Z)` is a nonempty uniform family of shaded `σ`-tubes in
`B₁ ⊆ ℝ³` with `λ(𝕍, Z) ≥ σ ^ η'`, and if there are a scale `ρ` with `σ ≤ a ≤ b ≤ ρ ≤ 1`, a
coarse family `(V_{ρ,k})_{k ∈ t}` of `ρ`-tubes with `V i ≤ V_{ρ,p i}`, and for every `k ∈ t` a
family of `a × b × 1` planks `2`-factoring the parent-map fibre
`𝕍[V_{ρ,k}] = (V_i)_{i ∈ s, p i = k}`, then

`μ(𝕍, Z) ≤ σ ^ (-ε') · C_F(𝕍, B₁) ^ (1 - β/2) · (a/b) ^ (3β/2) · σ ^ (-2β) · (|s| σ²) ^ (1 - β/2)`.

This is the **single** Lean record of GWZ Proposition 6.6(A).  A second copy used to sit in
`Kakeya/DimensionThree/Plank/Factorization.lean` under the name
`tubeMultiplicityOfLocalPlankFactorisation`; it asserted the same bound in the opposite scale
regime `ρ ≤ a`, with honest `a × b × 1` plank parts and the ambient space fixed at
`EuclideanSpace ℝ (Fin 3)`.  Neither form implies the other, it had no consumer, and [GWZ]
imposes no ordering between `ρ` and `a, b` at all, so it has been removed rather than kept as a
second statement for one paper result; see blueprint `note:ml1bootFlatPrismScales`.

Relative to the paper the statement below is a *restriction*: the plank scales are required to
lie below the coarse scale, `σ ≤ a ≤ b ≤ ρ ≤ 1`, which is the regime every consumer supplies,
the planks come out of `Kakeya.ml1Boot.exists_plankDimensions` inside the fibres of a
`ρ`-parent family.  The exponent `2` in the bracket is the literal ambient value, since `hdim`
is in force.

## The binders

* `hdim` fixes the ambient dimension at `3`; without it neither `hKKT` nor `hKF` is the
  hypothesis GWZ Proposition 6.6(A) uses, and the literal exponent `2` in the bracket
  `|s| σ ^ 2` would be wrong.
* `β`, `hβ0`, `hβ1` are the exponent of the two partial estimates and its admissible range;
  `1 - β / 2` and `3 β / 2` in the conclusion are meaningless outside it.
* `hKKT`, `hKF` are the two partial estimates the proposition consumes, at that same `β`.
* `Cw`, `hCw` are the plank comparability constant: the planks supplied by
  `Kakeya.ml1Boot.exists_plankDimensions` have their dimensions only up to
  `Kakeya.ml1Boot.plankPigeonhole.C`, so a fixed constant will not do, and `η'` must be chosen
  after it.
* `Cunif` is the uniformity constant of the family, quantified before `η'` for the same reason.
* `ε'` is the loss budget and `η'` the fullness threshold it buys; the order
  `∀ ε' > 0, ∃ η' > 0` is the blueprint's "for every `ε'` there are `η'` and `δ₀`".
* `∀ᶠ σ in 𝓝[>] 0` is that `δ₀`: the bound holds for all sufficiently small tube scales.
* `a`, `b`, `ρ` and the four inequalities `σ ≤ a ≤ b ≤ ρ ≤ 1` are the plank widths and the
  coarse scale, with the plank scales *below* the coarse scale; the chain subsumes the
  blueprint's separate `σ ≤ ρ`.
* `ι`, `κ` and their `DecidableEq` instances index the family and the coarse family; the
  instances are needed for the parent-map fibre `s.filter fun i => p i = k`.
* `V`, `Vρ`, `p` are the family, the coarse family and the parent map, followed by the two
  anonymous clauses `p i ∈ t` and `V i ≤ Vρ (p i)` that make the triple a parent family.  They
  are given as bare data rather than as `Kakeya.ml1Boot.IsParentFamily` so that this file does
  not depend on Section 8 (see the module docstring).
* The `Kakeya.IsFlatPrismFamily` hypothesis is the family package: nonempty, **one-sidedly**
  uniform, in `B₁`, pairwise essentially distinct, and full at level `σ ^ η'`.
* The last hypothesis is the plank factorization, one factorization per coarse tube; it is the
  only place `Cw`, `a` and `b` are read.

## Proof architecture

The proof uses the corrected Proposition 5.1 core and factors the selected family over the
fibres of the supplied parent map, not over containment fibres.  Pairwise essential distinctness
of the parent tubes replaces geometric uniqueness: an enlarged plank test body meets only a
bounded number of assigned parents, so parentwise Katz--Tao counts pool to the dilation
nonconcentration needed by Proposition 6.4.  The exact outer planks are obtained from genuine
scaled-collar envelopes of the actual factor bodies, and a pairwise essentially distinct outer
subfamily is extracted internally.  Its extraction loss, both `SelectScale` losses, the core
refinement/product loss, and the inner essential-distinctness normalization are all charged to
the local loss envelope.

The `unif` field remains the one-sided `Kakeya.IsFlatPrismUniform`.  This is exactly the part of
uniformity used by the proof and descends to the prescribed Section-8 subfamily without another
regularization.  Consequently Section 8 constructs the parent presentation at its call sites and
does not acquire any parent-overlap or nonconcentration hypothesis.  Proposition 6.4 is used in
its existing dilation form. -/
theorem multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation
    (hdim : Module.finrank ℝ E = 3)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β) (hKF : FrostmanEstimate.{u} E β)
    (Cw : NNReal) (hCw : 1 ≤ Cw) (Dpar : NNReal) :
    ∀ ε' > (0 : ℝ), ∃ η' > (0 : ℝ),
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0, ∀ Cunif : NNReal, 1 ≤ Cunif →
      (Cunif : ENNReal) ≤ (σ : ENNReal) ^ (-η') →
      ∀ a b ρ : NNReal, σ ≤ a → a ≤ b → b ≤ 1 → σ ≤ ρ →
      b ≤ Dpar * ρ → ρ ≤ 1 →
      ∀ {ι κ : Type u} [DecidableEq ι] [DecidableEq κ] {s : Finset ι} {t : Finset κ}
        (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ),
        IsFlatPrismFamily η' Cunif s V →
        FlatPrismParentPresentation (D := Dpar) s V t Vρ p →
        (∀ k ∈ t, ∃ F : ConvexSpaceBody.Factorization (s.filter fun i => p i = k)
              (fun i => (V i).toConvexSpaceBody) 2,
            IsPlankFamilyOfDimensions Cw a b F.parts
              (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ (σ : ENNReal) ^ (-ε')
            * (frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
                ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2)
            * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
            * (σ : ENNReal) ^ (-2 * β)
            * ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^ (1 - β / 2) := by
  classical
  intro ε' hε'
  by_cases hβ : β = 0
  · subst β
    obtain ⟨η, hη, hev⟩ := hKF.flatPrismBetaZero hdim ε' hε'
    refine ⟨η, hη, ?_⟩
    filter_upwards [hev] with σ hbound
    intro Cunif _hCunif _hCunifσ a b ρ _hσa _hab _hb1 _hσρ _hbρ _hρ1 ι κ _ _ s t V Vρ p
      hfamily _hparent _Fz
    exact hbound s V hfamily.ball hfamily.essDistinct hfamily.fullness a b
  · have hβpos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ)
    let f₃ := dimThreeLinearIsometryEquiv E hdim
    have hKF₃ : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β :=
      hKF.mapLinearIsometryEquiv f₃
    obtain ⟨C_NC, hC_NC, h64All⟩ :=
      FrostmanEstimate.plankEstimate_auxScale.{u} hβpos hβ1 hKF₃
    obtain ⟨η64, hη64, b₀64, hb₀64, h64⟩ :=
      h64All (ε' / 12) (by positivity)
    obtain ⟨C_NCI, hC_NCI, h64AllI⟩ :=
      FrostmanEstimate.plankEstimate_auxScale.{0} hβpos hβ1 hKF₃
    obtain ⟨η64I, hη64I, b₀64I, hb₀64I, h64I⟩ :=
      h64AllI (ε' / 12) (by positivity)
    obtain ⟨Cnorm, dED, Cinner, bGeom, δGeom, hCnorm, hdED, hCinner,
        hbGeom, hδGeom, hδGeom1, hinnerED⟩ :=
      exists_inner_ED_family_of_fineTubes.{u} C_NCI hC_NCI
    let hexp : ℝ := ε' / (3 * β)
    have hhexp : 0 < hexp := by
      dsimp only [hexp]
      exact div_pos hε' (mul_pos (by norm_num) hβpos)
    let Cexpand : NNReal := max 1 (max b₀64I⁻¹ bGeom⁻¹)
    have hCexpand : 1 ≤ Cexpand := le_max_left _ _
    have hb₀64inv : b₀64I⁻¹ ≤ Cexpand :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hbGeominv : bGeom⁻¹ ≤ Cexpand :=
      (le_max_right _ _).trans (le_max_right _ _)
    let Cwi : NNReal := Cexpand * Cw
    have hCwi : 1 ≤ Cwi := one_le_mul hCexpand hCw
    have hCwCwi : Cw ≤ Cwi := by
      dsimp only [Cwi]
      exact le_mul_of_one_le_left (by positivity) hCexpand
    let bSmall₀ : NNReal := min b₀64 Cwi⁻¹
    have hbSmall₀pos : 0 < bSmall₀ := lt_min hb₀64 (inv_pos.mpr
      (zero_lt_one.trans_le hCwi))
    obtain ⟨Kang, hKang⟩ :=
      ShadedSlab.exists_numAngleWindows_le (ε := ε' / 64) (by positivity)
    obtain ⟨Cm, hCm, hmassWindow⟩ := exists_plankWindowMassConst 1 le_rfl
    obtain ⟨ηLarge, hηLarge, hev⟩ :=
      hKF.flatPrismLargeWidth hβ0 hβ1 hβpos hdim ε' hε'
    let ηB : ℝ := ε' / 64
    have hηB : 0 < ηB := by
      dsimp only [ηB]
      positivity
    let η : ℝ := min ηLarge
      (min (η64I / 8)
        (min (hexp * η64 / 128) (min (hexp * ηB / 128) (ε' / 128))))
    have hη : 0 < η := by
      dsimp only [η]
      exact lt_min hηLarge
        (lt_min (by positivity)
          (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
    have hηLarge_le : η ≤ ηLarge := min_le_left _ _
    have hη64I_le : η ≤ η64I / 8 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hηOuter_le : η ≤ hexp * η64 / 128 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
    have hηLargeB_le : η ≤ hexp * ηB / 128 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    have hηEps_le : η ≤ ε' / 128 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    let eFund : ℝ := min (η64I / 128)
      (min (hexp * η64 / 512) (min (hexp * ηB / 512) (ε' / 512)))
    have heFund : 0 < eFund := by
      dsimp only [eFund]
      exact lt_min (by positivity)
        (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
    have heFundI : eFund ≤ η64I / 128 := min_le_left _ _
    have heFundOuter : eFund ≤ hexp * η64 / 512 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have heFundLargeB : eFund ≤ hexp * ηB / 512 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
    have heFundEps : eFund ≤ ε' / 512 :=
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_right _ _)
    let cNormLoss : ENNReal := (Cnorm : ENNReal) * ((dED : ENNReal) + 1)
    have hcNormLoss1 : 1 ≤ cNormLoss := by
      dsimp only [cNormLoss]
      exact one_le_mul (by exact_mod_cast hCnorm) (by simp)
    have hcNormLossTop : cNormLoss ≠ ⊤ := by
      dsimp only [cNormLoss]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.add_ne_top.mpr ⟨by finiteness, by norm_num⟩)
    let CFI₀ : ENNReal := flatPrismInnerNormalisedFrostman.C Cnorm dED
      (flatPrismInnerFrostman.C Cwi : ENNReal)
    let Cextract₀ : NNReal :=
      edParentCount.COfTestDilate 3 Dpar 1 (2 * ((8 * Cw) * 11 * Dpar)) *
        flatPrismOuterSplit.C Cw 11
    let dO₀ : ℕ := ⌈(Cextract₀ : ℝ)⌉₊
    let innerFixed₀ : ENNReal := (dED + 1 : ENNReal) * CFI₀ ^ (1 - β / 2) *
      (Cinner : ENNReal) ^ (β / 2) * (Cwi : ENNReal) ^ (2 * β) *
        (2 * (flatPrismBodyVolumeRatio.C Cw : ENNReal)) ^ (1 - β / 2)
    let splitFixed₀ : ENNReal := (dO₀ + 1 : ENNReal) * innerFixed₀ * 4 *
      (outerMultiplicityFromLocalBalls.C 3 : ENNReal)
    let rsh₀ : ℝ := comparablePlankEnvelope.shrink Cw
    let scaledBall₀ : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
      ConvexSpaceBody.closedUnitBall.homothety 0 rsh₀
    let fixedFrost₀ : ENNReal :=
      (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) * 8 *
        (volume plankWindow.carrier / volume scaledBall₀.carrier) * (dO₀ + 1 : ENNReal)
    let fixedFull₀ : ENNReal := (dO₀ + 1 : ENNReal) *
      (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) * 2 *
        (2 * 2 ^ 2 * lambdaInducedSingleWUniform.C)
    let Couter₀ : NNReal :=
      edParentCount.COfTestDilate 3 Dpar 1
        (2 * ((8 * Cw) * C_NC * Dpar)) * flatPrismOuterSplit.C Cw C_NC
    let CtestTotal₀ : NNReal := max 1 (Dpar * bSmall₀⁻¹)
    let CparentTotal₀ : NNReal := edParentCount.C 3 Dpar CtestTotal₀
    let Cdiv₀ : NNReal := 196520 * Kang * (8 * bSmall₀ ^ 2)⁻¹
    let Δlarge₀ : NNReal := CparentTotal₀ * (flatPrismEnvelopeVolumeRatio.C Cw * 2)
    let CoutLarge₀ : NNReal := Cdiv₀ * Δlarge₀
    let CfinalLarge₀ : NNReal := CoutLarge₀ * Cm⁻¹ ^ (1 - β / 2) *
      max 1 (bSmall₀ ^ (5 * β / 2 - 1))
    let partAFixedBase : ENNReal := max 1 <| max splitFixed₀ <|
      max fixedFrost₀ <| max fixedFull₀ <| max (Couter₀ : ENNReal) <|
        max (CparentTotal₀ : ENNReal) <| max (Cdiv₀ : ENNReal) (Cm : ENNReal)⁻¹
    let partAFixedEnvelope : ENNReal := max partAFixedBase (CfinalLarge₀ : ENNReal)
    let CwiLargeExtra : ENNReal := max 1 ((Cwi : ENNReal) ^ (1 - β))
    have hCwiLargeExtra1 : 1 ≤ CwiLargeExtra := le_max_left _ _
    have hCwiLargeExtraTop : CwiLargeExtra ≠ ⊤ := by
      dsimp only [CwiLargeExtra]
      exact max_ne_top (by norm_num) (by finiteness)
    have hpartAFixed1 : 1 ≤ partAFixedEnvelope :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hpartAFixedBase_le : partAFixedBase ≤ partAFixedEnvelope := le_max_left _ _
    have hCFI₀top : CFI₀ ≠ ⊤ := by
      dsimp only [CFI₀, flatPrismInnerNormalisedFrostman.C]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)) ENNReal.coe_ne_top)
        plankWindow.isCompact.measure_ne_top
    have hCFI₀one : 1 ≤ CFI₀ := by
      dsimp only [CFI₀, flatPrismInnerNormalisedFrostman.C]
      exact one_le_mul
        (one_le_mul
          (one_le_mul (by exact_mod_cast hCnorm) (by simp))
          (by exact_mod_cast flatPrismInnerFrostman.one_le Cwi))
        one_le_volume_plankWindow
    have hinnerFixed₀top : innerFixed₀ ≠ ⊤ := by
      dsimp only [innerFixed₀]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (by finiteness)
              (ENNReal.rpow_ne_top_of_ne_zero
                (zero_lt_one.trans_le hCFI₀one).ne' hCFI₀top))
            (ENNReal.rpow_ne_top_of_ne_zero
              (ENNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hCinner).ne')
              ENNReal.coe_ne_top))
          (ENNReal.rpow_ne_top_of_ne_zero
            (ENNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hCwi).ne')
            ENNReal.coe_ne_top))
        (ENNReal.rpow_ne_top_of_ne_zero (by
          exact mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr
            (zero_lt_one.trans_le (flatPrismBodyVolumeRatio.one_le Cw)).ne'))
          (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top))
    have hsplitFixed₀top : splitFixed₀ ≠ ⊤ := by
      dsimp only [splitFixed₀]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by finiteness) hinnerFixed₀top) (by norm_num))
        ENNReal.coe_ne_top
    have hpartAFixedTop : partAFixedEnvelope ≠ ⊤ := by
      have hrsh₀0 : rsh₀ ≠ 0 := by
        dsimp only [rsh₀]
        exact_mod_cast (comparablePlankEnvelope.shrink_pos hCw).ne'
      have hscaledBall₀0 : volume scaledBall₀.carrier ≠ 0 := by
        dsimp only [scaledBall₀]
        rw [ConvexSpaceBody.volume_homothety]
        exact mul_ne_zero (by
          have hrpos :
              0 < |rsh₀ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| := by
            positivity
          exact (ENNReal.ofReal_pos.mpr hrpos).ne')
          ConvexSpaceBody.closedUnitBall_volume_pos.ne'
      have hbaseTop : partAFixedBase ≠ ⊤ := by
        dsimp only [partAFixedBase, fixedFrost₀, fixedFull₀, splitFixed₀,
          innerFixed₀, CFI₀]
        apply max_ne_top
        · norm_num
        apply max_ne_top
        · exact hsplitFixed₀top
        apply max_ne_top
        · exact ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.mul_ne_top ENNReal.coe_ne_top (by norm_num))
              (ENNReal.div_ne_top (plankWindow.isCompact.measure_ne_top) hscaledBall₀0))
            (by finiteness)
        apply max_ne_top
        · finiteness
        apply max_ne_top
        · finiteness
        apply max_ne_top
        · finiteness
        apply max_ne_top
        · finiteness
        · exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hCm.ne')
      dsimp only [partAFixedEnvelope]
      exact max_ne_top hbaseTop (by finiteness)
    have hBsel : 1 ≤ max 1 (2 * Dpar) := le_max_left _ _
    refine ⟨η, hη, ?_⟩
    have hCwpos : 0 < Cw := zero_lt_one.trans_le hCw
    have hCwipos : 0 < Cwi := zero_lt_one.trans_le hCwi
    have hCwiinvpos : 0 < (Cwi : ENNReal)⁻¹ := ENNReal.inv_pos.mpr ENNReal.coe_ne_top
    have hδGeomNN : 0 < Real.toNNReal δGeom := Real.toNNReal_pos.mpr hδGeom
    filter_upwards [hev,
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num),
      Ioo_mem_nhdsGT hδGeomNN,
      ENNReal.eventually_coe_rpow_le_of_pos hhexp hCwiinvpos,
      ShadedBody.eventually_const_le_coe_rpow_neg hcNormLoss1 hcNormLossTop heFund,
      ShadedBody.eventually_const_le_coe_rpow_neg hpartAFixed1 hpartAFixedTop heFund,
      ShadedBody.eventually_const_le_coe_rpow_neg hCwiLargeExtra1 hCwiLargeExtraTop heFund,
      eventually_flatPrismVolumeRatioExponent_add_one_le_rpow_neg Dpar
        (show 0 < eFund / 4 by positivity),
      ShadedBody.eventually_outerDensitySelectionConstant_le_rpow_neg 7 heFund,
      ShadedBody.eventually_outerScaleSelectionConstant_le_rpow_neg
        (max 1 (2 * Dpar)) hBsel heFund,
      ShadedBody.eventually_factoringCoreAtScaleUniformPipelineLoss_le_rpow_neg heFund,
      eventually_flatPrism_card_le_rpow_neg_seven hdim] with
        σ hlargeBound hσrange hσGeom hσpowCwi hNormLoss hPartAFixed hCwiExtraLoss
          hVolumeExponent hDensityLoss
          hScaleLossMax hPipelineLoss hCardLoss
    intro Cunif hCunif hCunifσ a b ρ hσa hab hb1 hσρ hbρ hρ1 ι κ _ _ s t V Vρ p hfamily
      hparent hFz
    by_cases hlarge : σ ^ (ε' / (3 * β)) ≤ a
    · have hσ1 : σ ≤ 1 := hσrange.2.le.trans (by norm_num)
      have hfullLarge : (σ : ENNReal) ^ ηLarge ≤
          fullness s (fun i ↦ (V i).toShadedBody) := by
        calc
          (σ : ENNReal) ^ ηLarge ≤ (σ : ENNReal) ^ η :=
            ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hσ1) hηLarge_le
          _ ≤ _ := hfamily.fullness
      exact hlargeBound s V hfamily.ball hfamily.essDistinct hfullLarge a b hσa hab
        hb1 hlarge
    · let Fz' : ∀ k : FlatPrismParent t,
          ConvexSpaceBody.Factorization (s.filter fun i => p i = k.1)
            (fun i => (V i).toConvexSpaceBody) 2 :=
        fun k => (hFz k.1 k.2).choose
      have hFzDims : ∀ k : FlatPrismParent t,
          IsPlankFamilyOfDimensions Cw a b (Fz' k).parts
            (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)) := by
        intro k
        simpa only [Fz'] using (hFz k.1 k.2).choose_spec
      have hσ : 0 < σ := hσrange.1
      have hσpowCwiNN : σ ^ (ε' / (3 * β)) ≤ Cwi⁻¹ := by
        apply ENNReal.coe_le_coe.mp
        simpa only [ENNReal.coe_inv hCwipos.ne',
          ENNReal.coe_rpow_of_ne_zero hσ.ne'] using hσpowCwi
      have hσpowCwiR : (σ : ℝ) ^ (ε' / (3 * β)) ≤ ((Cwi⁻¹ : NNReal) : ℝ) := by
        exact_mod_cast hσpowCwiNN
      have hCwiinvCw : Cwi⁻¹ ≤ Cw⁻¹ :=
        (inv_le_inv₀ hCwipos hCwpos).2 hCwCwi
      have hσpowCwNN : σ ^ (ε' / (3 * β)) ≤ Cw⁻¹ :=
        hσpowCwiNN.trans hCwiinvCw
      have hσpowCwR : (σ : ℝ) ^ (ε' / (3 * β)) ≤ ((Cw⁻¹ : NNReal) : ℝ) := by
        exact_mod_cast hσpowCwNN
      have haCwinv : a ≤ Cw⁻¹ := by
        exact_mod_cast (le_of_not_ge hlarge).trans hσpowCwR
      have hCwa : Cw * a ≤ 1 := by
        calc
          Cw * a ≤ Cw * Cw⁻¹ := mul_le_mul_left' haCwinv Cw
          _ = 1 := mul_inv_cancel₀ hCwpos.ne'
      have haCwiinv : a ≤ Cwi⁻¹ := by
        exact_mod_cast (le_of_not_ge hlarge).trans hσpowCwiR
      have hCwia : Cwi * a ≤ 1 := by
        calc
          Cwi * a ≤ Cwi * Cwi⁻¹ := mul_le_mul_left' haCwiinv Cwi
          _ = 1 := mul_inv_cancel₀ hCwipos.ne'
      have hσhalfNN : σ ≤ (1 / 2 : NNReal) := hσrange.2.le
      have hσhalf : (σ : ℝ) ≤ 1 / 2 := by exact_mod_cast hσhalfNN
      have hσB : σ ≤ 2 * Dpar := by
        exact hσhalfNN.trans <| (by
          calc
            (1 / 2 : NNReal) ≤ 2 := by
              exact_mod_cast (by norm_num : (1 / 2 : ℝ) ≤ 2)
            _ ≤ 2 * Dpar := by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hparent.one_le (by norm_num : (0 : NNReal) ≤ 2))
      have hfullposE : 0 < (fullness s (fun i => (V i).toShadedBody) : ENNReal) :=
        (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hσ) ENNReal.coe_ne_top).trans_le
          hfamily.fullness
      have hfullpos : 0 < fullness s (fun i => (V i).toShadedBody) :=
        ENNReal.coe_pos.mp hfullposE
      have hmass : 0 < ∑ i ∈ s, volume (V i).shade := by
        exact pos_iff_ne_zero.mpr
          (ShadedBody.sum_volume_shade_ne_zero_of_fullness_pos s
            (fun i => (V i).toShadedBody) hfullpos)
      letI : Nontrivial E :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
      let F := flatPrismFactorFamily V p hparent.mapsTo Fz' hfamily.nonempty
      let hdisc := flatPrismFactorFamily_innerDiscretized V p hparent.mapsTo Fz'
        hfamily.nonempty hfamily.ball
      let D := flatPrismFactorFamily_volumeRatio_dilate_controlled V p hparent.mapsTo Fz'
        hfamily.nonempty hdim hσ (hσhalfNN.trans (by norm_num)) hρ1 hfamily.ball Vρ
        hparent.le_parent_dilate
      let R := ShadedBody.outerDensitySelection F hσ hdisc D hmass
      let G := F.restrictOuter R.selected
      have hRsub : R.selected ⊆ F.outerSet :=
        R.selected_subset.trans F.innerSet_image_parent_subset_outerSet
      have hmassG : 0 < ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
        simpa only [G] using R.selected_mass_pos F hσ hdisc D hmass
      have hupperG : ∀ j ∈ G.innerSet.image G.parent,
          (G.outerBody j).scale ≤ 2 * Dpar := by
        intro j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact flatPrismFactorFamily_outerScale_le_two_mul V p hparent.mapsTo Fz'
          hfamily.nonempty hdim hρ1 Vρ hparent.le_parent_dilate (G.parent i) (by
            apply Finset.mem_image.mpr
            exact ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩)
      have Q := ShadedBody.factoringAndMultPropCoreSelectScale G hσ
        (hdisc.restrictOuter R.selected) (D.restrictOuter R.selected hRsub) hσB hupperG hmassG
        hdim
        ((flatPrismFactorFamily_innerHasSimilarShape V p hparent.mapsTo Fz'
          hfamily.nonempty hσhalf).restrictOuter R.selected)
        ((flatPrismFactorFamily_hasFrostmanFibers V p hparent.mapsTo Fz'
          hfamily.nonempty).restrictOuter R.selected hRsub)
      have hVpos : ∀ i ∈ F.innerSet, 0 < volume (F.innerBody i).carrier := by
        intro i hi
        have hlo := Tube.le_volume (V i).toTube
        have hc0 : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ 0 :=
          (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)).ne'
        have hσe0 : (σ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hσ).ne'
        have hpow0 : (σ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
          pow_ne_zero _ hσe0
        have hlowpos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
            (σ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
          exact lt_of_le_of_ne zero_le (Ne.symm (mul_ne_zero hc0 hpow0))
        have : 0 < volume (V i).carrier := hlowpos.trans_le hlo
        simpa only [F, flatPrismFactorFamily_innerSet, flatPrismFactorFamily_innerBody] using this
      have hVK : ∀ i ∈ F.innerSet,
          (F.innerBody i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall := by
        intro i hi
        change (V i).carrier ⊆ Metric.closedBall 0 1
        exact hfamily.ball i (by simpa only [F, flatPrismFactorFamily_innerSet] using hi)
      have hFrF : IsFrostmanIn F.innerSet
          (fun i ↦ (F.innerBody i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
          (frostmanConstIn s (fun i ↦ (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall) := by
        simpa only [F, flatPrismFactorFamily_innerSet, flatPrismFactorFamily_innerBody,
          frostmanConstIn_eq_frostmanConstant] using
          (ConvexSpaceBody.isFrostmanIn_frostmanConstant
            (s := s) (W := fun i ↦ (V i).toConvexSpaceBody)
            (K := ConvexSpaceBody.closedUnitBall))
      have hFrG := R.selected_inner_isFrostmanIn F hσ hdisc D hmass hFrF hVK
      let hdiscG := hdisc.restrictOuter R.selected
      let DG := D.restrictOuter R.selected hRsub
      let S := ShadedBody.outerScaleSelection G hσ hdiscG hσB hupperG hmassG
      have hSsubR : ∀ j ∈ S.selected, j ∈ R.selected := by
        intro j hj
        have hjG : j ∈ G.outerSet :=
          G.innerSet_image_parent_subset_outerSet (S.selected_subset hj)
        simpa only [G, ShadedBody.FactorFamily.restrictOuter_outerSet] using hjG
      have hWGK : ∀ j ∈ S.selected, G.outerBody j ≤ ConvexSpaceBody.closedUnitBall := by
        intro j hj
        have hjF : j ∈ F.outerSet := hRsub (hSsubR j hj)
        change flatPrismBlockBody V j ≤ ConvexSpaceBody.closedUnitBall
        exact
          flatPrismBlockBody_le_of_inner_le V p Fz' ConvexSpaceBody.closedUnitBall
            (fun i hi ↦ hVK i (by simpa only [F, flatPrismFactorFamily_innerSet] using hi))
            j hjF
      have hunifG : ∀ j ∈ S.selected, ∀ j' ∈ S.selected,
          densityIn (G.fiber j) (fun i ↦ (G.innerBody i).toConvexSpaceBody) (G.outerBody j) ≤
            2 * densityIn (G.fiber j')
              (fun i ↦ (G.innerBody i).toConvexSpaceBody) (G.outerBody j') := by
        intro j hj j' hj'
        have hjR := hSsubR j hj
        have hjR' := hSsubR j' hj'
        dsimp only [G]
        rw [ShadedBody.FactorFamily.restrictOuter_fiber_of_mem F R.selected hjR,
          ShadedBody.FactorFamily.restrictOuter_fiber_of_mem F R.selected hjR']
        exact R.density_comparable j hjR j' hjR'
      have hOuterFrostman :=
        Q.selected_outer_isFrostmanIn G hσ hdiscG DG hσB hupperG hmassG hFrG
          (fun i hi ↦ hVpos i (Finset.mem_filter.mp hi).1)
          (fun i hi ↦ hVK i (Finset.mem_filter.mp hi).1) hWGK hunifG
      let GS := ShadedBody.selectedOuterScaleFamily G hσ hdiscG hσB hupperG hmassG
      let DGS := DG.restrictOuter S.selected
        (S.selected_subset.trans G.innerSet_image_parent_subset_outerSet)
      let w₁ := ShadedBody.selectedOuterScale G hσ hdiscG hσB hupperG hmassG
      let W := ShadedBody.outerThickFamilyAtScale GS hσ
        (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos
      have hWsubS : W.outerSet ⊆ S.selected := by
        intro j hj
        have hjGS := ShadedBody.outerThickFamilyAtScale_outerSet_subset GS hσ
          (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos hj
        simpa only [GS, ShadedBody.selectedOuterScaleFamily,
          ShadedBody.FactorFamily.restrictOuter_outerSet] using hjGS
      let H := GS.restrictOuter W.outerSet
      have hmassGS : 0 < ∑ i ∈ GS.innerSet, volume (GS.innerBody i).shade := by
        exact pos_of_mul_pos_right (hmassG.trans_le Q.selection_mass) (by positivity)
      have hWne : W.outerSet.Nonempty := by
        exact ShadedBody.outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos
          (F := GS) hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos hmassGS
      let Lcore := ShadedBody.FactoringAtScaleLossBound.uniform GS hσ
        (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos
      have hrefW : ShadedBody.IsCRefinement W.innerSet W.innerBody GS.innerSet GS.innerBody
          Lcore.refinementConstant := by
        exact ShadedBody.outerThickFamilyAtScale_isCRefinement_of_lossBound
          GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos Lcore
      have hGSfiber : ∀ j ∈ GS.outerSet, (GS.fiber j).Nonempty := by
        intro j hj
        have hjS : j ∈ S.selected := by
          simpa only [GS, ShadedBody.selectedOuterScaleFamily,
            ShadedBody.FactorFamily.restrictOuter_outerSet] using hj
        have hjImage := S.selected_subset hjS
        obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hjImage
        refine ⟨i, ?_⟩
        simp only [GS, ShadedBody.selectedOuterScaleFamily,
          ShadedBody.FactorFamily.fiber, ShadedBody.FactorFamily.restrictOuter_innerSet,
          Finset.mem_filter]
        exact ⟨⟨hi, by simpa only [hip] using hjS⟩, hip⟩
      have hGSpos : ∀ i ∈ GS.innerSet, 0 < volume (GS.innerBody i).carrier := by
        intro i hi
        exact hVpos i (by
          simp only [GS, ShadedBody.selectedOuterScaleFamily, G,
            ShadedBody.FactorFamily.restrictOuter_innerSet, Finset.mem_filter] at hi
          exact hi.1.1)
      have hGSdens : ∀ j ∈ GS.outerSet, ∀ j' ∈ GS.outerSet,
          densityIn (GS.fiber j) (fun i ↦ (GS.innerBody i).toConvexSpaceBody)
              (GS.outerBody j) ≤
            2 * densityIn (GS.fiber j') (fun i ↦ (GS.innerBody i).toConvexSpaceBody)
              (GS.outerBody j') := by
        intro j hj j' hj'
        have hjS : j ∈ S.selected := by
          simpa only [GS, ShadedBody.selectedOuterScaleFamily,
            ShadedBody.FactorFamily.restrictOuter_outerSet] using hj
        have hjS' : j' ∈ S.selected := by
          simpa only [GS, ShadedBody.selectedOuterScaleFamily,
            ShadedBody.FactorFamily.restrictOuter_outerSet] using hj'
        dsimp only [GS, ShadedBody.selectedOuterScaleFamily]
        rw [ShadedBody.FactorFamily.restrictOuter_fiber_of_mem G S.selected hjS,
          ShadedBody.FactorFamily.restrictOuter_fiber_of_mem G S.selected hjS']
        exact hunifG j hjS j' hjS'
      have hOuterCarrierRetained :
          (Lcore.refinementConstant : ENNReal) *
              (fullness GS.innerSet GS.innerBody : ENNReal) *
              (∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier) ≤
            2 ^ 2 * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier := by
        exact ShadedBody.outerCarrierMass_retained_of_innerRefinement GS W.toFactorFamily
          hWne hrefW
          (fun i ↦ ShadedBody.outerThickFamilyAtScale_innerBody_toConvexSpaceBody
            GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos i)
          (ShadedBody.outerThickFamilyAtScale_outerSet_subset
            GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos)
          rfl hGSfiber hGSpos hGSdens
      have hHcard : ∀ j ∈ W.outerSet,
          ((H.fiber j).card : ENNReal) * (W.outerSet.card : ENNReal) ≤
            2 * (flatPrismBodyVolumeRatio.C Cw : ENNReal) * (s.card : ENNReal) := by
        intro j hj
        have hledger := ShadedBody.fiber_card_mul_outerSet_card_le_of_density_comparable
          H hσ (fun i ↦ (V i).toTube) (V hfamily.nonempty.choose).toTube
          (fun _ ↦ rfl) (Cdens := 2)
          (Cvol := (flatPrismBodyVolumeRatio.C Cw : ENNReal)) (by
            intro x hx y hy
            rw [ShadedBody.FactorFamily.restrictOuter_fiber_of_mem GS W.outerSet hx,
              ShadedBody.FactorFamily.restrictOuter_fiber_of_mem GS W.outerSet hy]
            have hxS := hWsubS hx
            have hyS := hWsubS hy
            change densityIn (GS.fiber x)
                (fun i ↦ (GS.innerBody i).toConvexSpaceBody) (GS.outerBody x) ≤
              2 * densityIn (GS.fiber y)
                (fun i ↦ (GS.innerBody i).toConvexSpaceBody) (GS.outerBody y)
            dsimp only [GS, ShadedBody.selectedOuterScaleFamily]
            rw [ShadedBody.FactorFamily.restrictOuter_fiber_of_mem G S.selected hxS,
              ShadedBody.FactorFamily.restrictOuter_fiber_of_mem G S.selected hyS]
            exact hunifG x hxS y hyS) (by
            intro x hx y hy
            have hxS := hWsubS hx
            have hyS := hWsubS hy
            have hxR := hSsubR x hxS
            have hyR := hSsubR y hyS
            have hxF : x ∈ F.outerSet := hRsub hxR
            have hyF : y ∈ F.outerSet := hRsub hyR
            have hdimx := flatPrismBlockBody_isPlankOfDimensions
              (V := V) (p := p) (Fz := Fz') hFzDims x hxF
            have hdimy := flatPrismBlockBody_isPlankOfDimensions
              (V := V) (p := p) (Fz := Fz') hFzDims y hyF
            change volume (F.outerBody x).carrier ≤
              (flatPrismBodyVolumeRatio.C Cw : ENNReal) * volume (F.outerBody y).carrier
            exact hdimx.volume_le_mul_volume hdim hCw (hσ.trans_le hσa)
              ((hσ.trans_le hσa).trans_le hab) hdimy) hj
        calc
          ((H.fiber j).card : ENNReal) * (W.outerSet.card : ENNReal) ≤
              2 * (flatPrismBodyVolumeRatio.C Cw : ENNReal) *
                (H.innerSet.card : ENNReal) := by
            simpa only [H, ShadedBody.FactorFamily.restrictOuter_outerSet] using hledger
          _ ≤ 2 * (flatPrismBodyVolumeRatio.C Cw : ENNReal) * (s.card : ENNReal) := by
            gcongr
            intro i hi
            simp only [H, GS, ShadedBody.selectedOuterScaleFamily, G,
              ShadedBody.FactorFamily.restrictOuter_innerSet, Finset.mem_filter] at hi
            simpa only [F, flatPrismFactorFamily_innerSet] using hi.1.1.1
      have hWcarrier0 :
          (∑ i ∈ W.innerSet, volume (W.innerBody i).carrier) ≠ 0 := by
        let j : FlatPrismBlock t := hWne.choose
        have hj : j ∈ W.outerSet := hWne.choose_spec
        obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero
          (Q.core.fiber_nonnull j hj)
        obtain ⟨i, hiWfib, _hxi⟩ := Set.mem_iUnion₂.mp hx
        have hiW : i ∈ W.innerSet :=
          (ShadedBody.mem_factorFamily_fiber_iff W.toFactorFamily j i).mp hiWfib |>.1
        have hiGSset : i ∈ GS.innerSet := by
          rw [Q.core.innerSet_eq] at hiW
          exact (Finset.mem_filter.mp hiW).1
        have hpos : 0 < volume (W.innerBody i).carrier := by
          rw [show (W.innerBody i).toConvexSpaceBody =
              (GS.innerBody i).toConvexSpaceBody from Q.core.inner_carrier i]
          exact hGSpos i hiGSset
        exact (hpos.trans_le
          (Finset.single_le_sum_of_canonicallyOrdered
            (f := fun k ↦ volume (W.innerBody k).carrier) hiW)).ne'
      obtain ⟨x₀, hx₀, hfullFiber⟩ :=
        ShadedBody.exists_fullness_le_fiber W.toFactorFamily hWne hWcarrier0
      change x₀ ∈ W.outerSet at hx₀
      let f := dimThreeLinearIsometryEquiv E hdim
      let K : FlatPrismBlock t → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        fun j ↦ (GS.outerBody j).mapLinearIsometryEquiv f
      let Y : FlatPrismBlock t → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
        fun j ↦ (W.outerBody j).mapLinearIsometryEquiv f
      have hKdim : ∀ j ∈ W.outerSet, IsPlankOfDimensions Cw a b (K j) := by
        intro j hj
        have hjS := hWsubS hj
        have hjR := hSsubR j hjS
        have hjF : j ∈ F.outerSet := hRsub hjR
        have hd := flatPrismBlockBody_isPlankOfDimensions
          (V := V) (p := p) (Fz := Fz') hFzDims j hjF
        apply IsPlankOfDimensions.mapLinearIsometryEquiv hd f
      have hKball : ∀ j ∈ W.outerSet,
          K j ≤ (ConvexSpaceBody.closedUnitBall :
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) := by
        intro j hj
        have hjS := hWsubS hj
        have hle : GS.outerBody j ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
          change G.outerBody j ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
          exact hWGK j hjS
        have hm := ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
          (K := GS.outerBody j) (L := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) f
        rw [ConvexSpaceBody.closedUnitBall_mapLinearIsometryEquiv] at hm
        exact hm.mpr hle
      have hYcarrier : ∀ j ∈ W.outerSet,
          (Y j).toConvexSpaceBody =
            (K j).cthickening (comparablePlankEnvelope.scaleRadius (K j) : ℝ) := by
        intro j _hj
        have houter := ShadedBody.outerThickFamilyAtScale_outerBody_toConvexSpaceBody
          GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos j
        dsimp only [Y, K]
        change (W.outerBody j).toConvexSpaceBody.mapLinearIsometryEquiv f = _
        rw [houter]
        let rj : NNReal :=
          ⟨(GS.outerBody j).scale, Metric.thickness_nonneg (GS.outerBody j).carrier _⟩
        have hrj : (rj : ℝ) = (GS.outerBody j).scale := rfl
        calc
          ((GS.outerBody j).cthickening (GS.outerBody j).scale).mapLinearIsometryEquiv f =
              ((GS.outerBody j).cthickening (rj : ℝ)).mapLinearIsometryEquiv f := by
                rw [hrj]
          _ = ((GS.outerBody j).mapLinearIsometryEquiv f).cthickening
                (rj : ℝ) := by
              exact ConvexSpaceBody.mapLinearIsometryEquiv_cthickening _ _ _
          _ = ((GS.outerBody j).mapLinearIsometryEquiv f).cthickening
                (comparablePlankEnvelope.scaleRadius
                  ((GS.outerBody j).mapLinearIsometryEquiv f) : ℝ) := by
              rw [comparablePlankEnvelope.coe_scaleRadius,
                ConvexSpaceBody.mapLinearIsometryEquiv_scale, hrj]
      let makeP : ∀ j, j ∈ W.outerSet → ShadedPlank a b hab hb1 := fun j hj ↦
        comparablePlankEnvelope.shadedPlank hCw hab hb1 (K j) (Y j)
          (hYcarrier j hj) (hKdim j hj).2.1.2 (hKdim j hj).2.2.2 (hKball j hj)
      let j₀ : FlatPrismBlock t := hWne.choose
      have hj₀ : j₀ ∈ W.outerSet := hWne.choose_spec
      let P : FlatPrismBlock t → ShadedPlank a b hab hb1 := fun j ↦
        if hj : j ∈ W.outerSet then makeP j hj else makeP j₀ hj₀
      have hP : ∀ j (hj : j ∈ W.outerSet), P j = makeP j hj := by
        intro j hj
        simp [P, hj]
      let rsh : ℝ := comparablePlankEnvelope.shrink Cw
      have hrsh : rsh ≠ 0 := comparablePlankEnvelope.shrink_coe_ne_zero hCw
      let U : FlatPrismBlock t → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
        fun j ↦ (Y j).homothety 0 hrsh
      have hPshade : ∀ j ∈ W.outerSet,
          (P j).shade = (U j).shade := by
        intro j hj
        rw [hP j hj]
        rfl
      have hUcarrier : ∀ j ∈ W.outerSet,
          (U j).toConvexSpaceBody = comparablePlankEnvelope.scaledCollar Cw (K j) := by
        intro j hj
        dsimp only [U, rsh]
        rw [ShadedBody.homothety_toConvexSpaceBody, hYcarrier j hj]
        rfl
      have hPwindow : ∀ j ∈ W.outerSet,
          (P j).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
        intro j hj
        rw [hP j hj]
        exact comparablePlankEnvelope.plank_carrier_subset_window hCw hab hb1 (hKball j hj)
      have hPvol : ∀ j ∈ W.outerSet,
          volume (P j).carrier ≤
            (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) * volume (U j).carrier := by
        intro j hj
        rw [hP j hj, hUcarrier j hj]
        exact (hKdim j hj).volume_plank_le_mul_scaledCollar hCw
          (hσ.trans_le hσa) ((hσ.trans_le hσa).trans_le hab) hab hb1
      have hfullReshape :
          fullness W.outerSet W.outerBody ≤
            flatPrismEnvelopeVolumeRatio.C Cw *
              fullness W.outerSet (fun j ↦ (P j).toShadedBody) := by
        have hmap : fullness W.outerSet Y = fullness W.outerSet W.outerBody := by
          simpa only [Y] using
            ShadedBody.fullness_mapLinearIsometryEquiv W.outerSet W.outerBody f
        have hhom : fullness W.outerSet U = fullness W.outerSet Y := by
          simpa only [U] using
            ShadedBody.fullness_homothety W.outerSet Y 0 hrsh
        calc
          fullness W.outerSet W.outerBody = fullness W.outerSet U := by
            rw [hhom, hmap]
          _ ≤ flatPrismEnvelopeVolumeRatio.C Cw *
              fullness W.outerSet (fun j ↦ (P j).toShadedBody) := by
            apply ShadedBody.fullness_le_mul_of_same_shade_of_sum_carrier_le
            · exact (zero_lt_one.trans_le (flatPrismEnvelopeVolumeRatio.one_le Cw)).ne'
            · exact fun j hj ↦ (hPshade j hj).symm
            · rw [Finset.mul_sum]
              exact Finset.sum_le_sum fun j hj ↦ hPvol j hj
      have hmultP :
          ShadedBody.multiplicity W.outerSet W.outerBody =
            ShadedBody.multiplicity W.outerSet (fun j ↦ (P j).toShadedBody) := by
        calc
          ShadedBody.multiplicity W.outerSet W.outerBody =
              ShadedBody.multiplicity W.outerSet Y := by
                symm
                simpa only [Y] using
                  ShadedBody.multiplicity_mapLinearIsometryEquiv W.outerSet W.outerBody f
          _ = ShadedBody.multiplicity W.outerSet U := by
                symm
                simpa only [U] using
                  ShadedBody.multiplicity_homothety W.outerSet Y 0 hrsh
          _ = ShadedBody.multiplicity W.outerSet (fun j ↦ (P j).toShadedBody) :=
            ShadedBody.multiplicity_congr_shade _ _ _ fun j hj ↦ (hPshade j hj).symm
      have hScaledKleP : ∀ j ∈ W.outerSet,
          (K j).homothety 0 rsh ≤ (P j).toConvexSpaceBody := by
        intro j hj
        rw [hP j hj]
        change (K j).homothety 0 rsh ≤
          (comparablePlankEnvelope.plank Cw a b hab hb1 (K j)).toConvexSpaceBody
        exact ((ConvexSpaceBody.homothety_le_homothety_iff 0 hrsh).mpr
          (ConvexSpaceBody.self_le_cthickening (K j)
            (comparablePlankEnvelope.scaleRadius (K j) : ℝ))).trans
          (comparablePlankEnvelope.scaledCollar_le_plank hCw hab hb1
            (hKdim j hj).2.1.2 (hKdim j hj).2.2.2 (hKball j hj))
      let Tm : ι → Tube σ (EuclideanSpace ℝ (Fin 3)) :=
        fun i ↦ (V i).toTube.mapLinearIsometryEquiv f
      let Rm : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)) :=
        fun k ↦ (Vρ k).mapLinearIsometryEquiv f
      let L : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        fun i ↦ ((Tm i).toConvexSpaceBody).homothety 0 rsh
      let par : FlatPrismBlock (ι := ι) t → κ := fun x ↦ x.1.1
      let A : NNReal := 8 * Cw
      have hA : 1 ≤ A := by
        calc
          1 ≤ 8 := by norm_num
          _ ≤ 8 * Cw := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hCw (by positivity : (0 : NNReal) ≤ 8)
      have hAcoe : (A : ℝ) = rsh⁻¹ := by
        dsimp only [A, rsh, comparablePlankEnvelope.shrink]
        push_cast
        rw [inv_inv]
      have hGSinner_sub_s : GS.innerSet ⊆ s := by
        intro i hi
        change i ∈ (G.restrictOuter S.selected).innerSet at hi
        have hiG : i ∈ G.innerSet := (Finset.mem_filter.mp hi).1
        change i ∈ (F.restrictOuter R.selected).innerSet at hiG
        have hiF : i ∈ F.innerSet := (Finset.mem_filter.mp hiG).1
        simpa only [F, flatPrismFactorFamily_innerSet] using hiF
      have hTmParent : ∀ i ∈ GS.innerSet,
          p i ∈ t ∧ (Tm i).toConvexSpaceBody ≤ Tube.dilate (Rm (p i)) (Dpar : ℝ) := by
        intro i hi
        have hiS : i ∈ s := hGSinner_sub_s hi
        refine ⟨hparent.mapsTo i hiS, ?_⟩
        have hm := ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
          (K := (V i).toConvexSpaceBody)
          (L := Tube.dilate (Vρ (p i)) (Dpar : ℝ)) f
        rw [Tube.mapLinearIsometryEquiv_dilate] at hm
        simpa only [Tm, Rm, Tube.mapLinearIsometryEquiv_toConvexSpaceBody] using
          hm.mpr (hparent.le_parent_dilate i hiS)
      have hRmED : (t : Set κ).Pairwise fun k l ↦
          IsEssentiallyDistinct (Rm k).carrier (Rm l).carrier := by
        intro k hk l hl hkl
        simpa only [Rm, Tube.mapLinearIsometryEquiv_carrier] using
          (hparent.pairwise hk hl hkl).mapLinearIsometryEquiv f
      have hOuterNC : ∀ C_NC : NNReal, 1 ≤ C_NC →
          Plank.IsThickeningNonconcentrated W.outerSet (fun j ↦ (P j).toPrism3D) C_NC
            (((edParentCount.COfTestDilate 3 Dpar 1
                (2 * (A * C_NC * Dpar))) * flatPrismOuterSplit.C Cw C_NC) * (b / a)) := by
        intro C_NC hC_NC
        apply isThickeningNonconcentrated_of_parentCountAtDilatedBodies_body
          (q := GS.innerSet) (T := L) (r := t) (assign := p)
          (Cu' := edParentCount.COfTestDilate 3 Dpar 1 (2 * (A * C_NC * Dpar)))
          (Csplit := flatPrismOuterSplit.C Cw C_NC) (W := P)
          (par := par) (H := fun j ↦ (K j).homothety 0 rsh)
        · intro j hj θ hθ1 _hθab
          let Qtest := (Plank.thickened (P j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC
          let QA := Qtest.homothety 0 A
          let parentsSmall := t.filter fun k ↦ ∃ i ∈ GS.innerSet,
            p i = k ∧ L i ≤ Qtest.toConvexSpaceBody
          let parentsScaled := t.filter fun k ↦ ∃ i ∈ GS.innerSet,
            p i = k ∧ (Tm i).toConvexSpaceBody ≤ QA.toConvexSpaceBody
          have hcount := edParentCount.card_assignedParents_le_homotheticDilatedThickenedPlank
            (hσ.trans_le hσρ) hρ1 hparent.one_le hA hC_NC hbρ
            GS.innerSet Tm t Rm p hRmED hTmParent (P j).toPrism3D θ hθ1
          have hsub :
              parentsSmall ⊆ parentsScaled := by
            intro k hk
            rcases Finset.mem_filter.mp hk with ⟨hkt, i, hiH, hik, hiL⟩
            refine Finset.mem_filter.mpr ⟨hkt, i, hiH, hik, ?_⟩
            apply (ConvexSpaceBody.homothety_le_homothety_iff 0 hrsh).mp
            change L i ≤ QA.toConvexSpaceBody.homothety 0 rsh
            have hQA : QA.toConvexSpaceBody.homothety 0 rsh = Qtest.toConvexSpaceBody := by
              refine ConvexSpaceBody.ext ?_
              change AffineMap.homothety 0 rsh '' QA.carrier = Qtest.carrier
              have hApos : 0 < A := zero_lt_one.trans_le hA
              have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast hApos.ne'
              have hrsheq : rsh = ((A : ℝ))⁻¹ := by rw [hAcoe, inv_inv]
              rw [hrsheq]
              change AffineMap.homothety 0 (A : ℝ)⁻¹ ''
                (Qtest.homothety 0 A).carrier = Qtest.carrier
              rw [PrismNDim.carrier_homothety Qtest 0 hApos]
              exact homothety_inv_image_homothety_image 0 hA0 _
            rw [hQA]
            exact hiL
          have hcardSub :
              (parentsSmall.card : NNReal) ≤ (parentsScaled.card : NNReal) := by
            exact_mod_cast Finset.card_le_card hsub
          have hcount' :
              (parentsScaled.card : NNReal) ≤
                edParentCount.COfTestDilate 3 Dpar 1
                  (2 * (A * C_NC * Dpar)) := by
            exact_mod_cast (show
              (parentsScaled.card : ENNReal) ≤
                (edParentCount.COfTestDilate 3 Dpar 1
                  (2 * (A * C_NC * Dpar)) : ENNReal) by
              simpa only [parentsScaled, Qtest, QA] using hcount)
          convert hcardSub.trans hcount' using 1
          norm_cast
          congr 1
          ext k
          simp only [parentsSmall, Qtest, Finset.mem_filter]
        · intro x hx
          exact x.1.2
        · intro x hx
          have hxGS : x ∈ GS.outerSet :=
            ShadedBody.outerThickFamilyAtScale_outerSet_subset GS hσ
              (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos hx
          letI : DecidableEq (FlatPrismBlock (ι := ι) t) := Classical.decEq _
          obtain ⟨i, hiFib⟩ := hGSfiber x hxGS
          have hiGS : i ∈ GS.innerSet := (Finset.mem_filter.mp hiFib).1
          have hipx : GS.parent i = x := (Finset.mem_filter.mp hiFib).2
          refine ⟨i, hiGS, ?_, ?_⟩
          · have hiS : i ∈ s := hGSinner_sub_s hiGS
            have hpblock : flatPrismBlockOf V p hparent.mapsTo Fz' hfamily.nonempty i = x := by
              exact hipx
            have hfirst := congrArg (fun z : FlatPrismBlock t ↦ z.1.1) hpblock
            simpa [flatPrismBlockOf, hiS, par] using hfirst
          · have hiCarrier := GS.inner_le_parent i hiGS
            have hmap := ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff
              (K := (GS.innerBody i).toConvexSpaceBody) (L := GS.outerBody (GS.parent i)) f
            have hmapped := hmap.mpr hiCarrier
            have hInnerEq : (GS.innerBody i).toConvexSpaceBody =
                (V i).toConvexSpaceBody := rfl
            rw [hInnerEq, hipx] at hmapped
            apply (ConvexSpaceBody.homothety_le_homothety_iff 0 hrsh).mpr
            simpa only [L, Tm, K, Tube.mapLinearIsometryEquiv_toConvexSpaceBody, hipx] using hmapped
        · exact hScaledKleP
        · intro j hj θ hθ1 _hθab k hk
          letI : DecidableEq (FlatPrismBlock (ι := ι) t) := Classical.decEq _
          let pred : FlatPrismBlock (ι := ι) t → Prop := fun x ↦
            ((P x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              (((Plank.thickened (P j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
                Set (EuclideanSpace ℝ (Fin 3))) ∧ par x = k
          letI : DecidablePred pred := Classical.decPred pred
          let kp : FlatPrismParent t := ⟨k, hk⟩
          let Kpart : Finset ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := fun part ↦
            (part.convexHull_biUnion (fun i ↦ (V i).toConvexSpaceBody)).mapLinearIsometryEquiv f
          have hKTpart : IsKatzTao (Fz' kp).parts Kpart 2 := by
            exact (Fz' kp).isKatzTao.mapLinearIsometryEquiv f
          have hdimpart : ∀ part ∈ (Fz' kp).parts,
              IsPlankOfDimensions Cw a b (Kpart part) := by
            intro part hpart
            exact (hFzDims kp part hpart).mapLinearIsometryEquiv f
          have hparts := card_le_of_isKatzTao_scaledComparableBodies hCw
            (hσ.trans_le hσa) ((hσ.trans_le hσa).trans_le hab) (Fz' kp).parts Kpart
            hKTpart hdimpart C_NC (P j) hθ1
          let test := ((Plank.thickened (P j).toPrism3D θ hθ1).toPrismNDim.dilation
            C_NC).toConvexSpaceBody
          let cells : Finset (FlatPrismBlock (ι := ι) t) := by
            exact W.outerSet.filter pred
          let parts := (Fz' kp).parts.filter fun part ↦
            (Kpart part).homothety 0 rsh ≤ test
          have hcardNat : cells.card ≤ parts.card := by
            apply Finset.card_le_card_of_injOn (fun x : FlatPrismBlock t ↦ x.2)
            · intro x hx
              have hxcells := Finset.mem_filter.mp hx
              have hxW := hxcells.1
              have hxk : x.1.1 = k := hxcells.2.2
              have hxF : x ∈ F.outerSet := hRsub (hSsubR _ (hWsubS hxW))
              have hxpart : x.2 ∈ (Fz' x.1).parts := by
                change x ∈ flatPrismBlocks V p Fz' at hxF
                simpa only [flatPrismBlocks, Finset.mem_sigma, Finset.mem_attach, true_and] using hxF
              have hxpar : x.1 = kp := Subtype.ext hxk
              have hxKpart : Kpart x.2 = K x := rfl
              refine Finset.mem_filter.mpr ⟨?_, ?_⟩
              · rw [← hxpar]
                exact hxpart
              · rw [hxKpart]
                exact (hScaledKleP x hxW).trans hxcells.2.1
            · intro x hx y hy hxy
              have hxk : x.1.1 = k := (Finset.mem_filter.mp hx).2.2
              have hyk : y.1.1 = k := (Finset.mem_filter.mp hy).2.2
              have hfirst : x.1 = y.1 := Subtype.ext (hxk.trans hyk.symm)
              exact Sigma.ext hfirst (heq_of_eq hxy)
          have hcardNN : (cells.card : NNReal) ≤ (parts.card : NNReal) := by
            exact_mod_cast hcardNat
          have hparts' : (parts.card : NNReal) ≤
              flatPrismOuterSplit.C Cw C_NC * (b / a) * θ := by
            simpa only [parts, Kpart, test, rsh] using hparts
          convert hcardNN.trans hparts' using 1
          norm_cast
          congr 1
          ext x
          simp only [cells, pred, Finset.mem_filter]
      have hx₀S : x₀ ∈ S.selected := hWsubS hx₀
      have hx₀GS : x₀ ∈ GS.outerSet := by
        simpa only [GS, ShadedBody.selectedOuterScaleFamily,
          ShadedBody.FactorFamily.restrictOuter_outerSet] using hx₀S
      have hWinnerSet : W.innerSet =
          {i ∈ GS.innerSet | GS.parent i ∈ W.outerSet} := by
        simpa only [W] using
          (ShadedBody.outerThickFamilyAtScale_innerSet_eq_filter
            GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos)
      have hWparent : W.parent = GS.parent := by
        simpa only [W] using
          (ShadedBody.outerThickFamilyAtScale_parent
            GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos)
      have hWfibEq : W.fiber x₀ = GS.fiber x₀ := by
        apply Finset.ext
        intro i
        constructor
        · intro hi
          obtain ⟨hiW, hpi⟩ :=
            (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mp hi
          have hiGS : i ∈ GS.innerSet := by
            change i ∈ W.innerSet at hiW
            rw [hWinnerSet] at hiW
            exact (Finset.mem_filter.mp hiW).1
          exact (ShadedBody.mem_factorFamily_fiber_iff GS x₀ i).mpr
            ⟨hiGS, by simpa only [hWparent] using hpi⟩
        · intro hi
          obtain ⟨hiGS, hpi⟩ :=
            (ShadedBody.mem_factorFamily_fiber_iff GS x₀ i).mp hi
          have hiW : i ∈ W.innerSet := by
            rw [hWinnerSet]
            exact Finset.mem_filter.mpr ⟨hiGS, by simpa only [hpi] using hx₀⟩
          exact (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mpr
            ⟨hiW, by simpa only [hWparent] using hpi⟩
      have hFrGS : GS.HasFrostmanFibers 2 :=
        ((flatPrismFactorFamily_hasFrostmanFibers V p hparent.mapsTo Fz'
          hfamily.nonempty).restrictOuter R.selected hRsub).restrictOuter S.selected
            (S.selected_subset.trans G.innerSet_image_parent_subset_outerSet)
      have hFrW : IsFrostmanIn (W.fiber x₀)
          (fun i ↦ (W.innerBody i).toConvexSpaceBody) (GS.outerBody x₀) 2 := by
        have hbase := hFrGS x₀ hx₀GS
        rw [← hWfibEq] at hbase
        have hbodies : (fun i ↦ (W.innerBody i).toConvexSpaceBody) =
            (fun i ↦ (GS.innerBody i).toConvexSpaceBody) :=
          funext Q.core.inner_carrier
        rw [hbodies]
        exact hbase
      let Tin : ι → ShadedTube σ (EuclideanSpace ℝ (Fin 3)) := fun i =>
        { toTube := Tm i
          shade := ((W.innerBody i).mapLinearIsometryEquiv f).shade
          measurableSet_shade := ((W.innerBody i).mapLinearIsometryEquiv f).measurableSet_shade
          shade_subset := by
            have hs := ((W.innerBody i).mapLinearIsometryEquiv f).shade_subset
            change ((W.innerBody i).mapLinearIsometryEquiv f).shade ⊆ (Tm i).carrier
            rw [show (Tm i).carrier =
                ((W.innerBody i).mapLinearIsometryEquiv f).carrier by
              change ((V i).toTube.mapLinearIsometryEquiv f).carrier =
                ((W.innerBody i).mapLinearIsometryEquiv f).carrier
              rw [ShadedBody.mapLinearIsometryEquiv_carrier,
                Tube.mapLinearIsometryEquiv_carrier]
              congr 1
              exact congrArg ConvexSpaceBody.carrier
                (ShadedBody.outerThickFamilyAtScale_innerBody_toConvexSpaceBody
                  GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos i).symm]
            exact hs }
      have hTinConvex : ∀ i,
          (Tin i).toConvexSpaceBody =
            ((W.innerBody i).toConvexSpaceBody).mapLinearIsometryEquiv f := by
        intro i
        change (Tm i).toConvexSpaceBody =
          ((W.innerBody i).toConvexSpaceBody).mapLinearIsometryEquiv f
        change ((V i).mapLinearIsometryEquiv f).toConvexSpaceBody =
          ((W.innerBody i).toConvexSpaceBody).mapLinearIsometryEquiv f
        rw [ShadedTube.mapLinearIsometryEquiv_toConvexSpaceBody]
        rw [ShadedBody.outerThickFamilyAtScale_innerBody_toConvexSpaceBody
          GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos]
        rfl
      let Ain := comparablePlankEnvelope.bodyThin Cwi a
      let Bin := comparablePlankEnvelope.bodyWide Cwi b
      let Pin : Plank Ain Bin
          (comparablePlankEnvelope.bodyThin_le_bodyWide hab hCwia)
          (comparablePlankEnvelope.bodyWide_le_one Cwi b) :=
        comparablePlankEnvelope.bodyPlank Cwi a b hab hCwia (K x₀)
      have hKdimInner : IsPlankOfDimensions Cwi a b (K x₀) :=
        (hKdim x₀ hx₀).mono_constant hCwCwi
      have hKlePin : K x₀ ≤ Pin.toConvexSpaceBody := by
        exact comparablePlankEnvelope.body_le_bodyPlank hab hCwia
          hKdimInner.2.1.2 hKdimInner.2.2.2 (hKball x₀ hx₀)
      have hTinK : ∀ i ∈ W.fiber x₀,
          (Tin i).toConvexSpaceBody ≤ K x₀ := by
        intro i hi
        have hiW : i ∈ W.innerSet :=
          (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mp hi |>.1
        have hp : W.parent i = x₀ :=
          (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mp hi |>.2
        rw [hTinConvex i]
        have hiGS : i ∈ GS.innerSet := by
          change i ∈ W.innerSet at hiW
          rw [hWinnerSet] at hiW
          exact (Finset.mem_filter.mp hiW).1
        have hpar : GS.parent i = x₀ := by simpa only [hWparent] using hp
        apply (ConvexSpaceBody.mapLinearIsometryEquiv_le_mapLinearIsometryEquiv_iff f).2
        rw [ShadedBody.outerThickFamilyAtScale_innerBody_toConvexSpaceBody
          GS hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos]
        simpa only [hpar] using GS.inner_le_parent i hiGS
      have hTinPin : ∀ i ∈ W.fiber x₀,
          (Tin i).toConvexSpaceBody ≤ Pin.toConvexSpaceBody :=
        fun i hi ↦ (hTinK i hi).trans hKlePin
      have hFrTin : IsFrostmanIn (W.fiber x₀)
          (fun i ↦ (Tin i).toConvexSpaceBody) Pin.toConvexSpaceBody
          (flatPrismInnerFrostman.C Cwi : ENNReal) := by
        have hmapped := hFrW.mapLinearIsometryEquiv f
        have hfrK : IsFrostmanIn (W.fiber x₀)
            (fun i ↦ (Tin i).toConvexSpaceBody) (K x₀)
            2 := by
          simpa only [hTinConvex, K] using hmapped
        exact hKdimInner.frostmanIn_bodyPlank hCwi
          (hσ.trans_le hσa) ((hσ.trans_le hσa).trans_le hab) hab hCwia
          (hKball x₀ hx₀) hTinK hfrK
      have hWfiber_ne : (W.fiber x₀).Nonempty := by
        obtain ⟨z, hz⟩ := MeasureTheory.nonempty_of_measure_ne_zero
          (Q.core.fiber_nonnull x₀ hx₀)
        obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp hz
        exact ⟨i, hi⟩
      have hWfiber_sub_s : W.fiber x₀ ⊆ s := by
        intro i hi
        have hiW := (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mp hi |>.1
        rw [hWinnerSet] at hiW
        exact hGSinner_sub_s (Finset.mem_filter.mp hiW).1
      have hTinED : (W.fiber x₀ : Set ι).Pairwise
          (fun i j ↦ IsEssentiallyDistinct (Tin i).carrier (Tin j).carrier) := by
        intro i hi j hj hij
        change IsEssentiallyDistinct
          ((V i).toTube.mapLinearIsometryEquiv f).carrier
          ((V j).toTube.mapLinearIsometryEquiv f).carrier
        rw [Tube.mapLinearIsometryEquiv_carrier, Tube.mapLinearIsometryEquiv_carrier]
        exact (hfamily.essDistinct (hWfiber_sub_s hi) (hWfiber_sub_s hj) hij).mapLinearIsometryEquiv f
      have hAin_pos : 0 < Ain := by
        dsimp only [Ain, comparablePlankEnvelope.bodyThin]
        exact mul_pos hCwipos (hσ.trans_le hσa)
      have hσAin : σ ≤ Ain := by
        dsimp only [Ain, comparablePlankEnvelope.bodyThin]
        calc
          σ ≤ a := hσa
          _ = 1 * a := by rw [one_mul]
          _ ≤ Cwi * a := by gcongr
      have hbBin : b ≤ Bin := by
        exact comparablePlankEnvelope.le_bodyWide hCwi hb1
      have hσBin : σ ≤ 1 * Bin := by
        simpa only [one_mul] using hσa.trans (hab.trans hbBin)
      have hCexpandCwi : Cexpand ≤ Cwi := by
        dsimp only [Cwi]
        exact le_mul_of_one_le_right (by positivity) hCw
      have hb₀64Cwi : 1 ≤ b₀64I * Cwi := by
        have hb0 : b₀64I ≠ 0 := hb₀64I.ne'
        calc
          1 = b₀64I * b₀64I⁻¹ := (mul_inv_cancel₀ hb0).symm
          _ ≤ b₀64I * Cwi := by gcongr; exact hb₀64inv.trans hCexpandCwi
      have hσbAin : σ ≤ b₀64I * Ain := by
        calc
          σ ≤ a := hσa
          _ = 1 * a := by rw [one_mul]
          _ ≤ (b₀64I * Cwi) * a := by gcongr
          _ = b₀64I * Ain := by
            dsimp only [Ain, comparablePlankEnvelope.bodyThin]
            ring
      have hbGeomCwi : 1 ≤ bGeom * Cwi := by
        have hb0 : bGeom ≠ 0 := hbGeom.ne'
        calc
          1 = bGeom * bGeom⁻¹ := (mul_inv_cancel₀ hb0).symm
          _ ≤ bGeom * Cwi := by gcongr; exact hbGeominv.trans hCexpandCwi
      have hσGeomAin : σ ≤ bGeom * Ain := by
        calc
          σ ≤ a := hσa
          _ = 1 * a := by rw [one_mul]
          _ ≤ (bGeom * Cwi) * a := by gcongr
          _ = bGeom * Ain := by
            dsimp only [Ain, comparablePlankEnvelope.bodyThin]
            ring
      have hσGeomR : (σ : ℝ) ≤ δGeom := by
        have hcast : (σ : ℝ) < (Real.toNNReal δGeom : ℝ) := by exact_mod_cast hσGeom.2
        simpa [Real.coe_toNNReal _ hδGeom.le] using hcast.le
      obtain ⟨aI, bI, haIbI, hbI1, ιI, qI, PI, haI, hbI, haIpos, hσaI,
          hbIb₀, hratioI, hratioIE, hPIwindow, hPIED, hcardI, hcardIsub,
          hfullI, hmaxI, hslabI, hNCI, hmultI⟩ :=
        hinnerED hσ hAin_pos hσAin hσGeomR 1 b₀64I hσBin hσbAin
          hσGeomAin Pin (W.fiber x₀) Tin hWfiber_ne hTinPin hTinED
      have hFrPI : IsFrostmanIn qI (fun i ↦ (PI i).toConvexSpaceBody)
          plankWindow (flatPrismInnerNormalisedFrostman.C Cnorm dED
            (flatPrismInnerFrostman.C Cwi : ENNReal)) := by
        exact innerNormalised_isFrostmanIn hσ hAin_pos hσAin Pin (W.fiber x₀) Tin
          hTinPin hFrTin haI hbI Cnorm dED qI PI hPIwindow hcardI hmaxI
      let CFI : ENNReal := flatPrismInnerNormalisedFrostman.C Cnorm dED
        (flatPrismInnerFrostman.C Cwi : ENNReal)
      have hCFI1 : 1 ≤ CFI := by
        dsimp only [CFI, flatPrismInnerNormalisedFrostman.C]
        have hd1 : (1 : ENNReal) ≤ (dED : ENNReal) + 1 := by simp
        exact one_le_mul
          (one_le_mul (one_le_mul (by exact_mod_cast hCnorm) hd1)
            (by exact_mod_cast flatPrismInnerFrostman.one_le Cwi))
          one_le_volume_plankWindow
      have hCFItop : CFI ≠ ⊤ := by
        dsimp only [CFI, flatPrismInnerNormalisedFrostman.C]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top ENNReal.coe_ne_top (by finiteness)) ENNReal.coe_ne_top)
          plankWindow.isCompact.measure_ne_top
      let MI : NNReal := Cinner * (Bin / Ain) ^ 2
      have hMI1 : 1 ≤ MI := by
        have hratio1 : 1 ≤ Bin / Ain := by
          rw [le_div_iff₀ hAin_pos]
          simpa only [one_mul] using
            comparablePlankEnvelope.bodyThin_le_bodyWide hab hCwia
        exact one_le_mul hCinner (one_le_pow₀ hratio1)
      have hfullPI : σ ^ η64I ≤
          ShadedBody.fullness qI (fun i ↦ (PI i).toShadedBody) := by
        let cDen : NNReal :=
          (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent)⁻¹
        let cScale : NNReal :=
          (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar))⁻¹
        let cRef : NNReal := (cDen * cScale) * Lcore.refinementConstant
        let cNorm : NNReal := Cnorm * ((dED : NNReal) + 1)
        have hRref : ShadedBody.IsCRefinement G.innerSet G.innerBody
            F.innerSet F.innerBody cDen := by
          simpa only [cDen, G] using R.selection_refinement F hσ hdisc D hmass
        have hQref : ShadedBody.IsCRefinement GS.innerSet GS.innerBody
            G.innerSet G.innerBody cScale := by
          simpa only [cScale, GS] using
            Q.selection_refinement G hσ hdiscG DG hσB hupperG hmassG
        have hrefAll : ShadedBody.IsCRefinement W.innerSet W.innerBody
            F.innerSet F.innerBody cRef := by
          simpa only [cRef] using hrefW.trans (hQref.trans hRref)
        have hfullRef := hrefAll.coe_mul_fullness_le
        have hfullOriginal : (σ : ENNReal) ^ η ≤
            (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) := by
          simpa only [F, flatPrismFactorFamily_innerSet,
            flatPrismFactorFamily_innerBody] using hfamily.fullness
        have hfullIE : (ShadedBody.fullness (W.fiber x₀)
              (fun i ↦ (Tin i).toShadedBody) : ENNReal) ≤
            (cNorm : ENNReal) *
              (ShadedBody.fullness qI (fun i ↦ (PI i).toShadedBody) : ENNReal) := by
          have hcNorm : cNorm = Cnorm * ((dED + 1 : ℕ) : NNReal) := by
            simp only [cNorm, Nat.cast_add, Nat.cast_one]
          rw [hcNorm]
          exact_mod_cast hfullI
        have hTinFullness : ShadedBody.fullness (W.fiber x₀)
            (fun i ↦ (Tin i).toShadedBody) =
            ShadedBody.fullness (W.fiber x₀) W.innerBody := by
          unfold ShadedBody.fullness ShadedBody.fullness'
          have hshade : (∑ i ∈ W.fiber x₀, volume (Tin i).shade) =
              ∑ i ∈ W.fiber x₀, volume (W.innerBody i).shade := by
            apply Finset.sum_congr rfl
            intro i hi
            change volume (f '' (W.innerBody i).shade) = volume (W.innerBody i).shade
            exact volume_image_linearIsometryEquiv f (W.innerBody i).shade
          have hcarrier : (∑ i ∈ W.fiber x₀, volume (Tin i).carrier) =
              ∑ i ∈ W.fiber x₀, volume (W.innerBody i).carrier := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [show (Tin i).toConvexSpaceBody =
              ((W.innerBody i).toConvexSpaceBody).mapLinearIsometryEquiv f from hTinConvex i]
            exact ConvexSpaceBody.volume_mapLinearIsometryEquiv
              (W.innerBody i).toConvexSpaceBody f
          rw [hshade, hcarrier]
        have hchain : (cRef : ENNReal) * (σ : ENNReal) ^ η ≤
            (cNorm : ENNReal) *
              (ShadedBody.fullness qI (fun i ↦ (PI i).toShadedBody) : ENNReal) := by
          calc
            (cRef : ENNReal) * (σ : ENNReal) ^ η ≤
                (cRef : ENNReal) *
                  (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) := by gcongr
            _ ≤ (ShadedBody.fullness W.innerSet W.innerBody : ENNReal) := hfullRef
            _ ≤ (ShadedBody.fullness (W.fiber x₀) W.innerBody : ENNReal) := hfullFiber
            _ = (ShadedBody.fullness (W.fiber x₀)
                (fun i ↦ (Tin i).toShadedBody) : ENNReal) := by
              exact_mod_cast hTinFullness.symm
            _ ≤ _ := hfullIE
        have hBactual : max 1 (2 * Dpar) = 2 * Dpar := by
          apply max_eq_right
          calc
            (1 : NNReal) ≤ 2 := by norm_num
            _ ≤ 2 * Dpar := by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hparent.one_le (by positivity)
        have hScaleLoss' :
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) ≤
              (σ : ENNReal) ^ (-eFund) := by
          simpa only [hBactual] using hScaleLossMax
        have hCard : (s.card : ℝ) ≤ (σ : ℝ) ^ (-(7 : ℝ)) :=
          hCardLoss s (fun i ↦ (V i).toTube) hfamily.ball hfamily.essDistinct
        have hFcard : 0 < F.innerSet.card := by
          simpa only [F, flatPrismFactorFamily_innerSet] using hfamily.nonempty.card_pos
        have hFcardBound : (F.innerSet.card : ℝ) ≤ (σ : ℝ) ^ (-(7 : ℝ)) := by
          simpa only [F, flatPrismFactorFamily_innerSet] using hCard
        have hDexp : ((D.exponent + 1 : ℕ) : ENNReal) ≤
            (σ : ENNReal) ^ (-(eFund / 4)) := by
          rw [show D.exponent = flatPrismVolumeRatioExponent Dpar σ by
            exact flatPrismFactorFamily_volumeRatio_dilate_controlled_exponent V p
              hparent.mapsTo Fz' hfamily.nonempty hdim hσ
              (hσhalfNN.trans (by norm_num)) hρ1 hfamily.ball Vρ hparent.le_parent_dilate]
          exact hVolumeExponent
        have hDensityLoss' :
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) ≤
              (σ : ENNReal) ^ (-eFund) :=
          hDensityLoss F.innerSet.card D.exponent hFcard hFcardBound hDexp
        have hGSne : GS.innerSet.Nonempty := by
          obtain ⟨i, hi⟩ := hWfiber_ne
          have hiW := (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mp hi |>.1
          rw [hWinnerSet] at hiW
          exact ⟨i, (Finset.mem_filter.mp hiW).1⟩
        have hGScardBound : (GS.innerSet.card : ℝ) ≤ (σ : ℝ) ^ (-(7 : ℝ)) := by
          calc
            (GS.innerSet.card : ℝ) ≤ (s.card : ℝ) := by
              exact_mod_cast Finset.card_le_card hGSinner_sub_s
            _ ≤ _ := hCard
        have hw₁1 : w₁ ≤ 1 := by
          let jsel := S.selected_nonempty.choose
          have hjsel : jsel ∈ S.selected := S.selected_nonempty.choose_spec
          have hjselG : jsel ∈ G.innerSet.image G.parent := S.selected_subset hjsel
          have hbody : G.outerBody jsel ≤
              (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := hWGK jsel hjsel
          have hscale : (G.outerBody jsel).scale ≤ (1 : ℝ) := by
            exact Metric.thickness_le_of_subset_closedBall hbody (by norm_num)
              (Module.finrank ℝ E - 1)
          have hscale0 : 0 ≤ (G.outerBody jsel).scale :=
            Metric.thickness_nonneg (G.outerBody jsel).carrier _
          rw [← NNReal.coe_le_coe]
          change (Real.toNNReal (G.outerBody jsel).scale : ℝ) ≤ (1 : NNReal)
          rw [Real.coe_toNNReal _ hscale0]
          exact_mod_cast hscale
        have hDGSexp : DGS.exponent = D.exponent := rfl
        have hPipelineLoss' :
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                DGS.exponent w₁ : ENNReal) ≤ (σ : ENNReal) ^ (-eFund) := by
          apply hPipelineLoss GS.innerSet.card DGS.exponent hGSne.card_pos hGScardBound
          · simpa only [hDGSexp] using hDexp
          · exact ShadedBody.le_selectedOuterScale G hσ hdiscG hσB hupperG hmassG
          · exact hw₁1
        have hLref : Lcore.refinementConstant =
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁)⁻¹ := by
          simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform, hdim] using
            ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv
              3 GS.innerSet.card DGS.exponent w₁
        have hDenNN0 :
            ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent ≠ 0 := by
          intro hz
          have hle := R.mass_refinement
          rw [hz, ENNReal.coe_zero, zero_mul] at hle
          exact (not_le_of_gt hmass) hle
        have hScaleNN0 : ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) ≠ 0 := by
          intro hz
          have hle := Q.selection_mass
          rw [hz, ENNReal.coe_zero, zero_mul] at hle
          exact (not_le_of_gt hmassG) hle
        have hdiscGS : GS.InnerIsDiscretizedAtScale σ := by
          simpa only [GS, ShadedBody.selectedOuterScaleFamily] using
            hdiscG.restrictOuter S.selected
        have hLpos : 0 < Lcore.refinementConstant := by
          simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform] using
            ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos
              hσ hdiscGS DGS w₁ Q.scale_pos hWne
        have hPipeNN0 :
            ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ ≠ 0 := by
          have hinvpos : 0 <
              (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                DGS.exponent w₁)⁻¹ := by simpa only [← hLref] using hLpos
          exact (inv_pos.mp hinvpos).ne'
        have hcRefNN0 : cRef ≠ 0 := by
          dsimp only [cRef, cDen, cScale]
          rw [hLref]
          exact mul_ne_zero (mul_ne_zero (inv_ne_zero hDenNN0) (inv_ne_zero hScaleNN0))
            (inv_ne_zero hPipeNN0)
        have hcRefInv : (cRef : ENNReal)⁻¹ =
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
              (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) := by
          rw [← ENNReal.coe_inv hcRefNN0]
          norm_cast
          dsimp only [cRef, cDen, cScale]
          rw [hLref, mul_inv_rev, mul_inv_rev]
          simp only [inv_inv]
          ring
        have hLoss : (cNorm : ENNReal) * (cRef : ENNReal)⁻¹ ≤
            (σ : ENNReal) ^ (-(4 * eFund)) := by
          rw [hcRefInv]
          calc
            (cNorm : ENNReal) *
              ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                  (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal)) ≤
                (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-eFund) *
                  (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-eFund) := by
              simpa only [mul_assoc] using mul_le_mul
                (mul_le_mul
                  (mul_le_mul (by simpa [cNorm, cNormLoss] using hNormLoss.2.2)
                    hDensityLoss' bot_le bot_le)
                  hScaleLoss' bot_le bot_le)
                hPipelineLoss' bot_le bot_le
            _ = (σ : ENNReal) ^ (-(4 * eFund)) := by
              repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              congr 1
              ring
        have hcRef0 : (cRef : ENNReal) ≠ 0 := by
          rw [← ENNReal.inv_ne_top]
          rw [hcRefInv]
          exact ENNReal.mul_ne_top
            (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) ENNReal.coe_ne_top
        have hηfund : η ≤ η64I - 4 * eFund := by
          dsimp only [eFund]
          linarith [hη64I_le]
        have hfund : (cNorm : ENNReal) * (σ : ENNReal) ^ η64I ≤
            (cRef : ENNReal) * (σ : ENNReal) ^ η := by
          calc
            (cNorm : ENNReal) * (σ : ENNReal) ^ η64I =
                (cRef : ENNReal) * ((cNorm : ENNReal) * (cRef : ENNReal)⁻¹) *
                  (σ : ENNReal) ^ η64I := by
              calc
                (cNorm : ENNReal) * (σ : ENNReal) ^ η64I =
                    (cNorm : ENNReal) * 1 * (σ : ENNReal) ^ η64I := by rw [mul_one]
                _ = (cNorm : ENNReal) * ((cRef : ENNReal) * (cRef : ENNReal)⁻¹) *
                    (σ : ENNReal) ^ η64I := by
                  rw [ENNReal.mul_inv_cancel hcRef0 ENNReal.coe_ne_top]
                _ = _ := by ac_rfl
            _ ≤ (cRef : ENNReal) * (σ : ENNReal) ^ (-(4 * eFund)) *
                (σ : ENNReal) ^ η64I := by gcongr
            _ = (cRef : ENNReal) * (σ : ENNReal) ^ (η64I - 4 * eFund) := by
              calc
                (cRef : ENNReal) * (σ : ENNReal) ^ (-(4 * eFund)) *
                    (σ : ENNReal) ^ η64I =
                    (cRef : ENNReal) *
                      ((σ : ENNReal) ^ (-(4 * eFund)) *
                        (σ : ENNReal) ^ η64I) := by ring
                _ = _ := by
                  rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                    ENNReal.coe_ne_top]
                  congr 2
                  ring
            _ ≤ (cRef : ENNReal) * (σ : ENNReal) ^ η := by
              have hσE1 : (σ : ENNReal) ≤ 1 := by exact_mod_cast hNormLoss.2.1
              exact mul_le_mul_left' (ENNReal.rpow_le_rpow_of_exponent_ge
                hσE1 hηfund) _
        have hmul : (cNorm : ENNReal) * (σ : ENNReal) ^ η64I ≤
            (cNorm : ENNReal) *
              (ShadedBody.fullness qI (fun i ↦ (PI i).toShadedBody) : ENNReal) :=
          hfund.trans hchain
        have hcNorm0 : (cNorm : ENNReal) ≠ 0 := by
          exact ENNReal.coe_ne_zero.mpr (mul_ne_zero
            (zero_lt_one.trans_le hCnorm).ne' (by positivity))
        have hcNormTop : (cNorm : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        have hout : (σ : ENNReal) ^ η64I ≤
            (ShadedBody.fullness qI (fun i ↦ (PI i).toShadedBody) : ENNReal) :=
          (ENNReal.mul_le_mul_iff_left hcNorm0 hcNormTop).mp (by
            simpa only [mul_comm] using hmul)
        rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_ne_zero hσ.ne']
        exact hout
      have hinner64 := h64I qI haIbI hbI1 PI hσ hσaI hbIb₀ hPIwindow hPIED
        hfullPI MI hMI1 hNCI CFI hCFI1 hCFItop hFrPI
      let Cextract : NNReal :=
        edParentCount.COfTestDilate 3 Dpar 1 (2 * (A * 11 * Dpar)) *
          flatPrismOuterSplit.C Cw 11
      have hOuterNC11 : Plank.IsThickeningNonconcentrated W.outerSet
          (fun j ↦ (P j).toPrism3D) 11 (Cextract * (b / a)) := by
        simpa only [Cextract] using hOuterNC 11 (by norm_num)
      let dO : ℕ := ⌈(Cextract : ℝ)⌉₊
      obtain ⟨qO, hqOsub, hqOED, hqOcard, hrefO⟩ :=
        exists_pairwise_plank_CRefinement_of_isThickeningNonconcentrated
          (hσ.trans_le hσa) ((hσ.trans_le hσa).trans_le hab) (by norm_num)
          W.outerSet P hOuterNC11
      have hqOne : qO.Nonempty := by
        by_contra hqOempty
        rw [Finset.not_nonempty_iff_eq_empty.mp hqOempty, Finset.card_empty, Nat.mul_zero] at hqOcard
        exact hWne.ne_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hqOcard))
      have hqOcard0 : qO.card ≠ 0 := hqOne.card_ne_zero
      have hmultqO : ShadedBody.multiplicity W.outerSet
          (fun j ↦ (P j).toShadedBody) ≤
            ((dO + 1 : ℕ) : ENNReal) *
              ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) := by
        have hd0 : ((dO + 1 : ℕ) : NNReal) ≠ 0 := by positivity
        have hinv0 : ((dO + 1 : ℕ) : NNReal)⁻¹ ≠ 0 := inv_ne_zero hd0
        have hraw := ShadedBody.multiplicity_le_of_isCRefinement W.outerSet
          (fun j ↦ (P j).toShadedBody) hinv0
          (by simpa only [dO] using hrefO)
        have hraw' : ShadedBody.multiplicity W.outerSet
            (fun j ↦ (P j).toShadedBody) ≤
              (((dO + 1 : ℕ) : NNReal) : ENNReal) *
                ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) := by
          simpa only [ENNReal.coe_inv hd0, inv_inv] using hraw
        convert hraw' using 1 <;> norm_cast
      let retainedOuter : ENNReal :=
        (Lcore.refinementConstant : ENNReal) *
          (ShadedBody.fullness GS.innerSet GS.innerBody : ENNReal)
      have hLcoreRef0 : (Lcore.refinementConstant : ENNReal) ≠ 0 := by
        apply ENNReal.coe_ne_zero.mpr
        simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform,
          ShadedBody.FactoringAtScaleLossBound.refinementConstant] using
            (ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos
              (F := GS) hσ (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos hWne).ne'
      have hfullGSpos : 0 <
          (ShadedBody.fullness GS.innerSet GS.innerBody : ENNReal) := by
        rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul] at hmassGS
        exact pos_of_mul_pos_left hmassGS (by positivity)
      have hretained0 : retainedOuter ≠ 0 := by
        dsimp only [retainedOuter]
        exact mul_ne_zero hLcoreRef0 hfullGSpos.ne'
      have hretainedTop : retainedOuter ≠ ⊤ := by
        dsimp only [retainedOuter]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
      let Cretain : ENNReal := 4 * retainedOuter⁻¹
      have hOuterCarrierRetained' : retainedOuter *
          (∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier) ≤
            4 * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier := by
        calc
          retainedOuter * (∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier) ≤
              2 ^ 2 * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier := by
            simpa only [retainedOuter] using hOuterCarrierRetained
          _ = 4 * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier := by norm_num
      have hOuterCarrierRestriction :
          ∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier ≤
            Cretain * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier := by
        calc
          ∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier =
              retainedOuter⁻¹ *
                (retainedOuter *
                  ∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hretained0 hretainedTop, one_mul]
          _ ≤ retainedOuter⁻¹ *
              (4 * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier) := by
            exact mul_le_mul_left' hOuterCarrierRetained' retainedOuter⁻¹
          _ = Cretain * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier := by
            dsimp only [Cretain]
            ring
      have hOuterFrostmanW := hOuterFrostman.of_le_of_subset
        (C' := Cretain) (t := W.outerSet) (by
          intro j hj
          exact hWGK j hj) hWsubS (by
            change ∑ j ∈ GS.outerSet, volume (GS.outerBody j).carrier ≤
              Cretain * ∑ j ∈ W.outerSet, volume (GS.outerBody j).carrier
            exact hOuterCarrierRestriction)
      have hOuterFrostmanK := hOuterFrostmanW.mapLinearIsometryEquiv f
      have hGSouterBody : GS.outerBody = G.outerBody := by
        rfl
      have hOuterFrostmanScaled :=
        (ConvexSpaceBody.IsFrostmanIn.homothety
          (s := W.outerSet) (W := K)
          (K := (ConvexSpaceBody.closedUnitBall :
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))) 0 hrsh).2 (by
            change IsFrostmanIn W.outerSet K
              (ConvexSpaceBody.closedUnitBall :
                ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) _
            simpa only [K, hGSouterBody,
              ConvexSpaceBody.closedUnitBall_mapLinearIsometryEquiv] using
                hOuterFrostmanK)
      let scaledBall : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        (ConvexSpaceBody.closedUnitBall :
          ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).homothety 0 rsh
      have hScaledKBall : ∀ j ∈ W.outerSet,
          (K j).homothety 0 rsh ≤ scaledBall := by
        intro j hj
        dsimp only [scaledBall]
        exact (ConvexSpaceBody.homothety_le_homothety_iff 0 hrsh).2 (hKball j hj)
      have hScaledKWindow : ∀ j ∈ W.outerSet,
          (K j).homothety 0 rsh ≤ plankWindow := by
        intro j hj
        exact (hScaledKleP j hj).trans (hPwindow j hj)
      have hscaledBall0 : volume scaledBall.carrier ≠ 0 := by
        dsimp only [scaledBall]
        rw [ConvexSpaceBody.volume_homothety]
        exact mul_ne_zero (by
          have hrpos : 0 < |rsh ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))| := by
            positivity
          exact (ENNReal.ofReal_pos.mpr hrpos).ne')
          ConvexSpaceBody.closedUnitBall_volume_pos.ne'
      have hplankWindow0 : volume plankWindow.carrier ≠ 0 :=
        (lt_of_lt_of_le zero_lt_one one_le_volume_plankWindow).ne'
      have hOuterFrostmanWindow := hOuterFrostmanScaled.change_ambient
        hScaledKBall hScaledKWindow hscaledBall0 hplankWindow0
      have hPscaledVol : ∀ j ∈ W.outerSet,
          volume (P j).carrier ≤
            (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
              volume ((K j).homothety 0 rsh).carrier := by
        intro j hj
        rw [hP j hj]
        change volume (comparablePlankEnvelope.plank Cw a b hab hb1 (K j)).carrier ≤
          (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
            volume ((K j).homothety 0 rsh).carrier
        simpa only [rsh] using (hKdim j hj).volume_plank_le_mul_scaledBody hCw
          (hσ.trans_le hσa) ((hσ.trans_le hσa).trans_le hab) hab hb1
      have hOuterFrostmanP := ShadedBody.IsFrostmanIn.of_envelope hOuterFrostmanWindow
        hScaledKWindow (fun j hj ↦ hPwindow j hj) hScaledKleP hPscaledVol
      have hPvolume : ∀ j,
          volume (P j).carrier = 8 * (a : ENNReal) * (b : ENNReal) := by
        intro j
        rw [show volume (P j).carrier =
            8 * (a : ENNReal) * (b : ENNReal) * (1 : ENNReal) by
          exact Prism3D.volume_carrier (P j).toPrism3D]
        simp
      have hOuterPmassQ :
          ∑ j ∈ W.outerSet, volume (P j).carrier ≤
            ((dO + 1 : ℕ) : ENNReal) * ∑ j ∈ qO, volume (P j).carrier := by
        simp_rw [hPvolume]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hcardE : (W.outerSet.card : ENNReal) ≤
            ((dO + 1 : ℕ) : ENNReal) * (qO.card : ENNReal) := by
          exact_mod_cast (by simpa only [dO] using hqOcard)
        calc
          (W.outerSet.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) ≤
              (((dO + 1 : ℕ) : ENNReal) * (qO.card : ENNReal)) *
                (8 * (a : ENNReal) * (b : ENNReal)) := by gcongr
          _ = ((dO + 1 : ℕ) : ENNReal) *
              ((qO.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by ring
      have hOuterFrostmanQ := hOuterFrostmanP.of_le_of_subset
        (C' := ((dO + 1 : ℕ) : ENNReal)) (t := qO)
        (fun j hj ↦ hPwindow j hj) hqOsub hOuterPmassQ
      have hWouterCarrier0 :
          (∑ j ∈ W.outerSet, volume (W.outerBody j).carrier) ≠ 0 := by
        let j := hWne.choose
        have hj : j ∈ W.outerSet := hWne.choose_spec
        have hKlower := (hKdim j hj).volume_lower (by simp)
        have hKvol0 : volume (K j).carrier ≠ 0 := by
          have hlow0 : ((Cw : ENNReal) ^ 3)⁻¹ *
              (Metric.lt_volume_convexHull.c 3 : ENNReal) *
                ((a : ENNReal) * (b : ENNReal)) ≠ 0 := by
            exact mul_ne_zero
              (mul_ne_zero
                (ENNReal.inv_ne_zero.mpr (by finiteness))
                (ENNReal.coe_ne_zero.mpr
                  (Metric.lt_volume_convexHull.c_pos 3).ne'))
              (mul_ne_zero
                (ENNReal.coe_ne_zero.mpr (hσ.trans_le hσa).ne')
                (ENNReal.coe_ne_zero.mpr
                  ((hσ.trans_le hσa).trans_le hab).ne'))
          exact ((pos_iff_ne_zero.mpr hlow0).trans_le hKlower).ne'
        have hYvol0 : volume (Y j).carrier ≠ 0 := by
          rw [hYcarrier j hj]
          exact ((pos_iff_ne_zero.mpr hKvol0).trans_le
            (measure_mono (ConvexSpaceBody.self_le_cthickening (K j) _))).ne'
        have hWvol0 : volume (W.outerBody j).carrier ≠ 0 := by
          have hvolmap := ConvexSpaceBody.volume_mapLinearIsometryEquiv
            (W.outerBody j).toConvexSpaceBody f
          change volume (Y j).carrier = volume (W.outerBody j).carrier at hvolmap
          exact hvolmap ▸ hYvol0
        exact (pos_iff_ne_zero.mpr hWvol0 |>.trans_le
          (Finset.single_le_sum_of_canonicallyOrdered
            (f := fun k ↦ volume (W.outerBody k).carrier) hj)).ne'
      let coreFullCoeff : ENNReal :=
        (ShadedBody.factoringCoreAtScaleUniformFullnessConstant
          (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) * (2 : ENNReal)⁻¹
      have hCoreOuterFullness : coreFullCoeff *
          (ShadedBody.fullness GS.innerSet GS.innerBody : ENNReal) ^ 2 ≤
            (ShadedBody.fullness W.outerSet W.outerBody : ENNReal) := by
        rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
        apply (ENNReal.le_div_iff_mul_le (Or.inl hWouterCarrier0)
          (Or.inl (ENNReal.sum_ne_top.mpr fun j _ ↦
            (W.outerBody j).isCompact.measure_ne_top))).2
        have hthick := Q.core.thick_fullness
        rw [ShadedBody.coe_fullness] at hthick
        simpa only [coreFullCoeff, mul_assoc] using hthick
      let cDenO : NNReal :=
        (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent)⁻¹
      let cScaleO : NNReal :=
        (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar))⁻¹
      have hRrefO : ShadedBody.IsCRefinement G.innerSet G.innerBody
          F.innerSet F.innerBody cDenO := by
        simpa only [cDenO, G] using R.selection_refinement F hσ hdisc D hmass
      have hQrefO : ShadedBody.IsCRefinement GS.innerSet GS.innerBody
          G.innerSet G.innerBody cScaleO := by
        simpa only [cScaleO, GS] using
          Q.selection_refinement G hσ hdiscG DG hσB hupperG hmassG
      have hfullOriginalO : (σ : ENNReal) ^ η ≤
          (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) := by
        simpa only [F, flatPrismFactorFamily_innerSet,
          flatPrismFactorFamily_innerBody] using hfamily.fullness
      have hfullGSfunded : (cScaleO : ENNReal) * (cDenO : ENNReal) *
          (σ : ENNReal) ^ η ≤
            (ShadedBody.fullness GS.innerSet GS.innerBody : ENNReal) := by
        calc
          (cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η ≤
              (cScaleO : ENNReal) * (cDenO : ENNReal) *
                (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) := by gcongr
          _ ≤ (cScaleO : ENNReal) *
              (ShadedBody.fullness G.innerSet G.innerBody : ENNReal) := by
            rw [mul_assoc]
            gcongr
            exact hRrefO.coe_mul_fullness_le
          _ ≤ (ShadedBody.fullness GS.innerSet GS.innerBody : ENNReal) :=
            hQrefO.coe_mul_fullness_le
      let outerFullCoeff : ENNReal :=
        (((dO + 1 : ℕ) : ENNReal)⁻¹ *
          (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹) * coreFullCoeff
      have hOuterFullnessFunded : outerFullCoeff *
          ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ^ 2 ≤
            (ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) : ENNReal) := by
        have hreshapeE : (ShadedBody.fullness W.outerSet W.outerBody : ENNReal) ≤
            (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
              (ShadedBody.fullness W.outerSet
                (fun j ↦ (P j).toShadedBody) : ENNReal) := by
          exact_mod_cast hfullReshape
        have hrefFull := hrefO.coe_mul_fullness_le
        have henv0 : (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) ≠ 0 :=
          (zero_lt_one.trans_le (by exact_mod_cast
            flatPrismEnvelopeVolumeRatio.one_le Cw)).ne'
        have henvTop : (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) ≠ ⊤ := by finiteness
        have hdNN0 : (((dO + 1 : ℕ) : NNReal)) ≠ 0 := by positivity
        have hdCoe : ((((dO + 1 : ℕ) : NNReal) : ENNReal)) =
            ((dO + 1 : ℕ) : ENNReal) := by norm_cast
        have hdInvCoe : (((((dO + 1 : ℕ) : NNReal)⁻¹ : NNReal) : ENNReal)) =
            ((dO + 1 : ℕ) : ENNReal)⁻¹ := by
          rw [ENNReal.coe_inv hdNN0, hdCoe]
        have hrefFull' : ((dO + 1 : ℕ) : ENNReal)⁻¹ *
            (ShadedBody.fullness W.outerSet
              (fun j ↦ (P j).toShadedBody) : ENNReal) ≤
              (ShadedBody.fullness qO
                (fun j ↦ (P j).toShadedBody) : ENNReal) := by
          rw [← hdInvCoe]
          simpa only [dO] using hrefFull
        have hcoreFunded : coreFullCoeff *
            ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ^ 2 ≤
              (ShadedBody.fullness W.outerSet W.outerBody : ENNReal) := by
          calc
            coreFullCoeff *
                ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ^ 2 ≤
                coreFullCoeff *
                  (ShadedBody.fullness GS.innerSet GS.innerBody : ENNReal) ^ 2 := by
              gcongr
            _ ≤ (ShadedBody.fullness W.outerSet W.outerBody : ENNReal) :=
              hCoreOuterFullness
        calc
          outerFullCoeff *
              ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ^ 2 ≤
              (((dO + 1 : ℕ) : ENNReal)⁻¹ *
                (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹) *
                  (ShadedBody.fullness W.outerSet W.outerBody : ENNReal) := by
            dsimp only [outerFullCoeff]
            calc
              ((dO + 1 : ℕ) : ENNReal)⁻¹ *
                    (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹ * coreFullCoeff *
                      ((cScaleO : ENNReal) * (cDenO : ENNReal) *
                        (σ : ENNReal) ^ η) ^ 2 =
                  (((dO + 1 : ℕ) : ENNReal)⁻¹ *
                    (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹) *
                      (coreFullCoeff *
                        ((cScaleO : ENNReal) * (cDenO : ENNReal) *
                          (σ : ENNReal) ^ η) ^ 2) := by ring
              _ ≤ (((dO + 1 : ℕ) : ENNReal)⁻¹ *
                    (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹) *
                      (ShadedBody.fullness W.outerSet W.outerBody : ENNReal) :=
                mul_le_mul_left' hcoreFunded _
          _ ≤ (((dO + 1 : ℕ) : ENNReal)⁻¹ *
              (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹) *
                ((flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
                  (ShadedBody.fullness W.outerSet
                    (fun j ↦ (P j).toShadedBody) : ENNReal)) := by gcongr
          _ = ((dO + 1 : ℕ) : ENNReal)⁻¹ *
              (ShadedBody.fullness W.outerSet
                (fun j ↦ (P j).toShadedBody) : ENNReal) := by
            calc
              ((dO + 1 : ℕ) : ENNReal)⁻¹ *
                    (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹ *
                      ((flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
                        (ShadedBody.fullness W.outerSet
                          (fun j ↦ (P j).toShadedBody) : ENNReal)) =
                  ((dO + 1 : ℕ) : ENNReal)⁻¹ *
                    ((flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)⁻¹ *
                      (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal)) *
                        (ShadedBody.fullness W.outerSet
                          (fun j ↦ (P j).toShadedBody) : ENNReal) := by ring
              _ = ((dO + 1 : ℕ) : ENNReal)⁻¹ *
                    (ShadedBody.fullness W.outerSet
                      (fun j ↦ (P j).toShadedBody) : ENNReal) := by
                rw [ENNReal.inv_mul_cancel henv0 henvTop, mul_one]
          _ ≤ (ShadedBody.fullness qO
              (fun j ↦ (P j).toShadedBody) : ENNReal) := by
            exact hrefFull'
      have hProductG := Q.multiplicity_product_original G hσ hdiscG DG hσB
        hupperG hmassG x₀ hx₀
      have hProductOriginal :
          ShadedBody.multiplicity F.innerSet F.innerBody ≤
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
              (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.factoringCoreAtScaleUniformProductConstant
                  (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                  ShadedBody.multiplicity W.outerSet W.outerBody *
                    ShadedBody.multiplicity (W.fiber x₀) W.innerBody := by
        calc
          ShadedBody.multiplicity F.innerSet F.innerBody ≤
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                ShadedBody.multiplicity G.innerSet G.innerBody :=
            R.multiplicity_le_selected F hσ hdisc D hmass
          _ ≤ (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
              ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.factoringCoreAtScaleUniformProductConstant
                  (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                  ShadedBody.multiplicity W.outerSet W.outerBody *
                    ShadedBody.multiplicity (W.fiber x₀) W.innerBody) := by
            gcongr
          _ = _ := by ring
      have hBactual : max 1 (2 * Dpar) = 2 * Dpar := by
        apply max_eq_right
        calc
          (1 : NNReal) ≤ 2 := by norm_num
          _ ≤ 2 * Dpar := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hparent.one_le (by positivity)
      have hScaleLossGlobal :
          (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) ≤
            (σ : ENNReal) ^ (-eFund) := by
        simpa only [hBactual] using hScaleLossMax
      have hCardGlobal : (s.card : ℝ) ≤ (σ : ℝ) ^ (-(7 : ℝ)) :=
        hCardLoss s (fun i ↦ (V i).toTube) hfamily.ball hfamily.essDistinct
      have hFcardGlobal : 0 < F.innerSet.card := by
        simpa only [F, flatPrismFactorFamily_innerSet] using hfamily.nonempty.card_pos
      have hFcardBoundGlobal : (F.innerSet.card : ℝ) ≤
          (σ : ℝ) ^ (-(7 : ℝ)) := by
        simpa only [F, flatPrismFactorFamily_innerSet] using hCardGlobal
      have hDexpGlobal : ((D.exponent + 1 : ℕ) : ENNReal) ≤
          (σ : ENNReal) ^ (-(eFund / 4)) := by
        rw [show D.exponent = flatPrismVolumeRatioExponent Dpar σ by
          exact flatPrismFactorFamily_volumeRatio_dilate_controlled_exponent V p
            hparent.mapsTo Fz' hfamily.nonempty hdim hσ
            (hσhalfNN.trans (by norm_num)) hρ1 hfamily.ball Vρ
            hparent.le_parent_dilate]
        exact hVolumeExponent
      have hDensityLossGlobal :
          (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) ≤
            (σ : ENNReal) ^ (-eFund) :=
        hDensityLoss F.innerSet.card D.exponent hFcardGlobal hFcardBoundGlobal hDexpGlobal
      have hGSneGlobal : GS.innerSet.Nonempty := by
        obtain ⟨i, hi⟩ := hWfiber_ne
        have hiW := (ShadedBody.mem_shadedFactorFamily_fiber_iff W x₀ i).mp hi |>.1
        rw [hWinnerSet] at hiW
        exact ⟨i, (Finset.mem_filter.mp hiW).1⟩
      have hGScardBoundGlobal : (GS.innerSet.card : ℝ) ≤
          (σ : ℝ) ^ (-(7 : ℝ)) := by
        calc
          (GS.innerSet.card : ℝ) ≤ (s.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hGSinner_sub_s
          _ ≤ _ := hCardGlobal
      have hw₁Global : w₁ ≤ 1 := by
        let jsel := S.selected_nonempty.choose
        have hjsel : jsel ∈ S.selected := S.selected_nonempty.choose_spec
        have hjselG : jsel ∈ G.innerSet.image G.parent := S.selected_subset hjsel
        have hbody : G.outerBody jsel ≤
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := hWGK jsel hjsel
        have hscale : (G.outerBody jsel).scale ≤ (1 : ℝ) :=
          Metric.thickness_le_of_subset_closedBall hbody (by norm_num)
            (Module.finrank ℝ E - 1)
        have hscale0 : 0 ≤ (G.outerBody jsel).scale :=
          Metric.thickness_nonneg (G.outerBody jsel).carrier _
        rw [← NNReal.coe_le_coe]
        change (Real.toNNReal (G.outerBody jsel).scale : ℝ) ≤ (1 : NNReal)
        rw [Real.coe_toNNReal _ hscale0]
        exact_mod_cast hscale
      have hPipelineLossGlobal :
          (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) ≤ (σ : ENNReal) ^ (-eFund) := by
        apply hPipelineLoss GS.innerSet.card DGS.exponent hGSneGlobal.card_pos
          hGScardBoundGlobal
        · simpa only [show DGS.exponent = D.exponent from rfl] using hDexpGlobal
        · exact ShadedBody.le_selectedOuterScale G hσ hdiscG hσB hupperG hmassG
        · exact hw₁Global
      have hDenNN0Global :
          ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent ≠ 0 := by
        intro hz
        have hle := R.mass_refinement
        rw [hz, ENNReal.coe_zero, zero_mul] at hle
        exact (not_le_of_gt hmass) hle
      have hScaleNN0Global :
          ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) ≠ 0 := by
        intro hz
        have hle := Q.selection_mass
        rw [hz, ENNReal.coe_zero, zero_mul] at hle
        exact (not_le_of_gt hmassG) hle
      have hPipeNN0Global :
          ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
            DGS.exponent w₁ ≠ 0 := by
        have hdiscGSGlobal : GS.InnerIsDiscretizedAtScale σ := by
          simpa only [GS, ShadedBody.selectedOuterScaleFamily] using
            hdiscG.restrictOuter S.selected
        have hLposGlobal : 0 < Lcore.refinementConstant := by
          simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform] using
            ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos
              hσ hdiscGSGlobal DGS w₁ Q.scale_pos hWne
        have hLrefGlobal : Lcore.refinementConstant =
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁)⁻¹ := by
          simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform, hdim] using
            ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv
              3 GS.innerSet.card DGS.exponent w₁
        have hinvpos : 0 <
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁)⁻¹ := by
          simpa only [← hLrefGlobal] using hLposGlobal
        exact (inv_pos.mp hinvpos).ne'
      let bSmall : NNReal := min b₀64 Cwi⁻¹
      have hbSmall0 : 0 < bSmall := lt_min hb₀64 (inv_pos.mpr hCwipos)
      by_cases hbSmallCase : b ≤ bSmall
      · have hbCwi : Cwi * b ≤ 1 := by
          rw [mul_comm]
          exact (NNReal.le_inv_iff_mul_le hCwipos.ne').mp
            (hbSmallCase.trans (min_le_right _ _))
        have hAinEq : Ain = Cwi * a := rfl
        have hBinEq : Bin = Cwi * b := by
          dsimp only [Bin, comparablePlankEnvelope.bodyWide]
          rw [min_eq_left hbCwi]
        have haIEq : aI = σ / (Cwi * b) := by rw [haI, hBinEq]
        have hbIEq : bI = σ / (Cwi * a) := by rw [hbI, hAinEq]
        have hratioOrig : (aI : ENNReal) / (bI : ENNReal) =
            (a : ENNReal) / (b : ENNReal) := by
          calc
            (aI : ENNReal) / (bI : ENNReal) =
                (Ain : ENNReal) / (Bin : ENNReal) := hratioIE
            _ = (a : ENNReal) / (b : ENNReal) := by
              rw [hAinEq, hBinEq]
              push_cast
              exact ENNReal.mul_div_mul_left _ _
                (ENNReal.coe_ne_zero.mpr hCwipos.ne') ENNReal.coe_ne_top
        have hMIEq : MI = Cinner * (b / a) ^ 2 := by
          dsimp only [MI]
          rw [hBinEq, hAinEq]
          rw [mul_div_mul_left b a hCwipos.ne']
        have ha0nn : a ≠ 0 := (hσ.trans_le hσa).ne'
        have hb0nn : b ≠ 0 := ((hσ.trans_le hσa).trans_le hab).ne'
        have hbI0nn : bI ≠ 0 := by
          rw [hbIEq]
          positivity
        have hratioNN : aI / bI = a / b := by
          apply ENNReal.coe_injective
          rw [ENNReal.coe_div hbI0nn, ENNReal.coe_div hb0nn]
          exact hratioOrig
        have hratio0 : a / b ≠ 0 := div_ne_zero ha0nn hb0nn
        have hratioInv : b / a = (a / b)⁻¹ := by
          rw [inv_div]
        have hshapeRatioNN : MI ^ (β / 2) * (aI / bI) =
            Cinner ^ (β / 2) * (a / b) ^ (1 - β) := by
          rw [hMIEq, NNReal.mul_rpow, hratioNN, hratioInv]
          have hcollect : (((a / b)⁻¹) ^ 2) ^ (β / 2) * (a / b) =
              (a / b) ^ (1 - β) := by
            rw [← NNReal.rpow_natCast ((a / b)⁻¹) 2]
            rw [← NNReal.rpow_mul]
            norm_num only [Nat.cast_ofNat]
            have hinvpow : ((a / b)⁻¹) ^ β = (a / b) ^ (-β) := by
              calc
                ((a / b)⁻¹) ^ β = ((a / b) ^ (-1 : ℝ)) ^ β := by
                  rw [NNReal.rpow_neg, NNReal.rpow_one]
                _ = (a / b) ^ ((-1 : ℝ) * β) := by
                  rw [NNReal.rpow_mul]
                _ = (a / b) ^ (-β) := by congr 1; ring
            rw [show (2 : ℝ) * (β / 2) = β by ring, hinvpow]
            calc
              (a / b) ^ (-β) * (a / b) =
                  (a / b) ^ (-β) * (a / b) ^ (1 : ℝ) := by
                    rw [NNReal.rpow_one]
              _ = (a / b) ^ (-β + 1) :=
                (NNReal.rpow_add hratio0 (-β) 1).symm
              _ = (a / b) ^ (1 - β) := by congr 1; ring
          rw [mul_assoc, hcollect]
        have hshapeRatio : (MI : ENNReal) ^ (β / 2) *
              ((aI : ENNReal) / (bI : ENNReal)) =
            (Cinner : ENNReal) ^ (β / 2) *
              ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) := by
          have hc := congrArg (fun x : NNReal ↦ (x : ENNReal)) hshapeRatioNN
          simpa only [ENNReal.coe_mul, ENNReal.coe_div hbI0nn, ENNReal.coe_div hb0nn,
            ENNReal.coe_rpow_of_nonneg _ (by positivity : 0 ≤ β / 2),
            ENNReal.coe_rpow_of_nonneg _ (by linarith : 0 ≤ 1 - β)] using hc
        have hbIform : bI = Cwi⁻¹ * (a⁻¹ * σ) := by
          rw [hbIEq]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        have hshapeScaleNN : bI ^ (-2 * β) =
            Cwi ^ (2 * β) * (a⁻¹ * σ) ^ (-2 * β) := by
          rw [hbIform, NNReal.mul_rpow]
          congr 1
          calc
            (Cwi⁻¹) ^ (-2 * β) = (Cwi ^ (-1 : ℝ)) ^ (-2 * β) := by
              rw [NNReal.rpow_neg, NNReal.rpow_one]
            _ = Cwi ^ ((-1 : ℝ) * (-2 * β)) := by rw [← NNReal.rpow_mul]
            _ = Cwi ^ (2 * β) := by congr 1; ring
        have hshapeScale : (bI : ENNReal) ^ (-2 * β) =
            (Cwi : ENNReal) ^ (2 * β) *
              ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) := by
          have hbase0 : a⁻¹ * σ ≠ 0 := mul_ne_zero (inv_ne_zero ha0nn) hσ.ne'
          have hc := congrArg (fun x : NNReal ↦ (x : ENNReal)) hshapeScaleNN
          simpa only [ENNReal.coe_mul, ENNReal.coe_inv ha0nn,
            ENNReal.coe_rpow_of_ne_zero hbI0nn,
            ENNReal.coe_rpow_of_ne_zero hCwipos.ne',
            ENNReal.coe_rpow_of_ne_zero hbase0] using hc
        let CcardI : ENNReal := 2 * (flatPrismBodyVolumeRatio.C Cw : ENNReal)
        have hWcardE0 : (W.outerSet.card : ENNReal) ≠ 0 := by
          exact_mod_cast hWne.card_ne_zero
        have hWcardETop : (W.outerSet.card : ENNReal) ≠ ⊤ := by finiteness
        have hHfibEq : H.fiber x₀ = W.fiber x₀ := by
          dsimp only [H]
          rw [ShadedBody.FactorFamily.restrictOuter_fiber_of_mem GS W.outerSet hx₀,
            hWfibEq]
        have hqIprod : (qI.card : ENNReal) * (W.outerSet.card : ENNReal) ≤
            CcardI * (s.card : ENNReal) := by
          calc
            (qI.card : ENNReal) * (W.outerSet.card : ENNReal) ≤
                ((W.fiber x₀).card : ENNReal) * (W.outerSet.card : ENNReal) := by
              gcongr
            _ ≤ CcardI * (s.card : ENNReal) := by
              simpa only [CcardI, hHfibEq] using hHcard x₀ hx₀
        have hqIDiv : (qI.card : ENNReal) ≤
            CcardI * ((s.card : ENNReal) / (W.outerSet.card : ENNReal)) := by
          calc
            (qI.card : ENNReal) ≤
                (CcardI * (s.card : ENNReal)) / (W.outerSet.card : ENNReal) :=
              (ENNReal.le_div_iff_mul_le (Or.inl hWcardE0) (Or.inl hWcardETop)).2 hqIprod
            _ = CcardI * ((s.card : ENNReal) / (W.outerSet.card : ENNReal)) := by
              rw [mul_div_assoc]
        have hbIle : (bI : ENNReal) ≤ (a : ENNReal)⁻¹ * (σ : ENNReal) := by
          rw [hbIform]
          simp only [ENNReal.coe_mul, ENNReal.coe_inv hCwipos.ne',
            ENNReal.coe_inv ha0nn]
          calc
            _ ≤
                1 * ((a : ENNReal)⁻¹ * (σ : ENNReal)) := by
              gcongr
              exact ENNReal.inv_le_one.mpr (by exact_mod_cast hCwi)
            _ = _ := one_mul _
        have hcardBase : (bI : ENNReal) ^ 2 * (qI.card : ENNReal) ≤
            CcardI * (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
              ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) := by
          calc
            (bI : ENNReal) ^ 2 * (qI.card : ENNReal) ≤
                ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ 2 *
                  (CcardI * ((s.card : ENNReal) /
                    (W.outerSet.card : ENNReal))) := by gcongr
            _ = CcardI * (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) := by
              rw [mul_pow, ENNReal.inv_pow]
              ring
        have hpOuter : 0 ≤ 1 - β / 2 := by linarith
        have hshapeCard : ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
              (1 - β / 2) ≤
            CcardI ^ (1 - β / 2) *
              (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^
                  (1 - β / 2) := by
          calc
            ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^ (1 - β / 2) ≤
                (CcardI * (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                  ((s.card : ENNReal) / (W.outerSet.card : ENNReal)))) ^
                    (1 - β / 2) := ENNReal.rpow_le_rpow hcardBase hpOuter
            _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hpOuter
        let innerFixed : ENNReal := (dED + 1 : ENNReal) * CFI ^ (1 - β / 2) *
          (Cinner : ENNReal) ^ (β / 2) * (Cwi : ENNReal) ^ (2 * β) *
            CcardI ^ (1 - β / 2)
        let innerTarget : ENNReal := (σ : ENNReal) ^ (-(ε' / 12)) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
          (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
            ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^ (1 - β / 2)
        have hinnerCanonical :
            ShadedBody.multiplicity (W.fiber x₀)
                (fun i ↦ (Tin i).toShadedBody) ≤ innerFixed * innerTarget := by
          calc
            ShadedBody.multiplicity (W.fiber x₀)
                (fun i ↦ (Tin i).toShadedBody) ≤
                (dED + 1 : ENNReal) *
                  ShadedBody.multiplicity qI (fun i ↦ (PI i).toShadedBody) := hmultI
            _ ≤ (dED + 1 : ENNReal) *
                ((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2) *
                  (MI : ENNReal) ^ (β / 2) *
                  ((aI : ENNReal) / (bI : ENNReal)) *
                  (bI : ENNReal) ^ (-2 * β) *
                  ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                    (1 - β / 2)) := by gcongr
            _ ≤ innerFixed * innerTarget := by
              calc
                (dED + 1 : ENNReal) *
                    ((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2) *
                      (MI : ENNReal) ^ (β / 2) *
                      ((aI : ENNReal) / (bI : ENNReal)) *
                      (bI : ENNReal) ^ (-2 * β) *
                      ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                        (1 - β / 2)) =
                    (dED + 1 : ENNReal) *
                      (((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2)) *
                        ((MI : ENNReal) ^ (β / 2) *
                          ((aI : ENNReal) / (bI : ENNReal))) *
                        (bI : ENNReal) ^ (-2 * β) *
                        ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                          (1 - β / 2)) := by ring
                _ ≤ innerFixed * innerTarget := by
                  rw [hshapeRatio, hshapeScale]
                  let common : ENNReal := (dED + 1 : ENNReal) *
                    (σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2) *
                    (Cinner : ENNReal) ^ (β / 2) *
                    ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                    (Cwi : ENNReal) ^ (2 * β) *
                    ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β)
                  rw [show
                    (dED + 1 : ENNReal) *
                        ((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2) *
                          ((Cinner : ENNReal) ^ (β / 2) *
                            ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)) *
                          ((Cwi : ENNReal) ^ (2 * β) *
                            ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β)) *
                          ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                            (1 - β / 2)) =
                      common * (((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                        (1 - β / 2)) by dsimp only [common]; ring]
                  rw [show innerFixed * innerTarget = common *
                      (CcardI ^ (1 - β / 2) *
                        (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                          ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^
                            (1 - β / 2)) by
                    dsimp only [common, innerFixed, innerTarget]
                    ring]
                  exact mul_le_mul_left' hshapeCard common
        have hTinMultiplicity :
            ShadedBody.multiplicity (W.fiber x₀)
                (fun i ↦ (Tin i).toShadedBody) =
              ShadedBody.multiplicity (W.fiber x₀) W.innerBody := by
          have hbody : (fun i ↦ (Tin i).toShadedBody) =
              (fun i ↦ (W.innerBody i).mapLinearIsometryEquiv f) := by
            funext i
            apply ShadedBody.ext_of_toConvexSpaceBody_eq
            · exact hTinConvex i
            · rfl
          rw [hbody]
          exact ShadedBody.multiplicity_mapLinearIsometryEquiv
            (W.fiber x₀) W.innerBody f
        have hinnerCanonicalW :
            ShadedBody.multiplicity (W.fiber x₀) W.innerBody ≤
              innerFixed * innerTarget := by
          rw [← hTinMultiplicity]
          exact hinnerCanonical
        let splitExact : ENNReal :=
          (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
              (ShadedBody.factoringCoreAtScaleUniformProductConstant
                (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                (dO + 1 : ENNReal) * innerFixed
        have hsplitExact : ShadedBody.multiplicity F.innerSet F.innerBody ≤
            splitExact *
              ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) * innerTarget := by
          calc
            ShadedBody.multiplicity F.innerSet F.innerBody ≤
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                    (ShadedBody.factoringCoreAtScaleUniformProductConstant
                      (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                      ShadedBody.multiplicity W.outerSet W.outerBody *
                        ShadedBody.multiplicity (W.fiber x₀) W.innerBody := hProductOriginal
            _ = (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                    (ShadedBody.factoringCoreAtScaleUniformProductConstant
                      (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                      ShadedBody.multiplicity W.outerSet
                        (fun j ↦ (P j).toShadedBody) *
                        ShadedBody.multiplicity (W.fiber x₀) W.innerBody := by rw [hmultP]
            _ ≤ (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                    (ShadedBody.factoringCoreAtScaleUniformProductConstant
                      (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                      ((dO + 1 : ENNReal) *
                        ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody)) *
                        (innerFixed * innerTarget) := by
                  gcongr
                  simpa using hmultqO
            _ = splitExact *
                ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) * innerTarget := by
              dsimp only [splitExact]
              ring
        have hdOeq : dO = dO₀ := by
          dsimp only [dO, dO₀, Cextract, Cextract₀, A]
        have hinnerFixedEq : innerFixed = innerFixed₀ := by
          dsimp only [innerFixed, innerFixed₀, CFI, CFI₀, CcardI]
        have hsplitExactFormula : splitExact = splitFixed₀ *
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) := by
          dsimp only [splitExact]
          rw [ShadedBody.factoringCoreAtScaleUniformProductConstant_eq, hdim,
            hdOeq, hinnerFixedEq]
          dsimp only [splitFixed₀]
          push_cast
          ring
        have hsplitExactBound : splitExact ≤
            (σ : ENNReal) ^ (-(4 * eFund)) := by
          rw [hsplitExactFormula]
          have hsplitFixedEnvelope : splitFixed₀ ≤ partAFixedEnvelope := by
            exact ((le_max_left splitFixed₀
              (max fixedFrost₀ (max fixedFull₀ (max (Couter₀ : ENNReal)
                (max (CparentTotal₀ : ENNReal)
                  (max (Cdiv₀ : ENNReal) (Cm : ENNReal)⁻¹)))))).trans
              (le_max_right 1 _)).trans hpartAFixedBase_le
          have hsplitFixedLoss : splitFixed₀ ≤ (σ : ENNReal) ^ (-eFund) := by
            calc
              splitFixed₀ ≤ partAFixedEnvelope := hsplitFixedEnvelope
              _ ≤ (σ : ENNReal) ^ (-eFund) := hPartAFixed.2.2
          calc
            splitFixed₀ *
                  (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                  (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal) ≤
                (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-eFund) *
                  (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-eFund) := by
              exact mul_le_mul
                (mul_le_mul
                  (mul_le_mul hsplitFixedLoss
                    hDensityLossGlobal bot_le bot_le)
                  hScaleLossGlobal bot_le bot_le)
                hPipelineLossGlobal bot_le bot_le
            _ = (σ : ENNReal) ^ (-(4 * eFund)) := by
              repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              congr 1
              ring
        have hinvLoss : ∀ C : NNReal, C ≠ 0 →
            (C : ENNReal) ≤ (σ : ENNReal) ^ (-eFund) →
              (σ : ENNReal) ^ eFund ≤ (C : ENNReal)⁻¹ := by
          intro C hC0 hCle
          apply ENNReal.le_inv_iff_mul_le.mpr
          calc
            (σ : ENNReal) ^ eFund * (C : ENNReal) ≤
                (σ : ENNReal) ^ eFund * (σ : ENNReal) ^ (-eFund) := by gcongr
            _ = 1 := by
              rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              simp
        have hDenInvLoss : (σ : ENNReal) ^ eFund ≤
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
              ENNReal)⁻¹ := hinvLoss _ hDenNN0Global hDensityLossGlobal
        have hScaleInvLoss : (σ : ENNReal) ^ eFund ≤
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal)⁻¹ :=
          hinvLoss _ hScaleNN0Global hScaleLossGlobal
        let fullCoreC : NNReal :=
          ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3 GS.innerSet.card
            DGS.exponent w₁
        have hfullCoreC0 : fullCoreC ≠ 0 := by
          dsimp only [fullCoreC,
            ShadedBody.factoringCoreAtScaleUniformFullnessConstant]
          rw [ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv]
          exact mul_ne_zero (inv_ne_zero (by
              exact mul_ne_zero
                (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
                  ShadedBody.lambdaInducedSingleWUniform.C_pos.ne')
                (by positivity)))
            (pow_ne_zero _ (inv_ne_zero hPipeNN0Global))
        let outerFullCoeffNN : NNReal := ((dO + 1 : ℕ) : NNReal)⁻¹ *
          (flatPrismEnvelopeVolumeRatio.C Cw)⁻¹ * (fullCoreC * 2⁻¹)
        have houterFullCoeffNN0 : outerFullCoeffNN ≠ 0 := by
          dsimp only [outerFullCoeffNN]
          exact mul_ne_zero
            (mul_ne_zero (inv_ne_zero (by positivity))
              (inv_ne_zero (zero_lt_one.trans_le
                (flatPrismEnvelopeVolumeRatio.one_le Cw)).ne'))
            (mul_ne_zero hfullCoreC0 (inv_ne_zero (by norm_num)))
        have houterFullCoeffCoe : (outerFullCoeffNN : ENNReal) = outerFullCoeff := by
          dsimp only [outerFullCoeffNN, outerFullCoeff, coreFullCoeff, fullCoreC]
          simp only [ENNReal.coe_mul,
            ENNReal.coe_inv (by positivity : (((dO + 1 : ℕ) : NNReal)) ≠ 0),
            ENNReal.coe_inv (by
              exact (zero_lt_one.trans_le
                (flatPrismEnvelopeVolumeRatio.one_le Cw)).ne'),
            ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0)]
          rw [hdim]
          push_cast
          ring
        have houterFullInvFormula : (outerFullCoeffNN : ENNReal)⁻¹ =
            fixedFull₀ * (DGS.exponent + 1 : ℕ) *
              (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                DGS.exponent w₁ : ENNReal) ^ 2 := by
          rw [← ENNReal.coe_inv houterFullCoeffNN0]
          norm_cast
          dsimp only [outerFullCoeffNN, fullCoreC]
          repeat' rw [mul_inv_rev]
          rw [inv_inv (((dO + 1 : ℕ) : NNReal)),
            inv_inv (flatPrismEnvelopeVolumeRatio.C Cw), inv_inv (2 : NNReal),
            ShadedBody.inv_factoringCoreAtScaleUniformFullnessConstant_eq]
          rw [hdOeq]
          dsimp only [fixedFull₀]
          push_cast
          ring
        have hfixedFull_le : fixedFull₀ ≤ partAFixedEnvelope :=
          ((le_max_left _ _).trans <| (le_max_right _ _).trans <|
            (le_max_right _ _).trans <| (le_max_right _ _)).trans hpartAFixedBase_le
        have houterFullInvBound : outerFullCoeff⁻¹ ≤
            (σ : ENNReal) ^ (-(4 * eFund)) := by
          rw [← houterFullCoeffCoe, houterFullInvFormula]
          calc
            fixedFull₀ * (DGS.exponent + 1 : ℕ) *
                  (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal) ^ 2 ≤
                (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-(eFund / 4)) *
                  ((σ : ENNReal) ^ (-eFund)) ^ 2 := by
              gcongr
              · exact hfixedFull_le.trans hPartAFixed.2.2
              · simpa only [show DGS.exponent = D.exponent from rfl] using hDexpGlobal
            _ ≤ (σ : ENNReal) ^ (-(4 * eFund)) := by
              rw [← ENNReal.rpow_natCast]
              repeat' rw [← ENNReal.rpow_mul]
              repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              apply ENNReal.rpow_le_rpow_of_exponent_ge (by
                exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1))
              linarith [heFund]
        have houterFullCoeff0 : outerFullCoeff ≠ 0 := by
          rw [← houterFullCoeffCoe]
          exact ENNReal.coe_ne_zero.mpr houterFullCoeffNN0
        have houterFullCoeffTop : outerFullCoeff ≠ ⊤ := by
          rw [← houterFullCoeffCoe]
          exact ENNReal.coe_ne_top
        have houterCoeffLower : (σ : ENNReal) ^ (4 * eFund) ≤ outerFullCoeff := by
          have hle : (σ : ENNReal) ^ (4 * eFund) ≤ outerFullCoeff⁻¹⁻¹ := by
            apply ENNReal.le_inv_iff_mul_le.mpr
            calc
              (σ : ENNReal) ^ (4 * eFund) * outerFullCoeff⁻¹ ≤
                  (σ : ENNReal) ^ (4 * eFund) *
                    (σ : ENNReal) ^ (-(4 * eFund)) := by gcongr
              _ = 1 := by
                rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
                simp
          simpa only [inv_inv] using hle
        have hcScaleLower : (σ : ENNReal) ^ eFund ≤ (cScaleO : ENNReal) := by
          dsimp only [cScaleO]
          rw [ENNReal.coe_inv hScaleNN0Global]
          exact hScaleInvLoss
        have hcDenLower : (σ : ENNReal) ^ eFund ≤ (cDenO : ENNReal) := by
          dsimp only [cDenO]
          rw [ENNReal.coe_inv hDenNN0Global]
          exact hDenInvLoss
        have hOuterFundPower : (σ : ENNReal) ^ (2 * η + 8 * eFund) ≤
            outerFullCoeff *
              ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ^ 2 := by
          calc
            (σ : ENNReal) ^ (2 * η + 8 * eFund) =
                (σ : ENNReal) ^ (4 * eFund) *
                  (((σ : ENNReal) ^ eFund * (σ : ENNReal) ^ eFund *
                    (σ : ENNReal) ^ η) ^ 2) := by
              have hi : (σ : ENNReal) ^ eFund * (σ : ENNReal) ^ eFund *
                    (σ : ENNReal) ^ η = (σ : ENNReal) ^ (η + 2 * eFund) := by
                repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
                congr 1
                ring
              rw [hi,
                ← ENNReal.rpow_natCast ((σ : ENNReal) ^ (η + 2 * eFund)) 2,
                ← ENNReal.rpow_mul,
                ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
              congr 1
              ring
            _ ≤ outerFullCoeff *
                (((cScaleO : ENNReal) * (cDenO : ENNReal) *
                  (σ : ENNReal) ^ η) ^ 2) := by gcongr
        have hOuterFullPower : (σ : ENNReal) ^ (2 * η + 8 * eFund) ≤
            (ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) : ENNReal) :=
          hOuterFundPower.trans hOuterFullnessFunded
        have hlargeStrict : a < σ ^ hexp := by
          simpa only [hexp] using lt_of_not_ge hlarge
        have hOuterExp : 2 * η + 8 * eFund ≤ hexp * η64 := by
          linarith [hηOuter_le, heFundOuter]
        have hfullOuterE : (a : ENNReal) ^ η64 ≤
            (ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) : ENNReal) := by
          calc
            (a : ENNReal) ^ η64 ≤ (((σ : ENNReal) ^ hexp) ^ η64) := by
              apply ENNReal.rpow_le_rpow
              · have hc : (a : ENNReal) ≤ ((σ ^ hexp : NNReal) : ENNReal) :=
                  ENNReal.coe_le_coe.mpr hlargeStrict.le
                simpa only [ENNReal.coe_rpow_of_ne_zero hσ.ne'] using hc
              · exact hη64.le
            _ = (σ : ENNReal) ^ (hexp * η64) := by
              rw [← ENNReal.rpow_mul]
            _ ≤ (σ : ENNReal) ^ (2 * η + 8 * eFund) :=
              ENNReal.rpow_le_rpow_of_exponent_ge (by
                exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1))
                hOuterExp
            _ ≤ _ := hOuterFullPower
        have hfullOuter : a ^ η64 ≤
            ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) := by
          exact_mod_cast hfullOuterE
        have hfund0 : (σ : ENNReal) ^ η ≠ 0 := by
          exact (ENNReal.rpow_pos (by exact_mod_cast hσ) ENNReal.coe_ne_top).ne'
        have hfundTop : (σ : ENNReal) ^ η ≠ ⊤ := by
          exact ENNReal.rpow_ne_top_of_ne_zero (ENNReal.coe_ne_zero.mpr hσ.ne')
            ENNReal.coe_ne_top
        have hInvFullF :
            (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹ ≤
              (σ : ENNReal) ^ (-η) := by
          calc
            (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹ ≤
                ((σ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv.mpr hfullOriginalO
            _ = (σ : ENNReal) ^ (-η) := (ENNReal.rpow_neg _ _).symm
        have hcDen0 : (cDenO : ENNReal) ≠ 0 := by
          dsimp only [cDenO]
          rw [ENNReal.coe_inv hDenNN0Global]
          exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
        have hcDenTop : (cDenO : ENNReal) ≠ ⊤ := by
          dsimp only [cDenO]
          rw [ENNReal.coe_inv hDenNN0Global]
          exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hDenNN0Global)
        have hcScale0 : (cScaleO : ENNReal) ≠ 0 := by
          dsimp only [cScaleO]
          rw [ENNReal.coe_inv hScaleNN0Global]
          exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
        have hcScaleTop : (cScaleO : ENNReal) ≠ ⊤ := by
          dsimp only [cScaleO]
          rw [ENNReal.coe_inv hScaleNN0Global]
          exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hScaleNN0Global)
        have hfullGLower : (cDenO : ENNReal) * (σ : ENNReal) ^ η ≤
            (ShadedBody.fullness G.innerSet G.innerBody : ENNReal) := by
          calc
            (cDenO : ENNReal) * (σ : ENNReal) ^ η ≤
                (cDenO : ENNReal) *
                  (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) := by gcongr
            _ ≤ _ := hRrefO.coe_mul_fullness_le
        have hInvFullG :
            (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹ ≤
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                ENNReal) * (σ : ENNReal) ^ (-η) := by
          calc
            (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹ ≤
                ((cDenO : ENNReal) * (σ : ENNReal) ^ η)⁻¹ :=
              ENNReal.inv_le_inv.mpr hfullGLower
            _ = (cDenO : ENNReal)⁻¹ * ((σ : ENNReal) ^ η)⁻¹ := by
              rw [ENNReal.mul_inv (Or.inl hcDen0) (Or.inl hcDenTop)]
            _ = (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) * (σ : ENNReal) ^ (-η) := by
              dsimp only [cDenO]
              rw [ENNReal.coe_inv hDenNN0Global, inv_inv, ENNReal.rpow_neg]
        have hLrefGlobal : Lcore.refinementConstant =
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁)⁻¹ := by
          simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform, hdim] using
            ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv
              3 GS.innerSet.card DGS.exponent w₁
        have hRetainedLower :
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                DGS.exponent w₁ : ENNReal)⁻¹ *
              ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ≤
                retainedOuter := by
          dsimp only [retainedOuter]
          rw [hLrefGlobal, ENNReal.coe_inv hPipeNN0Global]
          gcongr
        have hRetainedInv : retainedOuter⁻¹ ≤
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) *
              (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                ENNReal) * (σ : ENNReal) ^ (-η) := by
          calc
            retainedOuter⁻¹ ≤
                ((ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal)⁻¹ *
                  ((cScaleO : ENNReal) * (cDenO : ENNReal) *
                    (σ : ENNReal) ^ η))⁻¹ := ENNReal.inv_le_inv.mpr hRetainedLower
            _ = (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) * (σ : ENNReal) ^ (-η) := by
              have hrestInv :
                  ((cScaleO : ENNReal) * (cDenO : ENNReal) *
                    (σ : ENNReal) ^ η)⁻¹ =
                    (cScaleO : ENNReal)⁻¹ * (cDenO : ENNReal)⁻¹ *
                      ((σ : ENNReal) ^ η)⁻¹ := by
                rw [ENNReal.mul_inv
                  (Or.inl (mul_ne_zero hcScale0 hcDen0))
                  (Or.inl (ENNReal.mul_ne_top hcScaleTop hcDenTop))]
                rw [ENNReal.mul_inv (Or.inl hcScale0) (Or.inl hcScaleTop)]
              rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top))
                (Or.inl (ENNReal.inv_ne_top.mpr
                  (ENNReal.coe_ne_zero.mpr hPipeNN0Global)))]
              rw [hrestInv]
              dsimp only [cScaleO, cDenO]
              rw [ENNReal.coe_inv hScaleNN0Global, ENNReal.coe_inv hDenNN0Global]
              rw [inv_inv, inv_inv, inv_inv, ENNReal.rpow_neg]
              ring
        have hCretainBound : Cretain ≤
            4 * (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) *
              (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                ENNReal) * (σ : ENNReal) ^ (-η) := by
          dsimp only [Cretain]
          calc
            4 * retainedOuter⁻¹ ≤ 4 *
                ((ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                  (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                    ENNReal) * (σ : ENNReal) ^ (-η)) :=
              mul_le_mul_left' hRetainedInv 4
            _ = 4 *
                (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) * (σ : ENNReal) ^ (-η) := by ring
        let CF : ENNReal := frostmanConstIn s
          (fun i ↦ (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        let outerFrostCoeff : ENNReal :=
          (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
            (2 * (CF *
              ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) *
                (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹) *
              ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹)) *
              Cretain * (volume plankWindow.carrier / volume scaledBall.carrier)) *
            (dO + 1 : ENNReal)
        have hOuterFrostmanQ' : IsFrostmanIn qO
            (fun j ↦ (P j).toConvexSpaceBody) plankWindow outerFrostCoeff := by
          convert hOuterFrostmanQ using 1 <;>
            dsimp only [outerFrostCoeff, CF, scaledBall] <;> push_cast <;> ring
        have hfixedFrost_le : fixedFrost₀ ≤ partAFixedEnvelope :=
          ((le_max_left _ _).trans <| (le_max_right _ _).trans <|
            (le_max_right _ _)).trans hpartAFixedBase_le
        have hfixedFrostBound : fixedFrost₀ ≤ (σ : ENNReal) ^ (-eFund) :=
          hfixedFrost_le.trans hPartAFixed.2.2
        have hrshEq : rsh = rsh₀ := rfl
        have hscaledBallEq : scaledBall = scaledBall₀ := by
          dsimp only [scaledBall, scaledBall₀]
        have hσnegPowThree : ((σ : ENNReal) ^ (-η)) ^ (3 : ℕ) =
            (σ : ENNReal) ^ (-3 * η) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1
          ring
        have hOuterFrostRaw : outerFrostCoeff ≤ fixedFrost₀ * CF *
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
              ENNReal) ^ 3 *
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) ^ 2 *
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) * (σ : ENNReal) ^ (-3 * η) := by
          dsimp only [outerFrostCoeff]
          calc
            (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
                  (2 * (CF *
                    ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) *
                      (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹) *
                    ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                      (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹)) *
                    Cretain *
                      (volume plankWindow.carrier / volume scaledBall.carrier)) *
                  (dO + 1 : ENNReal) ≤
                (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
                  (2 * (CF *
                    ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) * (σ : ENNReal) ^ (-η)) *
                    ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                      ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) * (σ : ENNReal) ^ (-η)))) *
                    (4 *
                      (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                        DGS.exponent w₁ : ENNReal) *
                      (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                      (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) * (σ : ENNReal) ^ (-η)) *
                    (volume plankWindow.carrier / volume scaledBall.carrier)) *
                  (dO + 1 : ENNReal) := by gcongr
            _ = fixedFrost₀ * CF *
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) ^ 3 *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) ^ 2 *
                (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) * (σ : ENNReal) ^ (-3 * η) := by
              rw [hscaledBallEq, hdOeq]
              dsimp only [fixedFrost₀]
              ring_nf
              rw [hσnegPowThree]
              rw [show -(η * 3) = -3 * η by ring]
              ring
        have hOuterFrostPower : outerFrostCoeff ≤
            (σ : ENNReal) ^ (-(3 * η + 7 * eFund)) * CF := by
          exact hOuterFrostRaw.trans <|
            ShadedBody.outerFrostman_loss_bound
              (ENNReal.coe_ne_zero.mpr hσ.ne') ENNReal.coe_ne_top
              hfixedFrostBound hDensityLossGlobal hScaleLossGlobal hPipelineLossGlobal
        let Csplit : NNReal := σ ^ (-(ε' / 16))
        have hFrostExp : 3 * η + 7 * eFund ≤ ε' / 16 := by
          linarith [hηEps_le, heFundEps]
        have hOuterFrostCoeffSplit : outerFrostCoeff ≤ (Csplit : ENNReal) * CF := by
          calc
            outerFrostCoeff ≤ (σ : ENNReal) ^ (-(3 * η + 7 * eFund)) * CF :=
              hOuterFrostPower
            _ ≤ (σ : ENNReal) ^ (-(ε' / 16)) * CF := by
              apply mul_le_mul_right'
              exact ENNReal.rpow_le_rpow_of_exponent_ge
                (by
                  have hcoe := ENNReal.coe_le_coe.mpr hNormLoss.2.1
                  simpa only [ENNReal.coe_one] using hcoe)
                (neg_le_neg hFrostExp)
            _ = (Csplit : ENNReal) * CF := by
              dsimp only [Csplit]
              rw [ENNReal.coe_rpow_of_ne_zero hσ.ne']
        have hOuterFrostmanSplit : IsFrostmanIn qO
            (fun j ↦ (P j).toConvexSpaceBody) plankWindow ((Csplit : ENNReal) * CF) :=
          hOuterFrostmanQ'.mono hOuterFrostCoeffSplit
        have hCsplit1 : 1 ≤ Csplit := by
          dsimp only [Csplit]
          have hneg : -(ε' / 16) ≤ 0 :=
            neg_nonpos.mpr (div_nonneg hε'.le (by norm_num))
          exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
            (x := σ) (z := -(ε' / 16)) hσ hNormLoss.2.1 hneg
        have hCF1 : 1 ≤ CF := by
          apply one_le_frostmanConstIn
          rw [Kakeya.densityIn_pos_iff]
          obtain ⟨i, hi⟩ := hfamily.nonempty
          refine ⟨i, hi, ?_, hfamily.ball i hi⟩
          simpa only [F, flatPrismFactorFamily_innerSet,
            flatPrismFactorFamily_innerBody] using hVpos i hi
        by_cases hCFtop : CF = ⊤
        · dsimp only [CF] at hCFtop
          rw [hCFtop]
          have hhalf : β / 2 ≤ (1 : ℝ) / 2 :=
            div_le_div_of_nonneg_right hβ1 (by norm_num)
          have hpPos : 0 < 1 - β / 2 :=
            (by norm_num : 0 < 1 - (1 : ℝ) / 2).trans_le
              (sub_le_sub_left hhalf 1)
          rw [ENNReal.top_rpow_of_pos hpPos]
          have haPos : 0 < a := hσ.trans_le hσa
          have hbPos : 0 < b := haPos.trans_le hab
          have hσLoss0 : (σ : ENNReal) ^ (-ε') ≠ 0 :=
            (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hσ) ENNReal.coe_ne_top).ne'
          have hratioPos : 0 < (a : ENNReal) / (b : ENNReal) :=
            ENNReal.div_pos (ENNReal.coe_ne_zero.mpr haPos.ne') ENNReal.coe_ne_top
          have hratioTop : (a : ENNReal) / (b : ENNReal) ≠ ⊤ :=
            ENNReal.div_ne_top ENNReal.coe_ne_top (ENNReal.coe_ne_zero.mpr hbPos.ne')
          have hratioPow0 : ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) ≠ 0 :=
            (ENNReal.rpow_pos hratioPos hratioTop).ne'
          have hσBetaPow0 : (σ : ENNReal) ^ (-2 * β) ≠ 0 :=
            (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hσ) ENNReal.coe_ne_top).ne'
          have hcard0 : (s.card : ENNReal) ≠ 0 := by
            exact_mod_cast hfamily.nonempty.card_ne_zero
          have hcardBasePos : 0 < (s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ) :=
            ENNReal.mul_pos hcard0 (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hσ.ne'))
          have hcardPow0 :
              ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^ (1 - β / 2) ≠ 0 :=
            (ENNReal.rpow_pos hcardBasePos (by finiteness)).ne'
          rw [ENNReal.mul_top hσLoss0, ENNReal.top_mul hratioPow0,
            ENNReal.top_mul hσBetaPow0, ENNReal.top_mul hcardPow0]
          exact le_top
        · let Couter : NNReal :=
            edParentCount.COfTestDilate 3 Dpar 1
              (2 * (A * C_NC * Dpar)) * flatPrismOuterSplit.C Cw C_NC
          let CouterBig : NNReal := max 1 Couter
          let Cbig : NNReal := CouterBig * Csplit
          have hCouterEq : Couter = Couter₀ := by
            dsimp only [Couter, Couter₀, A]
          have hCouterBig1 : 1 ≤ CouterBig := le_max_left _ _
          have hCouterBigFixed : (CouterBig : ENNReal) ≤ partAFixedEnvelope := by
            rw [show (CouterBig : ENNReal) = max 1 (Couter : ENNReal) by
              simp only [CouterBig, ENNReal.coe_max, ENNReal.coe_one]]
            apply max_le hpartAFixed1
            rw [hCouterEq]
            exact ((le_max_left _ _).trans <| (le_max_right _ _).trans <|
              (le_max_right _ _).trans <| (le_max_right _ _).trans <|
                (le_max_right _ _)).trans hpartAFixedBase_le
          have hCouterBigBound : (CouterBig : ENNReal) ≤
              (σ : ENNReal) ^ (-eFund) := hCouterBigFixed.trans hPartAFixed.2.2
          have hCbig1 : 1 ≤ Cbig := one_le_mul hCouterBig1 hCsplit1
          have hCsplitBig : Csplit ≤ Cbig := by
            dsimp only [Cbig]
            exact le_mul_of_one_le_left (by positivity) hCouterBig1
          have hba1 : 1 ≤ b / a := by
            rw [le_div_iff₀ (hσ.trans_le hσa)]
            simpa only [one_mul] using hab
          have hMbig1 : 1 ≤ Cbig * (b / a) := one_le_mul hCbig1 hba1
          have hNCbig : Plank.IsThickeningNonconcentrated qO
              (fun j ↦ (P j).toPrism3D) C_NC (Cbig * (b / a)) := by
            intro j hj φ hφ1 hφab
            have hjW : j ∈ W.outerSet := hqOsub hj
            calc
              ((qO.filter fun k ↦ ((P k).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
                    (((Plank.thickened (P j).toPrism3D φ hφ1).toPrismNDim.dilation
                      C_NC).carrier : Set (EuclideanSpace ℝ (Fin 3)))).card : NNReal) ≤
                  ((W.outerSet.filter fun k ↦
                    ((P k).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
                    (((Plank.thickened (P j).toPrism3D φ hφ1).toPrismNDim.dilation
                      C_NC).carrier : Set (EuclideanSpace ℝ (Fin 3)))).card : NNReal) := by
                exact_mod_cast Finset.card_le_card
                  (Finset.filter_subset_filter _ hqOsub)
              _ ≤ Couter * (b / a) * φ := by
                simpa only [Couter] using hOuterNC C_NC hC_NC j hjW φ hφ1 hφab
              _ ≤ Cbig * (b / a) * φ := by
                gcongr
                dsimp only [Cbig, CouterBig]
                exact (le_max_right _ _).trans
                  (le_mul_of_one_le_right (by positivity) hCsplit1)
          have hCFsplit1 : 1 ≤ (Csplit : ENNReal) * CF := by
            exact one_le_mul (by exact_mod_cast hCsplit1) hCF1
          have hCFsplitTop : (Csplit : ENNReal) * CF ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop
          have h64OuterRaw := h64 qO hab hb1 P (hσ.trans_le hσa) le_rfl
            (hbSmallCase.trans (min_le_left _ _)) (fun j hj ↦ hPwindow j (hqOsub hj))
            hqOED hfullOuter (Cbig * (b / a)) hMbig1 hNCbig
            ((Csplit : ENNReal) * CF) hCFsplit1 hCFsplitTop hOuterFrostmanSplit
          have h64Outer : ShadedBody.multiplicity qO
              (fun j ↦ (P j).toShadedBody) ≤
                (a : ENNReal) ^ (-(ε' / 4)) *
                ((Csplit : ENNReal) * CF) ^ (1 - β / 2) *
                ((Cbig * (b / a) : NNReal) : ENNReal) ^ (β / 2) *
                ((a : ENNReal) / (b : ENNReal)) *
                (b : ENNReal) ^ (-2 * β) *
                ((b : ENNReal) ^ 2 * (qO.card : ENNReal)) ^ (1 - β / 2) := by
            have hApow : (a : ENNReal) ^ (-(ε' / 12)) ≤
                (a : ENNReal) ^ (-(ε' / 4)) := by
              exact ENNReal.rpow_le_rpow_of_exponent_ge
                (by
                  have hcoe := ENNReal.coe_le_coe.mpr (hab.trans hb1)
                  simpa only [ENNReal.coe_one] using hcoe)
                (by linarith [hε'])
            let outerRest : ENNReal :=
              ((Csplit : ENNReal) * CF) ^ (1 - β / 2) *
                ((Cbig * (b / a) : NNReal) : ENNReal) ^ (β / 2) *
                ((a : ENNReal) / (b : ENNReal)) *
                (b : ENNReal) ^ (-2 * β) *
                ((b : ENNReal) ^ 2 * (qO.card : ENNReal)) ^ (1 - β / 2)
            calc
              ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) ≤
                  (a : ENNReal) ^ (-(ε' / 12)) *
                  ((Csplit : ENNReal) * CF) ^ (1 - β / 2) *
                  ((Cbig * (b / a) : NNReal) : ENNReal) ^ (β / 2) *
                  ((a : ENNReal) / (b : ENNReal)) *
                  (b : ENNReal) ^ (-2 * β) *
                  ((b : ENNReal) ^ 2 * (qO.card : ENNReal)) ^
                    (1 - β / 2) := h64OuterRaw
              _ = (a : ENNReal) ^ (-(ε' / 12)) * outerRest := by
                dsimp only [outerRest]
                ring
              _ ≤ (a : ENNReal) ^ (-(ε' / 4)) * outerRest :=
                mul_le_mul_right' hApow outerRest
              _ = _ := by
                dsimp only [outerRest]
                ring
          have hsplitToCsplit : splitExact ≤ (Csplit : ENNReal) := by
            calc
              splitExact ≤ (σ : ENNReal) ^ (-(4 * eFund)) := hsplitExactBound
              _ ≤ (σ : ENNReal) ^ (-(ε' / 16)) :=
                ENNReal.rpow_le_rpow_of_exponent_ge
                  (by
                    have hcoe := ENNReal.coe_le_coe.mpr hNormLoss.2.1
                    simpa only [ENNReal.coe_one] using hcoe)
                  (by linarith [heFundEps])
              _ = (Csplit : ENNReal) := by
                dsimp only [Csplit]
                rw [ENNReal.coe_rpow_of_ne_zero hσ.ne']
          have hqOcardW : qO.card ≤ W.outerSet.card := Finset.card_le_card hqOsub
          have hqOcardWE : (qO.card : ENNReal) ≤ (W.outerSet.card : ENNReal) := by
            exact_mod_cast hqOcardW
          let innerTargetQ : ENNReal := (σ : ENNReal) ^ (-(ε' / 4)) *
            ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
            ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
            (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
              ((s.card : ENNReal) / (qO.card : ENNReal))) ^ (1 - β / 2)
          have hinnerTargetWQ : innerTarget ≤ innerTargetQ := by
            have hσpow : (σ : ENNReal) ^ (-(ε' / 12)) ≤
                (σ : ENNReal) ^ (-(ε' / 4)) := by
              exact ENNReal.rpow_le_rpow_of_exponent_ge
                (by
                  have hcoe := ENNReal.coe_le_coe.mpr hNormLoss.2.1
                  simpa only [ENNReal.coe_one] using hcoe)
                (by linarith [hε'])
            have hdiv : (s.card : ENNReal) / (W.outerSet.card : ENNReal) ≤
                (s.card : ENNReal) / (qO.card : ENNReal) :=
              ENNReal.div_le_div_left hqOcardWE (s.card : ENNReal)
            have hcardBase :
                ((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                    ((s.card : ENNReal) / (W.outerSet.card : ENNReal)) ≤
                  ((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                    ((s.card : ENNReal) / (qO.card : ENNReal)) :=
              mul_le_mul_left' hdiv (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2)
            have hcardPow := ENNReal.rpow_le_rpow hcardBase hpOuter
            let restW : ENNReal :=
              ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
                (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                  ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^ (1 - β / 2)
            let restQ : ENNReal :=
              ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
                (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                  ((s.card : ENNReal) / (qO.card : ENNReal))) ^ (1 - β / 2)
            have hrest : restW ≤ restQ := by
              dsimp only [restW, restQ]
              exact mul_le_mul_left' hcardPow
                (((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                  ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β))
            calc
              innerTarget = (σ : ENNReal) ^ (-(ε' / 12)) * restW := by
                dsimp only [innerTarget, restW]
                ring
              _ ≤ (σ : ENNReal) ^ (-(ε' / 4)) * restW :=
                mul_le_mul_right' hσpow restW
              _ ≤ (σ : ENNReal) ^ (-(ε' / 4)) * restQ :=
                mul_le_mul_left' hrest ((σ : ENNReal) ^ (-(ε' / 4)))
              _ = innerTargetQ := by
                dsimp only [innerTargetQ, restQ]
                ring
          have hsplitLocalF : ShadedBody.multiplicity F.innerSet F.innerBody ≤
              (Csplit : ENNReal) *
                ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) *
                  innerTargetQ := by
            calc
              ShadedBody.multiplicity F.innerSet F.innerBody ≤
                  splitExact *
                    ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) *
                      innerTarget := hsplitExact
              _ ≤ (Csplit : ENNReal) *
                    ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) *
                      innerTargetQ := by gcongr
          have hsplitLocal : ShadedBody.multiplicity s
                (fun i ↦ (V i).toShadedBody) ≤
              (Csplit : ENNReal) *
                ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) *
                  ((σ : ENNReal) ^ (-(ε' / 4)) *
                    ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                    ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
                    (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                      ((s.card : ENNReal) / (qO.card : ENNReal))) ^
                        (1 - β / 2)) := by
            simpa only [F, flatPrismFactorFamily_innerSet,
              flatPrismFactorFamily_innerBody, innerTargetQ] using hsplitLocalF
          have hCbigBound : (Cbig : ENNReal) ≤
              (σ : ENNReal) ^ (-(eFund + ε' / 16)) := by
            calc
              (Cbig : ENNReal) = (CouterBig : ENNReal) * (Csplit : ENNReal) := by
                simp only [Cbig, ENNReal.coe_mul]
              _ ≤ (σ : ENNReal) ^ (-eFund) *
                  (σ : ENNReal) ^ (-(ε' / 16)) := by
                gcongr
                dsimp only [Csplit]
                rw [ENNReal.coe_rpow_of_ne_zero hσ.ne']
              _ = (σ : ENNReal) ^ (-(eFund + ε' / 16)) := by
                rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
                congr 1
                ring
          have hpBig0 : 0 ≤ 1 + β / 2 := by linarith
          have hpBigLe : 1 + β / 2 ≤ 3 / 2 := by linarith
          have hmulBig : (eFund + ε' / 16) * (1 + β / 2) ≤ ε' / 4 := by
            calc
              (eFund + ε' / 16) * (1 + β / 2) ≤
                  (ε' / 512 + ε' / 16) * (3 / 2) := by
                exact mul_le_mul (by linarith [heFundEps]) hpBigLe
                  (by positivity) (by positivity)
              _ ≤ ε' / 4 := by linarith [hε']
          have hthrBig : (Cbig : ENNReal) ^ (1 + β / 2) ≤
              (σ : ENNReal) ^ (-(ε' / 4)) := by
            calc
              (Cbig : ENNReal) ^ (1 + β / 2) ≤
                  ((σ : ENNReal) ^ (-(eFund + ε' / 16))) ^ (1 + β / 2) :=
                ENNReal.rpow_le_rpow hCbigBound hpBig0
              _ = (σ : ENNReal) ^ (-((eFund + ε' / 16) * (1 + β / 2))) := by
                rw [← ENNReal.rpow_mul]
                congr 1
                ring
              _ ≤ (σ : ENNReal) ^ (-(ε' / 4)) :=
                ENNReal.rpow_le_rpow_of_exponent_ge
                  (by
                    have hcoe := ENNReal.coe_le_coe.mpr hNormLoss.2.1
                    simpa only [ENNReal.coe_one] using hcoe)
                  (by linarith)
          have hpSplit0 : 0 ≤ 1 - β / 2 := by linarith
          have hthr2 : (Csplit : ENNReal) ^ (1 - β / 2) ≤
              (σ : ENNReal) ^ (-(ε' / 4)) := by
            calc
              (Csplit : ENNReal) ^ (1 - β / 2) =
                  (σ : ENNReal) ^ (-(ε' / 16) * (1 - β / 2)) := by
                dsimp only [Csplit]
                rw [ENNReal.coe_rpow_of_ne_zero hσ.ne', ← ENNReal.rpow_mul]
              _ ≤ (σ : ENNReal) ^ (-(ε' / 4)) :=
                ENNReal.rpow_le_rpow_of_exponent_ge
                  (by
                    have hcoe := ENNReal.coe_le_coe.mpr hNormLoss.2.1
                    simpa only [ENNReal.coe_one] using hcoe)
                  (by nlinarith [hβ0, hβ1, hε'])
          have hfinal := localHighBranchBound hβpos hβ1 hε' hσ
            (hσ.trans_le hσa) hab hσa hCsplit1 hCsplitBig hCbig1 hCF1 hCFtop
            hqOcard0 h64Outer hsplitLocal hthrBig hthr2
          simpa only [CF, mul_comm ((σ : ENNReal) ^ 2) (s.card : ENNReal)] using hfinal
      · have ha0nn : a ≠ 0 := (hσ.trans_le hσa).ne'
        have hb0nn : b ≠ 0 := ((hσ.trans_le hσa).trans_le hab).ne'
        have hAinEq : Ain = Cwi * a := rfl
        have hbIform : bI = Cwi⁻¹ * (a⁻¹ * σ) := by
          rw [hbI, hAinEq]
          field_simp [hCwipos.ne', ha0nn]
        have hratioNN : aI / bI = Ain / Bin := hratioI
        have hAin0 : Ain ≠ 0 := by rw [hAinEq]; positivity
        have hBin0 : Bin ≠ 0 :=
          (((hσ.trans_le hσa).trans_le hab).trans_le hbBin).ne'
        have hratioAin0 : Ain / Bin ≠ 0 := div_ne_zero hAin0 hBin0
        have hbI0nn : bI ≠ 0 := by
          rw [hbI]
          exact div_ne_zero hσ.ne' hAin0
        have hMI0nn : MI ≠ 0 := (zero_lt_one.trans_le hMI1).ne'
        have hCinner0nn : Cinner ≠ 0 := (zero_lt_one.trans_le hCinner).ne'
        have hMIRatioNN : MI ^ (β / 2) * (aI / bI) =
            Cinner ^ (β / 2) * (Ain / Bin) ^ (1 - β) := by
          dsimp only [MI]
          rw [NNReal.mul_rpow, hratioNN]
          have hcollect : ((Bin / Ain) ^ 2) ^ (β / 2) * (Ain / Bin) =
              (Ain / Bin) ^ (1 - β) := by
            have hinv : Bin / Ain = (Ain / Bin)⁻¹ := by
              field_simp [hAin0, hBin0]
            rw [hinv, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
            change (Ain / Bin)⁻¹ ^ ((2 : ℝ) * (β / 2)) * (Ain / Bin) =
              (Ain / Bin) ^ (1 - β)
            have hinvpow : ((Ain / Bin)⁻¹) ^ β = (Ain / Bin) ^ (-β) := by
              calc
                ((Ain / Bin)⁻¹) ^ β = ((Ain / Bin) ^ (-1 : ℝ)) ^ β := by
                  rw [NNReal.rpow_neg, NNReal.rpow_one]
                _ = (Ain / Bin) ^ ((-1 : ℝ) * β) := by rw [NNReal.rpow_mul]
                _ = (Ain / Bin) ^ (-β) := by congr 1; ring
            rw [show (2 : ℝ) * (β / 2) = β by ring, hinvpow]
            calc
              (Ain / Bin) ^ (-β) * (Ain / Bin) =
                  (Ain / Bin) ^ (-β) * (Ain / Bin) ^ (1 : ℝ) := by
                    rw [NNReal.rpow_one]
              _ = (Ain / Bin) ^ (-β + 1) :=
                (NNReal.rpow_add hratioAin0 (-β) 1).symm
              _ = (Ain / Bin) ^ (1 - β) := by congr 1; ring
          calc
            Cinner ^ (β / 2) * ((Bin / Ain) ^ 2) ^ (β / 2) * (Ain / Bin) =
                Cinner ^ (β / 2) *
                  (((Bin / Ain) ^ 2) ^ (β / 2) * (Ain / Bin)) := by ring
            _ = _ := by rw [hcollect]
        have hAinBinLe : Ain / Bin ≤ Cwi * (a / b) := by
          rw [div_le_iff₀ (pos_iff_ne_zero.mpr hBin0)]
          calc
            Ain = Cwi * (a / b) * b := by
              rw [hAinEq]
              field_simp [hb0nn]
            _ ≤ Cwi * (a / b) * Bin := by gcongr
        have hratioPowLe : (Ain / Bin) ^ (1 - β) ≤
            Cwi ^ (1 - β) * (a / b) ^ (1 - β) := by
          calc
            (Ain / Bin) ^ (1 - β) ≤ (Cwi * (a / b)) ^ (1 - β) :=
              NNReal.rpow_le_rpow hAinBinLe (by linarith)
            _ = _ := NNReal.mul_rpow
        have hMIRatioE : (MI : ENNReal) ^ (β / 2) *
              ((aI : ENNReal) / (bI : ENNReal)) =
            (Cinner : ENNReal) ^ (β / 2) *
              ((Ain : ENNReal) / (Bin : ENNReal)) ^ (1 - β) := by
          have hcast := congrArg (fun x : NNReal ↦ (x : ENNReal)) hMIRatioNN
          simpa only [ENNReal.coe_mul,
            ENNReal.coe_rpow_of_ne_zero hMI0nn,
            ENNReal.coe_div hbI0nn,
            ENNReal.coe_rpow_of_ne_zero hCinner0nn,
            ENNReal.coe_div hBin0,
            ENNReal.coe_rpow_of_ne_zero hratioAin0] using hcast
        have hratioPowE :
            ((Ain : ENNReal) / (Bin : ENNReal)) ^ (1 - β) ≤
              (Cwi : ENNReal) ^ (1 - β) *
                ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) := by
          have hcast := ENNReal.coe_le_coe.mpr hratioPowLe
          simpa only [ENNReal.coe_rpow_of_ne_zero hratioAin0,
            ENNReal.coe_div hBin0, ENNReal.coe_mul,
            ENNReal.coe_rpow_of_ne_zero hCwipos.ne', ENNReal.coe_div hb0nn,
            ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha0nn hb0nn)] using hcast
        have hshapeRatio : (MI : ENNReal) ^ (β / 2) *
              ((aI : ENNReal) / (bI : ENNReal)) ≤
            (Cinner : ENNReal) ^ (β / 2) * (Cwi : ENNReal) ^ (1 - β) *
              ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) := by
          calc
            (MI : ENNReal) ^ (β / 2) *
                ((aI : ENNReal) / (bI : ENNReal)) =
                (Cinner : ENNReal) ^ (β / 2) *
                  ((Ain : ENNReal) / (Bin : ENNReal)) ^ (1 - β) := hMIRatioE
            _ ≤ (Cinner : ENNReal) ^ (β / 2) *
                ((Cwi : ENNReal) ^ (1 - β) *
                  ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)) :=
              mul_le_mul_left' hratioPowE ((Cinner : ENNReal) ^ (β / 2))
            _ = _ := by ring
        have hshapeScaleNN : bI ^ (-2 * β) =
            Cwi ^ (2 * β) * (a⁻¹ * σ) ^ (-2 * β) := by
          rw [hbIform, NNReal.mul_rpow]
          congr 1
          calc
            (Cwi⁻¹) ^ (-2 * β) = (Cwi ^ (-1 : ℝ)) ^ (-2 * β) := by
              rw [NNReal.rpow_neg, NNReal.rpow_one]
            _ = Cwi ^ ((-1 : ℝ) * (-2 * β)) := by rw [← NNReal.rpow_mul]
            _ = Cwi ^ (2 * β) := by congr 1; ring
        have hshapeScale : (bI : ENNReal) ^ (-2 * β) =
            (Cwi : ENNReal) ^ (2 * β) *
              ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) := by
          have hbase0nn : a⁻¹ * σ ≠ 0 := mul_ne_zero (inv_ne_zero ha0nn) hσ.ne'
          have hcast := congrArg (fun x : NNReal ↦ (x : ENNReal)) hshapeScaleNN
          simpa only [ENNReal.coe_rpow_of_ne_zero hbI0nn, ENNReal.coe_mul,
            ENNReal.coe_rpow_of_ne_zero hCwipos.ne', ENNReal.coe_inv ha0nn,
            ENNReal.coe_rpow_of_ne_zero hbase0nn] using hcast
        let CcardI : ENNReal := 2 * (flatPrismBodyVolumeRatio.C Cw : ENNReal)
        have hWcardE0 : (W.outerSet.card : ENNReal) ≠ 0 := by
          exact_mod_cast hWne.card_ne_zero
        have hWcardETop : (W.outerSet.card : ENNReal) ≠ ⊤ := by finiteness
        have hHfibEq : H.fiber x₀ = W.fiber x₀ := by
          dsimp only [H]
          rw [ShadedBody.FactorFamily.restrictOuter_fiber_of_mem GS W.outerSet hx₀,
            hWfibEq]
        have hqIprod : (qI.card : ENNReal) * (W.outerSet.card : ENNReal) ≤
            CcardI * (s.card : ENNReal) := by
          calc
            (qI.card : ENNReal) * (W.outerSet.card : ENNReal) ≤
                ((W.fiber x₀).card : ENNReal) * (W.outerSet.card : ENNReal) := by
              apply mul_le_mul_right'
              exact_mod_cast hcardIsub
            _ ≤ CcardI * (s.card : ENNReal) := by
              simpa only [CcardI, ← hHfibEq] using hHcard x₀ hx₀
        have hqIDiv : (qI.card : ENNReal) ≤
            CcardI * ((s.card : ENNReal) / (W.outerSet.card : ENNReal)) := by
          calc
            (qI.card : ENNReal) ≤
                (CcardI * (s.card : ENNReal)) / (W.outerSet.card : ENNReal) :=
              (ENNReal.le_div_iff_mul_le (Or.inl hWcardE0) (Or.inl hWcardETop)).2 hqIprod
            _ = CcardI * ((s.card : ENNReal) / (W.outerSet.card : ENNReal)) := by
              simp only [div_eq_mul_inv]
              ring
        have hbIle : (bI : ENNReal) ≤ (a : ENNReal)⁻¹ * (σ : ENNReal) := by
          calc
            (bI : ENNReal) = ((Cwi⁻¹ * (a⁻¹ * σ) : NNReal) : ENNReal) := by
              exact congrArg (fun x : NNReal ↦ (x : ENNReal)) hbIform
            _ = (Cwi : ENNReal)⁻¹ * ((a : ENNReal)⁻¹ * (σ : ENNReal)) := by
              simp only [ENNReal.coe_mul, ENNReal.coe_inv hCwipos.ne',
                ENNReal.coe_inv ha0nn]
            (Cwi : ENNReal)⁻¹ * ((a : ENNReal)⁻¹ * (σ : ENNReal)) ≤
                1 * ((a : ENNReal)⁻¹ * (σ : ENNReal)) := by
              gcongr
              exact ENNReal.inv_le_one.mpr (by exact_mod_cast hCwi)
            _ = _ := one_mul _
        have hpOuter : 0 ≤ 1 - β / 2 := by linarith
        have hshapeCard : ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
              (1 - β / 2) ≤ CcardI ^ (1 - β / 2) *
              (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^
                  (1 - β / 2) := by
          have hbase : (bI : ENNReal) ^ 2 * (qI.card : ENNReal) ≤
              CcardI * (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) := by
            calc
              (bI : ENNReal) ^ 2 * (qI.card : ENNReal) ≤
                  ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ 2 *
                    (CcardI * ((s.card : ENNReal) /
                      (W.outerSet.card : ENNReal))) := by gcongr
              _ = _ := by rw [mul_pow, ENNReal.inv_pow]; ring
          calc
            ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^ (1 - β / 2) ≤
                (CcardI * (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                  ((s.card : ENNReal) / (W.outerSet.card : ENNReal)))) ^
                    (1 - β / 2) := ENNReal.rpow_le_rpow hbase hpOuter
            _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hpOuter
        let innerFixedLarge : ENNReal := (dED + 1 : ENNReal) * CFI ^ (1 - β / 2) *
          (Cinner : ENNReal) ^ (β / 2) * (Cwi : ENNReal) ^ (1 - β) *
            (Cwi : ENNReal) ^ (2 * β) * CcardI ^ (1 - β / 2)
        let innerTarget : ENNReal := (σ : ENNReal) ^ (-(ε' / 12)) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
          ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
          (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
            ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^ (1 - β / 2)
        have hinnerCanonical : ShadedBody.multiplicity (W.fiber x₀)
              (fun i ↦ (Tin i).toShadedBody) ≤ innerFixedLarge * innerTarget := by
          calc
            ShadedBody.multiplicity (W.fiber x₀) (fun i ↦ (Tin i).toShadedBody) ≤
                (dED + 1 : ENNReal) *
                  ShadedBody.multiplicity qI (fun i ↦ (PI i).toShadedBody) := hmultI
            _ ≤ (dED + 1 : ENNReal) *
                ((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2) *
                  (MI : ENNReal) ^ (β / 2) *
                  ((aI : ENNReal) / (bI : ENNReal)) *
                  (bI : ENNReal) ^ (-2 * β) *
                  ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                    (1 - β / 2)) := by gcongr
            _ ≤ innerFixedLarge * innerTarget := by
              let pref : ENNReal := (dED + 1 : ENNReal) *
                ((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2))
              let ratioI : ENNReal := (MI : ENNReal) ^ (β / 2) *
                ((aI : ENNReal) / (bI : ENNReal))
              let ratioT : ENNReal := (Cinner : ENNReal) ^ (β / 2) *
                (Cwi : ENNReal) ^ (1 - β) *
                ((a : ENNReal) / (b : ENNReal)) ^ (1 - β)
              let scaleI : ENNReal := (bI : ENNReal) ^ (-2 * β)
              let scaleT : ENNReal := (Cwi : ENNReal) ^ (2 * β) *
                ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β)
              let cardI : ENNReal :=
                ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^ (1 - β / 2)
              let cardT : ENNReal := CcardI ^ (1 - β / 2) *
                (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                  ((s.card : ENNReal) / (W.outerSet.card : ENNReal))) ^ (1 - β / 2)
              have hratioIT : ratioI ≤ ratioT := by
                simpa only [ratioI, ratioT] using hshapeRatio
              have hscaleIT : scaleI ≤ scaleT := by
                simpa only [scaleI, scaleT] using hshapeScale.le
              have hcardIT : cardI ≤ cardT := by
                simpa only [cardI, cardT] using hshapeCard
              calc
                (dED + 1 : ENNReal) *
                    ((σ : ENNReal) ^ (-(ε' / 12)) * CFI ^ (1 - β / 2) *
                      (MI : ENNReal) ^ (β / 2) *
                      ((aI : ENNReal) / (bI : ENNReal)) *
                      (bI : ENNReal) ^ (-2 * β) *
                      ((bI : ENNReal) ^ 2 * (qI.card : ENNReal)) ^
                        (1 - β / 2)) = pref * ratioI * scaleI * cardI := by
                    dsimp only [pref, ratioI, scaleI, cardI]
                    ring
                _ ≤ pref * ratioT * scaleT * cardT := by
                  exact mul_le_mul
                    (mul_le_mul
                      (mul_le_mul le_rfl hratioIT bot_le bot_le)
                      hscaleIT bot_le bot_le)
                    hcardIT bot_le bot_le
                _ = innerFixedLarge * innerTarget := by
                  dsimp only [pref, ratioT, scaleT, cardT, innerFixedLarge, innerTarget]
                  ring
        have hTinMultiplicity : ShadedBody.multiplicity (W.fiber x₀)
                (fun i ↦ (Tin i).toShadedBody) =
              ShadedBody.multiplicity (W.fiber x₀) W.innerBody := by
          have hbody : (fun i ↦ (Tin i).toShadedBody) =
              (fun i ↦ (W.innerBody i).mapLinearIsometryEquiv f) := by
            funext i
            apply ShadedBody.ext_of_toConvexSpaceBody_eq
            · exact hTinConvex i
            · rfl
          rw [hbody]
          exact ShadedBody.multiplicity_mapLinearIsometryEquiv
            (W.fiber x₀) W.innerBody f
        have hinnerCanonicalW : ShadedBody.multiplicity (W.fiber x₀) W.innerBody ≤
            innerFixedLarge * innerTarget := by
          rw [← hTinMultiplicity]
          exact hinnerCanonical
        let splitExact : ENNReal :=
          (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
              (ShadedBody.factoringCoreAtScaleUniformProductConstant
                (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                (dO + 1 : ENNReal) * innerFixedLarge
        have hsplitExact : ShadedBody.multiplicity F.innerSet F.innerBody ≤
            splitExact * ShadedBody.multiplicity qO
              (fun j ↦ (P j).toShadedBody) * innerTarget := by
          calc
            ShadedBody.multiplicity F.innerSet F.innerBody ≤
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                    (ShadedBody.factoringCoreAtScaleUniformProductConstant
                      (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                      ShadedBody.multiplicity W.outerSet W.outerBody *
                        ShadedBody.multiplicity (W.fiber x₀) W.innerBody := hProductOriginal
            _ = (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                    (ShadedBody.factoringCoreAtScaleUniformProductConstant
                      (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                      ShadedBody.multiplicity W.outerSet
                        (fun j ↦ (P j).toShadedBody) *
                        ShadedBody.multiplicity (W.fiber x₀) W.innerBody := by rw [hmultP]
            _ ≤ (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                    (ShadedBody.factoringCoreAtScaleUniformProductConstant
                      (Module.finrank ℝ E) GS.innerSet.card DGS.exponent w₁ : ENNReal) *
                      ((dO + 1 : ENNReal) *
                        ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody)) *
                        (innerFixedLarge * innerTarget) := by
                  gcongr
                  simpa using hmultqO
            _ = splitExact * ShadedBody.multiplicity qO
                (fun j ↦ (P j).toShadedBody) * innerTarget := by
              dsimp only [splitExact]
              ring
        have hdOeq : dO = dO₀ := by
          dsimp only [dO, dO₀, Cextract, Cextract₀, A]
        have hinnerLargeFormula : innerFixedLarge =
            innerFixed₀ * (Cwi : ENNReal) ^ (1 - β) := by
          dsimp only [innerFixedLarge, innerFixed₀, CFI, CFI₀, CcardI]
          ring
        have hsplitFormula : splitExact = splitFixed₀ *
            (Cwi : ENNReal) ^ (1 - β) *
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) := by
          dsimp only [splitExact]
          rw [ShadedBody.factoringCoreAtScaleUniformProductConstant_eq, hdim,
            hdOeq, hinnerLargeFormula]
          dsimp only [splitFixed₀]
          push_cast
          ring
        have hsplitBound : splitExact ≤ (σ : ENNReal) ^ (-(5 * eFund)) := by
          rw [hsplitFormula]
          calc
            splitFixed₀ * (Cwi : ENNReal) ^ (1 - β) *
                  (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                  (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal) ≤
                (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-eFund) *
                  (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-eFund) *
                  (σ : ENNReal) ^ (-eFund) := by
              gcongr
              · have hsplitFixedEnvelope : splitFixed₀ ≤ partAFixedEnvelope := by
                  exact ((le_max_left splitFixed₀
                    (max fixedFrost₀ (max fixedFull₀ (max (Couter₀ : ENNReal)
                      (max (CparentTotal₀ : ENNReal)
                        (max (Cdiv₀ : ENNReal) (Cm : ENNReal)⁻¹)))))).trans
                    (le_max_right 1 _)).trans hpartAFixedBase_le
                exact hsplitFixedEnvelope.trans hPartAFixed.2.2
              · exact (le_max_right _ _).trans hCwiExtraLoss.2.2
            _ = (σ : ENNReal) ^ (-(5 * eFund)) := by
              repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              congr 1
              ring
        have hinvLossLarge : ∀ C : NNReal, C ≠ 0 →
            (C : ENNReal) ≤ (σ : ENNReal) ^ (-eFund) →
              (σ : ENNReal) ^ eFund ≤ (C : ENNReal)⁻¹ := by
          intro C hC0 hCle
          apply ENNReal.le_inv_iff_mul_le.mpr
          calc
            (σ : ENNReal) ^ eFund * (C : ENNReal) ≤
                (σ : ENNReal) ^ eFund * (σ : ENNReal) ^ (-eFund) := by gcongr
            _ = 1 := by
              rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              simp
        have hDenInvLossLarge : (σ : ENNReal) ^ eFund ≤
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
              ENNReal)⁻¹ := hinvLossLarge _ hDenNN0Global hDensityLossGlobal
        have hScaleInvLossLarge : (σ : ENNReal) ^ eFund ≤
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal)⁻¹ :=
          hinvLossLarge _ hScaleNN0Global hScaleLossGlobal
        let fullCoreCLarge : NNReal :=
          ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3 GS.innerSet.card
            DGS.exponent w₁
        have hfullCoreCLarge0 : fullCoreCLarge ≠ 0 := by
          dsimp only [fullCoreCLarge,
            ShadedBody.factoringCoreAtScaleUniformFullnessConstant]
          rw [ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv]
          exact mul_ne_zero (inv_ne_zero (by
              exact mul_ne_zero
                (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
                  ShadedBody.lambdaInducedSingleWUniform.C_pos.ne')
                (by positivity)))
            (pow_ne_zero _ (inv_ne_zero hPipeNN0Global))
        let outerFullCoeffNNLarge : NNReal := ((dO + 1 : ℕ) : NNReal)⁻¹ *
          (flatPrismEnvelopeVolumeRatio.C Cw)⁻¹ * (fullCoreCLarge * 2⁻¹)
        have houterFullCoeffNNLarge0 : outerFullCoeffNNLarge ≠ 0 := by
          dsimp only [outerFullCoeffNNLarge]
          exact mul_ne_zero
            (mul_ne_zero (inv_ne_zero (by positivity))
              (inv_ne_zero (zero_lt_one.trans_le
                (flatPrismEnvelopeVolumeRatio.one_le Cw)).ne'))
            (mul_ne_zero hfullCoreCLarge0 (inv_ne_zero (by norm_num)))
        have houterFullCoeffCoeLarge :
            (outerFullCoeffNNLarge : ENNReal) = outerFullCoeff := by
          dsimp only [outerFullCoeffNNLarge, outerFullCoeff, coreFullCoeff, fullCoreCLarge]
          simp only [ENNReal.coe_mul,
            ENNReal.coe_inv (by positivity : (((dO + 1 : ℕ) : NNReal)) ≠ 0),
            ENNReal.coe_inv (by
              exact (zero_lt_one.trans_le
                (flatPrismEnvelopeVolumeRatio.one_le Cw)).ne'),
            ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0)]
          rw [hdim]
          push_cast
          ring
        have houterFullInvFormulaLarge : (outerFullCoeffNNLarge : ENNReal)⁻¹ =
            fixedFull₀ * (DGS.exponent + 1 : ℕ) *
              (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                DGS.exponent w₁ : ENNReal) ^ 2 := by
          rw [← ENNReal.coe_inv houterFullCoeffNNLarge0]
          norm_cast
          dsimp only [outerFullCoeffNNLarge, fullCoreCLarge]
          repeat' rw [mul_inv_rev]
          rw [inv_inv (((dO + 1 : ℕ) : NNReal)),
            inv_inv (flatPrismEnvelopeVolumeRatio.C Cw), inv_inv (2 : NNReal),
            ShadedBody.inv_factoringCoreAtScaleUniformFullnessConstant_eq]
          rw [hdOeq]
          dsimp only [fixedFull₀]
          push_cast
          ring
        have hfixedFullLarge_le : fixedFull₀ ≤ partAFixedEnvelope :=
          ((le_max_left _ _).trans <| (le_max_right _ _).trans <|
            (le_max_right _ _).trans <| (le_max_right _ _)).trans hpartAFixedBase_le
        have houterFullInvBoundLarge : outerFullCoeff⁻¹ ≤
            (σ : ENNReal) ^ (-(4 * eFund)) := by
          rw [← houterFullCoeffCoeLarge, houterFullInvFormulaLarge]
          calc
            fixedFull₀ * (DGS.exponent + 1 : ℕ) *
                  (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal) ^ 2 ≤
                (σ : ENNReal) ^ (-eFund) * (σ : ENNReal) ^ (-(eFund / 4)) *
                  ((σ : ENNReal) ^ (-eFund)) ^ 2 := by
              gcongr
              · exact hfixedFullLarge_le.trans hPartAFixed.2.2
              · simpa only [show DGS.exponent = D.exponent from rfl] using hDexpGlobal
            _ ≤ (σ : ENNReal) ^ (-(4 * eFund)) := by
              rw [← ENNReal.rpow_natCast]
              repeat' rw [← ENNReal.rpow_mul]
              repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                ENNReal.coe_ne_top]
              apply ENNReal.rpow_le_rpow_of_exponent_ge (by
                exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1))
              linarith [heFund]
        have houterCoeffLowerLarge :
            (σ : ENNReal) ^ (4 * eFund) ≤ outerFullCoeff := by
          have hle : (σ : ENNReal) ^ (4 * eFund) ≤ outerFullCoeff⁻¹⁻¹ := by
            apply ENNReal.le_inv_iff_mul_le.mpr
            calc
              (σ : ENNReal) ^ (4 * eFund) * outerFullCoeff⁻¹ ≤
                  (σ : ENNReal) ^ (4 * eFund) *
                    (σ : ENNReal) ^ (-(4 * eFund)) := by gcongr
              _ = 1 := by
                rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
                simp
          simpa only [inv_inv] using hle
        have hcScaleLowerLarge :
            (σ : ENNReal) ^ eFund ≤ (cScaleO : ENNReal) := by
          dsimp only [cScaleO]
          rw [ENNReal.coe_inv hScaleNN0Global]
          exact hScaleInvLossLarge
        have hcDenLowerLarge : (σ : ENNReal) ^ eFund ≤ (cDenO : ENNReal) := by
          dsimp only [cDenO]
          rw [ENNReal.coe_inv hDenNN0Global]
          exact hDenInvLossLarge
        have hOuterFundPowerLarge : (σ : ENNReal) ^ (2 * η + 8 * eFund) ≤
            outerFullCoeff *
              ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ^ 2 := by
          calc
            (σ : ENNReal) ^ (2 * η + 8 * eFund) =
                (σ : ENNReal) ^ (4 * eFund) *
                  (((σ : ENNReal) ^ eFund * (σ : ENNReal) ^ eFund *
                    (σ : ENNReal) ^ η) ^ 2) := by
              have hi : (σ : ENNReal) ^ eFund * (σ : ENNReal) ^ eFund *
                    (σ : ENNReal) ^ η = (σ : ENNReal) ^ (η + 2 * eFund) := by
                repeat' rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
                congr 1
                ring
              rw [hi, ← ENNReal.rpow_natCast ((σ : ENNReal) ^ (η + 2 * eFund)) 2,
                ← ENNReal.rpow_mul,
                ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne') ENNReal.coe_ne_top]
              congr 1
              ring
            _ ≤ outerFullCoeff *
                (((cScaleO : ENNReal) * (cDenO : ENNReal) *
                  (σ : ENNReal) ^ η) ^ 2) := by gcongr
        have hOuterFullPowerLarge : (σ : ENNReal) ^ (2 * η + 8 * eFund) ≤
            (ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) : ENNReal) :=
          hOuterFundPowerLarge.trans hOuterFullnessFunded
        have hlargeStrictLarge : a < σ ^ hexp := by
          simpa only [hexp] using lt_of_not_ge hlarge
        have hOuterExpLarge : 2 * η + 8 * eFund ≤ hexp * ηB := by
          linarith [hηLargeB_le, heFundLargeB]
        have hfullOuterLargeE : (a : ENNReal) ^ ηB ≤
            (ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) : ENNReal) := by
          calc
            (a : ENNReal) ^ ηB ≤ (((σ : ENNReal) ^ hexp) ^ ηB) := by
              apply ENNReal.rpow_le_rpow
              · have hc : (a : ENNReal) ≤ ((σ ^ hexp : NNReal) : ENNReal) :=
                  ENNReal.coe_le_coe.mpr hlargeStrictLarge.le
                simpa only [ENNReal.coe_rpow_of_ne_zero hσ.ne'] using hc
              · exact hηB.le
            _ = (σ : ENNReal) ^ (hexp * ηB) := by rw [← ENNReal.rpow_mul]
            _ ≤ (σ : ENNReal) ^ (2 * η + 8 * eFund) :=
              ENNReal.rpow_le_rpow_of_exponent_ge (by
                exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1))
                hOuterExpLarge
            _ ≤ _ := hOuterFullPowerLarge
        have hfullOuterLarge : a ^ ηB ≤
            ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) := by
          exact_mod_cast hfullOuterLargeE
        have hbLarge : bSmall ≤ b := (lt_of_not_ge hbSmallCase).le
        let parentsSelected : Finset κ :=
          t.filter fun k ↦ ∃ i ∈ GS.innerSet, p i = k
        have hρ0 : 0 < ρ := hσ.trans_le hσρ
        have hparentsCard : (parentsSelected.card : ENNReal) ≤
            (CparentTotal₀ : ENNReal) := by
          have hcount := flatPrismOccupiedParents_le hρ0 hρ1 hparent.one_le hbSmall0
            hbLarge hbρ GS.innerSet (fun i ↦ (V i).toTube)
            (fun i hi ↦ hfamily.ball i (hGSinner_sub_s hi)) t Vρ p hparent.pairwise
            (fun i hi ↦ by
              have his : i ∈ s := hGSinner_sub_s hi
              exact ⟨hparent.mapsTo i his, hparent.le_parent_dilate i his⟩)
          simpa only [parentsSelected, CparentTotal₀, CtestTotal₀, bSmall, bSmall₀,
            hdim] using hcount
        have hparSelected : ∀ x ∈ qO, par x ∈ parentsSelected := by
          intro x hx
          have hxW : x ∈ W.outerSet := hqOsub hx
          have hxGS : x ∈ GS.outerSet :=
            ShadedBody.outerThickFamilyAtScale_outerSet_subset GS hσ
              (hdiscG.restrictOuter S.selected) DGS w₁ Q.scale_pos hxW
          obtain ⟨i, hiFib⟩ := hGSfiber x hxGS
          have hiData := (ShadedBody.mem_factorFamily_fiber_iff GS x i).mp hiFib
          have hiGS : i ∈ GS.innerSet := hiData.1
          have hipx : GS.parent i = x := hiData.2
          have hiS : i ∈ s := hGSinner_sub_s hiGS
          have hpblock : flatPrismBlockOf V p hparent.mapsTo Fz' hfamily.nonempty i = x := hipx
          have hfirst := congrArg (fun z : FlatPrismBlock t ↦ z.1.1) hpblock
          have hpi : p i = par x := by
            simpa [flatPrismBlockOf, hiS, par] using hfirst
          exact Finset.mem_filter.mpr ⟨x.1.2, i, hiGS, hpi⟩
        let Uouter : FlatPrismBlock (ι := ι) t →
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
          fun x ↦ (K x).homothety 0 rsh
        have hKTFib : ∀ k ∈ parentsSelected,
            IsKatzTao (qO.filter fun x ↦ par x = k) Uouter 2 := by
          intro k hk
          have hkt : k ∈ t := (Finset.mem_filter.mp hk).1
          let kp : FlatPrismParent t := ⟨k, hkt⟩
          let Kpart : Finset ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
            fun part ↦
              ((part.convexHull_biUnion fun i ↦ (V i).toConvexSpaceBody)
                |>.mapLinearIsometryEquiv f).homothety 0 rsh
          have hKTpart : IsKatzTao (Fz' kp).parts Kpart 2 := by
            exact ((Fz' kp).isKatzTao.mapLinearIsometryEquiv f).homothety 0 hrsh
          apply flatPrismParentFibre_isKatzTao hKTpart
          · intro x hx hxk
            have hxF : x ∈ F.outerSet := hRsub (hSsubR _ (hWsubS (hqOsub hx)))
            have hxpart : x.2 ∈ (Fz' x.1).parts := by
              change x ∈ flatPrismBlocks V p Fz' at hxF
              simpa only [flatPrismBlocks, Finset.mem_sigma, Finset.mem_attach,
                true_and] using hxF
            have hxpar : x.1 = kp := Subtype.ext hxk
            rw [← hxpar]
            exact hxpart
          · intro x hx _hxk
            rfl
        have hDensityRaw : maxDensity qO (fun x ↦ (P x).toConvexSpaceBody) ≤
            (parentsSelected.card : ENNReal) *
              ((flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) * 2) := by
          exact maxDensity_le_of_flatPrismParentwise_envelopes hparSelected hKTFib
            (fun x hx ↦ hScaledKleP x (hqOsub hx))
            (fun x hx ↦ hPscaledVol x (hqOsub hx))
        let ΔLarge : NNReal :=
          CparentTotal₀ * (flatPrismEnvelopeVolumeRatio.C Cw * 2)
        have hDensityLarge : maxDensity qO (fun x ↦ (P x).toConvexSpaceBody) ≤
            (ΔLarge : ENNReal) := by
          calc
            maxDensity qO (fun x ↦ (P x).toConvexSpaceBody) ≤
                (parentsSelected.card : ENNReal) *
                  ((flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) * 2) := hDensityRaw
            _ ≤ (CparentTotal₀ : ENNReal) *
                  ((flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) * 2) := by gcongr
            _ = (ΔLarge : ENNReal) := by
              simp only [ΔLarge, ENNReal.coe_mul]
              norm_num
        have hKangLarge : ∀ δ' : NNReal, 0 < δ' → δ' ≤ 1 →
            ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤
              (Kang : ENNReal) * (δ' : ENNReal) ^ (-((ε' / 2) / 9)) := by
          intro δ' hδ' hδ'1
          calc
            ((ShadedSlab.numAngleWindows δ' : ℕ) : ENNReal) ≤
                (Kang : ENNReal) * (δ' : ENNReal) ^ (-(ε' / 64)) :=
              hKang δ' hδ' hδ'1
            _ ≤ (Kang : ENNReal) * (δ' : ENNReal) ^ (-((ε' / 2) / 9)) := by
              have hδ'E : (δ' : ENNReal) ≤ 1 := by exact_mod_cast hδ'1
              exact mul_le_mul_left'
                (ENNReal.rpow_le_rpow_of_exponent_ge hδ'E (by linarith [hε'])) _
        have hfullOuterLarge' : a ^ ((ε' / 2) / 9) ≤
            ShadedBody.fullness qO (fun j ↦ (P j).toShadedBody) := by
          calc
            a ^ ((ε' / 2) / 9) ≤ a ^ ηB :=
              NNReal.rpow_le_rpow_of_exponent_ge (hσ.trans_le hσa)
                (hab.trans hb1) (by dsimp only [ηB]; linarith [hε'])
            _ ≤ _ := hfullOuterLarge
        have hOuterMultLarge :
            ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) ≤
              ((Cdiv₀ * ΔLarge : NNReal) : ENNReal) *
                (σ : ENNReal) ^ (-(ε' / 6)) := by
          simpa only [Cdiv₀] using
            outerMultiplicityLargeOfMaxDensity hε' hσ hσa (hab.trans hb1) hbSmall0
              hKangLarge qO P hbLarge hqOne hDensityLarge hfullOuterLarge'
        have hsplitCoeffLarge : splitExact ≤
            (σ : ENNReal) ^ (-(ε' / 12)) := by
          calc
            splitExact ≤ (σ : ENNReal) ^ (-(5 * eFund)) := hsplitBound
            _ ≤ (σ : ENNReal) ^ (-(ε' / 12)) :=
              ENNReal.rpow_le_rpow_of_exponent_ge (by
                exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1))
                (by linarith [heFundEps])
        have hsplitLargeF : ShadedBody.multiplicity F.innerSet F.innerBody ≤
            (1 : ENNReal) *
              ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) *
                ((σ : ENNReal) ^ (-(ε' / 6)) *
                  ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                  ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
                  (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                    ((s.card : ENNReal) / (qO.card : ENNReal))) ^
                      (1 - β / 2)) := by
          apply absorbSplitAndRestrictCard hβ1 hσ
            (Finset.card_le_card hqOsub) hsplitCoeffLarge
          simpa only [innerTarget] using hsplitExact
        have hsplitLarge : ShadedBody.multiplicity s
              (fun i ↦ (V i).toShadedBody) ≤
            (1 : ENNReal) *
              ShadedBody.multiplicity qO (fun j ↦ (P j).toShadedBody) *
                ((σ : ENNReal) ^ (-(ε' / 6)) *
                  ((a : ENNReal) / (b : ENNReal)) ^ (1 - β) *
                  ((a : ENNReal)⁻¹ * (σ : ENNReal)) ^ (-2 * β) *
                  (((a : ENNReal) ^ 2)⁻¹ * (σ : ENNReal) ^ 2 *
                    ((s.card : ENNReal) / (qO.card : ENNReal))) ^
                      (1 - β / 2)) := by
          simpa only [F, flatPrismFactorFamily_innerSet,
            flatPrismFactorFamily_innerBody] using hsplitLargeF
        have hfund0Large : (σ : ENNReal) ^ η ≠ 0 := by
          exact (ENNReal.rpow_pos (by exact_mod_cast hσ) ENNReal.coe_ne_top).ne'
        have hfundTopLarge : (σ : ENNReal) ^ η ≠ ⊤ := by
          exact ENNReal.rpow_ne_top_of_ne_zero (ENNReal.coe_ne_zero.mpr hσ.ne')
            ENNReal.coe_ne_top
        have hInvFullFLarge :
            (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹ ≤
              (σ : ENNReal) ^ (-η) := by
          calc
            (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹ ≤
                ((σ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv.mpr hfullOriginalO
            _ = (σ : ENNReal) ^ (-η) := (ENNReal.rpow_neg _ _).symm
        have hcDen0Large : (cDenO : ENNReal) ≠ 0 := by
          dsimp only [cDenO]
          rw [ENNReal.coe_inv hDenNN0Global]
          exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
        have hcDenTopLarge : (cDenO : ENNReal) ≠ ⊤ := by
          dsimp only [cDenO]
          rw [ENNReal.coe_inv hDenNN0Global]
          exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hDenNN0Global)
        have hcScale0Large : (cScaleO : ENNReal) ≠ 0 := by
          dsimp only [cScaleO]
          rw [ENNReal.coe_inv hScaleNN0Global]
          exact ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
        have hcScaleTopLarge : (cScaleO : ENNReal) ≠ ⊤ := by
          dsimp only [cScaleO]
          rw [ENNReal.coe_inv hScaleNN0Global]
          exact ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hScaleNN0Global)
        have hfullGLowerLarge : (cDenO : ENNReal) * (σ : ENNReal) ^ η ≤
            (ShadedBody.fullness G.innerSet G.innerBody : ENNReal) := by
          calc
            (cDenO : ENNReal) * (σ : ENNReal) ^ η ≤
                (cDenO : ENNReal) *
                  (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) := by gcongr
            _ ≤ _ := hRrefO.coe_mul_fullness_le
        have hInvFullGLarge :
            (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹ ≤
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                ENNReal) * (σ : ENNReal) ^ (-η) := by
          calc
            (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹ ≤
                ((cDenO : ENNReal) * (σ : ENNReal) ^ η)⁻¹ :=
              ENNReal.inv_le_inv.mpr hfullGLowerLarge
            _ = (cDenO : ENNReal)⁻¹ * ((σ : ENNReal) ^ η)⁻¹ := by
              rw [ENNReal.mul_inv (Or.inl hcDen0Large) (Or.inl hcDenTopLarge)]
            _ = (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) * (σ : ENNReal) ^ (-η) := by
              dsimp only [cDenO]
              rw [ENNReal.coe_inv hDenNN0Global, inv_inv, ENNReal.rpow_neg]
        have hLrefGlobalLarge : Lcore.refinementConstant =
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁)⁻¹ := by
          simpa only [Lcore, ShadedBody.FactoringAtScaleLossBound.uniform, hdim] using
            ShadedBody.factoringCoreAtScaleUniformRefinementConstant_eq_inv
              3 GS.innerSet.card DGS.exponent w₁
        have hRetainedLowerLarge :
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                DGS.exponent w₁ : ENNReal)⁻¹ *
              ((cScaleO : ENNReal) * (cDenO : ENNReal) * (σ : ENNReal) ^ η) ≤
                retainedOuter := by
          dsimp only [retainedOuter]
          rw [hLrefGlobalLarge, ENNReal.coe_inv hPipeNN0Global]
          gcongr
        have hRetainedInvLarge : retainedOuter⁻¹ ≤
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) *
              (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                ENNReal) * (σ : ENNReal) ^ (-η) := by
          calc
            retainedOuter⁻¹ ≤
                ((ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal)⁻¹ *
                  ((cScaleO : ENNReal) * (cDenO : ENNReal) *
                    (σ : ENNReal) ^ η))⁻¹ := ENNReal.inv_le_inv.mpr hRetainedLowerLarge
            _ = (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) * (σ : ENNReal) ^ (-η) := by
              have hrestInv :
                  ((cScaleO : ENNReal) * (cDenO : ENNReal) *
                    (σ : ENNReal) ^ η)⁻¹ =
                    (cScaleO : ENNReal)⁻¹ * (cDenO : ENNReal)⁻¹ *
                      ((σ : ENNReal) ^ η)⁻¹ := by
                rw [ENNReal.mul_inv
                  (Or.inl (mul_ne_zero hcScale0Large hcDen0Large))
                  (Or.inl (ENNReal.mul_ne_top hcScaleTopLarge hcDenTopLarge))]
                rw [ENNReal.mul_inv (Or.inl hcScale0Large) (Or.inl hcScaleTopLarge)]
              rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top))
                (Or.inl (ENNReal.inv_ne_top.mpr
                  (ENNReal.coe_ne_zero.mpr hPipeNN0Global)))]
              rw [hrestInv]
              dsimp only [cScaleO, cDenO]
              rw [ENNReal.coe_inv hScaleNN0Global, ENNReal.coe_inv hDenNN0Global]
              rw [inv_inv, inv_inv, inv_inv, ENNReal.rpow_neg]
              ring
        have hCretainBoundLarge : Cretain ≤
            4 * (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) *
              (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
              (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                ENNReal) * (σ : ENNReal) ^ (-η) := by
          dsimp only [Cretain]
          calc
            4 * retainedOuter⁻¹ ≤ 4 *
                ((ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                    DGS.exponent w₁ : ENNReal) *
                  (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                  (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                    ENNReal) * (σ : ENNReal) ^ (-η)) :=
              mul_le_mul_left' hRetainedInvLarge 4
            _ = 4 *
                (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) * (σ : ENNReal) ^ (-η) := by ring
        let CF : ENNReal := frostmanConstIn s
          (fun i ↦ (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        let outerFrostCoeffLarge : ENNReal :=
          (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
            (2 * (CF *
              ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) *
                (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹) *
              ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹)) *
              Cretain * (volume plankWindow.carrier / volume scaledBall.carrier)) *
            (dO + 1 : ENNReal)
        have hOuterFrostmanQLarge : IsFrostmanIn qO
            (fun j ↦ (P j).toConvexSpaceBody) plankWindow outerFrostCoeffLarge := by
          convert hOuterFrostmanQ using 1 <;>
            dsimp only [outerFrostCoeffLarge, CF, scaledBall] <;> push_cast <;> ring
        have hfixedFrostLarge_le : fixedFrost₀ ≤ partAFixedEnvelope :=
          ((le_max_left _ _).trans <| (le_max_right _ _).trans <|
            (le_max_right _ _)).trans hpartAFixedBase_le
        have hfixedFrostLargeBound : fixedFrost₀ ≤ (σ : ENNReal) ^ (-eFund) :=
          hfixedFrostLarge_le.trans hPartAFixed.2.2
        have hscaledBallEqLarge : scaledBall = scaledBall₀ := by
          dsimp only [scaledBall, scaledBall₀]
        have hσnegPowThreeLarge : ((σ : ENNReal) ^ (-η)) ^ (3 : ℕ) =
            (σ : ENNReal) ^ (-3 * η) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1
          ring
        have hOuterFrostRawLarge : outerFrostCoeffLarge ≤ fixedFrost₀ * CF *
            (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
              ENNReal) ^ 3 *
            (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) ^ 2 *
            (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
              DGS.exponent w₁ : ENNReal) * (σ : ENNReal) ^ (-3 * η) := by
          dsimp only [outerFrostCoeffLarge]
          calc
            (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
                  (2 * (CF *
                    ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) *
                      (ShadedBody.fullness F.innerSet F.innerBody : ENNReal)⁻¹) *
                    ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                      (ShadedBody.fullness G.innerSet G.innerBody : ENNReal)⁻¹)) *
                    Cretain *
                      (volume plankWindow.carrier / volume scaledBall.carrier)) *
                  (dO + 1 : ENNReal) ≤
                (flatPrismEnvelopeVolumeRatio.C Cw : ENNReal) *
                  (2 * (CF *
                    ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) * (σ : ENNReal) ^ (-η)) *
                    ((ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                      ((ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) * (σ : ENNReal) ^ (-η)))) *
                    (4 *
                      (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                        DGS.exponent w₁ : ENNReal) *
                      (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) *
                      (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                        ENNReal) * (σ : ENNReal) ^ (-η)) *
                    (volume plankWindow.carrier / volume scaledBall.carrier)) *
                  (dO + 1 : ENNReal) := by gcongr
            _ = fixedFrost₀ * CF *
                (ShadedBody.outerDensitySelectionConstant F.innerSet.card D.exponent :
                  ENNReal) ^ 3 *
                (ShadedBody.outerScaleSelectionConstant σ (2 * Dpar) : ENNReal) ^ 2 *
                (ShadedBody.factoringCoreAtScaleUniformPipelineLoss 3 GS.innerSet.card
                  DGS.exponent w₁ : ENNReal) * (σ : ENNReal) ^ (-3 * η) := by
              rw [hscaledBallEqLarge, hdOeq]
              dsimp only [fixedFrost₀]
              ring_nf
              rw [hσnegPowThreeLarge]
              rw [show -(η * 3) = -3 * η by ring]
              ring
        have hOuterFrostPowerLarge : outerFrostCoeffLarge ≤
            (σ : ENNReal) ^ (-(3 * η + 7 * eFund)) * CF := by
          exact hOuterFrostRawLarge.trans <|
            ShadedBody.outerFrostman_loss_bound
              (ENNReal.coe_ne_zero.mpr hσ.ne') ENNReal.coe_ne_top
              hfixedFrostLargeBound hDensityLossGlobal hScaleLossGlobal hPipelineLossGlobal
        let CsplitLarge : NNReal := σ ^ (-(ε' / 16))
        have hFrostExpLarge : 3 * η + 7 * eFund ≤ ε' / 16 := by
          linarith [hηEps_le, heFundEps]
        have hOuterFrostCoeffSplitLarge : outerFrostCoeffLarge ≤
            (CsplitLarge : ENNReal) * CF := by
          calc
            outerFrostCoeffLarge ≤ (σ : ENNReal) ^ (-(3 * η + 7 * eFund)) * CF :=
              hOuterFrostPowerLarge
            _ ≤ (σ : ENNReal) ^ (-(ε' / 16)) * CF := by
              apply mul_le_mul_right'
              exact ENNReal.rpow_le_rpow_of_exponent_ge (by
                have hcoe := ENNReal.coe_le_coe.mpr hNormLoss.2.1
                simpa only [ENNReal.coe_one] using hcoe) (neg_le_neg hFrostExpLarge)
            _ = (CsplitLarge : ENNReal) * CF := by
              dsimp only [CsplitLarge]
              rw [ENNReal.coe_rpow_of_ne_zero hσ.ne']
        have hOuterFrostmanSplitLarge : IsFrostmanIn qO
            (fun j ↦ (P j).toConvexSpaceBody) plankWindow
              ((CsplitLarge : ENNReal) * CF) :=
          hOuterFrostmanQLarge.mono hOuterFrostCoeffSplitLarge
        have hCsplitLarge1 : 1 ≤ CsplitLarge := by
          dsimp only [CsplitLarge]
          have hneg : -(ε' / 16) ≤ 0 :=
            neg_nonpos.mpr (div_nonneg hε'.le (by norm_num))
          exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
            (x := σ) (z := -(ε' / 16)) hσ hNormLoss.2.1 hneg
        have hCF1Large : 1 ≤ CF := by
          apply one_le_frostmanConstIn
          rw [Kakeya.densityIn_pos_iff]
          obtain ⟨i, hi⟩ := hfamily.nonempty
          refine ⟨i, hi, ?_, hfamily.ball i hi⟩
          simpa only [F, flatPrismFactorFamily_innerSet,
            flatPrismFactorFamily_innerBody] using hVpos i hi
        by_cases hCFtopLarge : CF = ⊤
        · dsimp only [CF] at hCFtopLarge
          rw [hCFtopLarge]
          have hhalf : β / 2 ≤ (1 : ℝ) / 2 :=
            div_le_div_of_nonneg_right hβ1 (by norm_num)
          have hpPos : 0 < 1 - β / 2 :=
            (by norm_num : 0 < 1 - (1 : ℝ) / 2).trans_le
              (sub_le_sub_left hhalf 1)
          rw [ENNReal.top_rpow_of_pos hpPos]
          have haPos : 0 < a := hσ.trans_le hσa
          have hbPos : 0 < b := haPos.trans_le hab
          have hσLoss0 : (σ : ENNReal) ^ (-ε') ≠ 0 :=
            (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hσ) ENNReal.coe_ne_top).ne'
          have hratioPos : 0 < (a : ENNReal) / (b : ENNReal) :=
            ENNReal.div_pos (ENNReal.coe_ne_zero.mpr haPos.ne') ENNReal.coe_ne_top
          have hratioTop : (a : ENNReal) / (b : ENNReal) ≠ ⊤ :=
            ENNReal.div_ne_top ENNReal.coe_ne_top (ENNReal.coe_ne_zero.mpr hbPos.ne')
          have hratioPow0 : ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2) ≠ 0 :=
            (ENNReal.rpow_pos hratioPos hratioTop).ne'
          have hσBetaPow0 : (σ : ENNReal) ^ (-2 * β) ≠ 0 :=
            (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hσ) ENNReal.coe_ne_top).ne'
          have hcard0 : (s.card : ENNReal) ≠ 0 := by
            exact_mod_cast hfamily.nonempty.card_ne_zero
          have hcardBasePos : 0 < (s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ) :=
            ENNReal.mul_pos hcard0 (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hσ.ne'))
          have hcardPow0 :
              ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^ (1 - β / 2) ≠ 0 :=
            (ENNReal.rpow_pos hcardBasePos (by finiteness)).ne'
          rw [ENNReal.mul_top hσLoss0, ENNReal.top_mul hratioPow0,
            ENNReal.top_mul hσBetaPow0, ENNReal.top_mul hcardPow0]
          exact le_top
        · have hmassLarge : (Cm : ENNReal) ≤ ((CsplitLarge : ENNReal) * CF) *
              ((qO.card : ENNReal) * (a : ENNReal)) := by
            have hm := hmassWindow P (hσ.trans_le hσa) hqOne
              (fun j hj ↦ hPwindow j (hqOsub hj))
              (CF := (CsplitLarge : ENNReal) * CF) (by
                simpa only [ENNReal.coe_one, one_mul] using hOuterFrostmanSplitLarge)
            exact hm
          have hCfinalLargeBound : (CfinalLarge₀ : ENNReal) ≤
              (σ : ENNReal) ^ (-eFund) := by
            exact (le_max_right partAFixedBase (CfinalLarge₀ : ENNReal)).trans
              hPartAFixed.2.2
          have hfixedEq :
              (((Cdiv₀ * ΔLarge) * Cm⁻¹ ^ (1 - β / 2) *
                max 1 (bSmall ^ (5 * β / 2 - 1)) : NNReal) : ENNReal) =
                (CfinalLarge₀ : ENNReal) := by
            congr 1
          have hpLarge : 0 ≤ 1 - β / 2 := by linarith
          have hpLargeLe : 1 - β / 2 ≤ 1 := by linarith
          have hCsplitLargePow : (CsplitLarge : ENNReal) ^ (1 - β / 2) ≤
              (σ : ENNReal) ^ (-(ε' / 16)) := by
            calc
              (CsplitLarge : ENNReal) ^ (1 - β / 2) =
                  (σ : ENNReal) ^ (-(ε' / 16) * (1 - β / 2)) := by
                dsimp only [CsplitLarge]
                rw [ENNReal.coe_rpow_of_ne_zero hσ.ne', ← ENNReal.rpow_mul]
              _ ≤ (σ : ENNReal) ^ (-(ε' / 16)) :=
                ENNReal.rpow_le_rpow_of_exponent_ge (by
                  exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1)) (by
                    nlinarith [hβ0, hε'])
          have habsorbLarge :
              ((((Cdiv₀ * ΔLarge) * Cm⁻¹ ^ (1 - β / 2) *
                    max 1 (bSmall ^ (5 * β / 2 - 1)) : NNReal) : ENNReal) *
                  (CsplitLarge : ENNReal) ^ (1 - β / 2)) ≤
                (σ : ENNReal) ^ (-(ε' / 2)) := by
            rw [hfixedEq]
            calc
              (CfinalLarge₀ : ENNReal) *
                    (CsplitLarge : ENNReal) ^ (1 - β / 2) ≤
                  (σ : ENNReal) ^ (-eFund) *
                    (σ : ENNReal) ^ (-(ε' / 16)) := by gcongr
              _ = (σ : ENNReal) ^ (-(eFund + ε' / 16)) := by
                rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hσ.ne')
                  ENNReal.coe_ne_top]
                congr 1
                ring
              _ ≤ (σ : ENNReal) ^ (-(ε' / 2)) :=
                ENNReal.rpow_le_rpow_of_exponent_ge (by
                  exact_mod_cast hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1)) (by
                    linarith [heFundEps])
          have hfinalLarge := combineLargeAndAbsorb hβpos hβ1 hε' hσ
            (hσrange.2.le.trans (by norm_num : (1 / 2 : NNReal) ≤ 1))
            (hσ.trans_le hσa) hab hb1 hbSmall0 hbLarge hCm hCsplitLarge1
            hCF1Large hCFtopLarge hqOcard0 hfamily.nonempty.card_ne_zero hmassLarge
            hOuterMultLarge hsplitLarge habsorbLarge
          simpa only [CF, mul_comm ((σ : ENNReal) ^ 2) (s.card : ENNReal)] using hfinalLarge

/-- **GWZ Proposition 6.6(A) in ship's scale ordering, with the coarse family assumed essentially
distinct.**

This is exactly `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` — same conclusion, same
`Kakeya.IsFlatPrismFamily`, same factorization hypothesis, same ordering `σ ≤ a ≤ b ≤ ρ ≤ 1`,
same conclusion — **plus one hypothesis**: the coarse `ρ`-tubes indexed by `t` are pairwise
essentially distinct.

It is proved, from `Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` at
parent dilation `D = 1`.  Its purpose is to pin down, mechanically, the *only* gap between the
harvested proof and this development's open statement of 6.6(A): everything else in that statement
is discharged, and `hED` is what remains.  Whether `hED` may be added to
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` is a fidelity question about GWZ's hypotheses
on the coarse family `𝕋_ρ`, and is left to a human; no statement has been weakened here. -/
theorem multiplicity_le_of_factorsThroughFlatPrisms_of_coarseEssDistinct
    (hdim : Module.finrank ℝ E = 3)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKKT : KatzTaoEstimate.{u} E β) (hKF : FrostmanEstimate.{u} E β)
    (Cw : NNReal) (hCw : 1 ≤ Cw) :
    ∀ ε' > (0 : ℝ), ∃ η' > (0 : ℝ),
    ∀ᶠ (σ : NNReal) in 𝓝[>] 0, ∀ Cunif : NNReal, 1 ≤ Cunif →
      (Cunif : ENNReal) ≤ (σ : ENNReal) ^ (-η') →
      ∀ a b ρ : NNReal, σ ≤ a → a ≤ b → b ≤ ρ → ρ ≤ 1 →
      ∀ {ι κ : Type u} [DecidableEq ι] [DecidableEq κ] {s : Finset ι} {t : Finset κ}
        (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ),
        IsFlatPrismFamily η' Cunif s V →
        (∀ i ∈ s, p i ∈ t) →
        (∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Vρ (p i)).toConvexSpaceBody) →
        (t : Set κ).Pairwise
          (fun k l => IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier) →
        (∀ k ∈ t, ∃ F : ConvexSpaceBody.Factorization (s.filter fun i => p i = k)
              (fun i => (V i).toConvexSpaceBody) 2,
            IsPlankFamilyOfDimensions Cw a b F.parts
              (fun part => part.convexHull_biUnion (fun i => (V i).toConvexSpaceBody))) →
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ (σ : ENNReal) ^ (-ε')
            * (frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
                ConvexSpaceBody.closedUnitBall) ^ (1 - β / 2)
            * ((a : ENNReal) / (b : ENNReal)) ^ (3 * β / 2)
            * (σ : ENNReal) ^ (-2 * β)
            * ((s.card : ENNReal) * (σ : ENNReal) ^ (2 : ℕ)) ^ (1 - β / 2) := by
  intro ε' hε'
  obtain ⟨η, hη, hev⟩ :=
    multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation hdim hβ0 hβ1 hKKT hKF Cw hCw
      1 ε' hε'
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with σ hbound
  intro Cunif hCunif hCunifσ a b ρ hσa hab hbρ hρ1 ι κ _ _ s t V Vρ p hfamily hp hle hED hFz
  refine hbound Cunif hCunif hCunifσ a b ρ hσa hab (hbρ.trans hρ1)
    (hσa.trans (hab.trans hbρ)) (by simpa using hbρ) hρ1 V Vρ p hfamily ?_ hFz
  exact
    { one_le := le_rfl
      mapsTo := hp
      le_parent_dilate := fun i hi => by
        refine le_trans (hle i hi) ?_
        intro x hx
        exact Tube.subset_dilate (Vρ (p i)) (le_refl (1 : ℝ)) hx
      pairwise := hED }

/-! ### Declarations retained from `kakeya/ship`

`wjq/lem5.1-section8-integration` deleted the two constant-weakening helpers below and restated
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'` with extra hypotheses.  Both ship
declarations are retained verbatim: the helpers because ship consumers use them, and the
proposition because it is this development's protected statement of GWZ Proposition 6.6(A) and
must not be weakened to accept a branch proof.  See the port note on
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms_of_parentPresentation` above for exactly which
hypothesis separates the two.
-/

/-- Weakening the constant, at the tube level.  The node data and the branching function are
unchanged; `boundedOverlap` bounds a cardinality by `C` directly and `card_class_le` by
`C * branchingN k`.  This is `Tube.UniformTubeSet.mono` minus the deleted lower bracket. -/
def IsFlatPrismUniformTubeSet.mono {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C C' : NNReal} (𝒰 : IsFlatPrismUniformTubeSet s T N C) (hC : C ≤ C') :
    IsFlatPrismUniformTubeSet s T N C' where
  cover := 𝒰.cover
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap k hk V := (𝒰.boundedOverlap k hk V).trans hC
  card_class_le k hk j hj := (𝒰.card_class_le k hk j hj).trans (mul_le_mul_left hC _)

/-- **Weakening the constant.**  The hierarchy and both counting functions are unchanged; the two
retained clauses are upper bounds with `C` on the right, so each composes with `hC`.  This is
`ShadedTube.ShadedUniformTubeSet.mono` minus the two deleted lower brackets, and it is what a
consumer that fixes its uniformity constant before the family arrives needs. -/
def IsFlatPrismUniform.mono {ι : Type*} {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C C' : NNReal} (𝒱 : IsFlatPrismUniform s V N C)
    (hC : C ≤ C') : IsFlatPrismUniform s V N C' where
  tubeUniform := 𝒱.tubeUniform.mono hC
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le x hx k hk i hi hxi :=
    (𝒱.card_shadeClass_le x hx k hk i hi hxi).trans (mul_le_mul_left hC _)
  le_branchingN x hx k hk :=
    (𝒱.le_branchingN x hx k hk).trans (mul_le_mul_left hC _)



end FlatPrisms

end Kakeya
