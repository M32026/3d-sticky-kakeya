/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.FlatPrisms
public import Kakeya.Thickness.Lemmas
public import Kakeya.Tube.IntersectionVolume

/-!
# Main Lemma 1, Case (ii): the tube attached to a plank

This file collects the geometric and volume-theoretic obligations that
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` (blueprint
`lem:ml1bootPlankInTubeRepaired`, in `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`) is
assembled from, so that the lemma itself becomes a short assembly.  It formalizes the group of
auxiliary statements of `GWZAdapted/section8_endgame.tex`:

* `Kakeya.ml1Boot.volume_bounds_of_ethickness_bounds` (blueprint
  `lem:volumeFromEthicknessBounds`) — the two-sided volume estimate in `ℝ³`, packaged once so
  that the two volume computations below become a matter of supplying six numbers;
* `Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions` (blueprint `lem:ml1bootPlankVolume`)
  and `Kakeya.ml1Boot.volume_bounds_of_tube` (blueprint `lem:ml1bootTubeVolumeScale`) — the
  volumes of a plank and of a tube of moderate scale;
* `Kakeya.ml1Boot.tube_ethickness_bounds` (blueprint `lem:tubeEthicknesses`) — the
  ethicknesses of a tube, the four separate bounds of `Tube` glued by
  `Metric.ethickness_antitone` into the identity `τₖ(T) = δ` for `1 ≤ k ≤ n - 1`;
* `Kakeya.ml1Boot.unitCoreSegment` (blueprint `lem:unitCoreSegment`),
  `Kakeya.ml1Boot.dist_prism_transverse_le` (blueprint `lem:prismTransverseDist`) and
  `Kakeya.ml1Boot.prism_subset_unitCoreTube` (blueprint `lem:prismUnitCoreTube`) — the purely
  geometric fact that a rectangular prism whose first half-width is at most `Λ₀` lies in the
  `(2 Λ₀)`-dilate of a tube whose core is the unit segment through its centre along its long axis;
* `Kakeya.ml1Boot.plankTube` (blueprint `def:ml1bootPlankTube`) and
  `Kakeya.ml1Boot.subset_plankTube` (blueprint `lem:ml1bootPlankTubeContainment`) — that tube,
  of scale `C b`, attached to a nonempty compact set through its outer prism, and the
  containment of the set in its `(2 Λ₀)`-dilate;
* `Kakeya.ml1Boot.plankInTube_constant_bounds` (blueprint
  `lem:ml1bootPlankInTubeConstantBounds`) — the arithmetic of the constants.

## The comparability constant is a parameter

The blueprint writes `C_𝕎 = C_{lem:ml1bootPlankPigeonhole}` throughout this group, i.e.
`Kakeya.ml1Boot.plankPigeonhole.C`, which is defined downstream in
`Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.  Here the constant is carried as an explicit
parameter `C : NNReal`, which is a strict generalization: instantiating `C := plankPigeonhole.C`
returns the blueprint statements verbatim, `plankPigeonhole.C` being a reducible abbreviation.
The same applies to `Kakeya.ml1Boot.plankInTube_constant_bounds`, whose right-hand side is the
unfolding of `Kakeya.ml1Boot.plankInTube.C`.

## Ethicknesses versus affine thicknesses

Every statement here is phrased in the ethicknesses `Metric.ethickness ℝ · k` except
`Kakeya.ml1Boot.subset_plankTube`, which reads off the half-widths of an outer prism and is
therefore phrased in the affine thicknesses `Metric.thickness ℝ · k`; the two agree on bounded
sets by `Metric.ethickness_thickness`, which is where that identification is discharged.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Metric

namespace Kakeya

namespace ml1Boot

/-! ### The two-sided volume estimate in `ℝ³` -/

section Volume

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Two-sided volume bounds from ethickness bounds in `ℝ³`** (blueprint
`lem:volumeFromEthicknessBounds`).

If the three ethicknesses of a convex body `V ⊆ ℝ³` are sandwiched between `lₖ` and `uₖ`, then
`c₃ l₀ l₁ l₂ ≤ |V| ≤ 8 u₀ u₁ u₂`, where `c₃ = Metric.lt_volume_convexHull.c 3`.

The lower half is `Convex.ethickness_prod_le_volume` and the upper half is
`Metric.volume_le_prod_ethickness`, in each case after expanding
`∏ k ∈ Finset.range 3, Metric.ethickness ℝ V.carrier k` and pushing the three monotonicity
steps through the triple product.  That work is done once here, because
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions` and
`Kakeya.ml1Boot.volume_bounds_of_tube` are the same computation with different data. -/
theorem volume_bounds_of_ethickness_bounds (hdim : Module.finrank ℝ E = 3)
    (V : ConvexSpaceBody E) {l₀ l₁ l₂ u₀ u₁ u₂ : ENNReal}
    (hl₀ : l₀ ≤ ethickness ℝ V.carrier 0) (hl₁ : l₁ ≤ ethickness ℝ V.carrier 1)
    (hl₂ : l₂ ≤ ethickness ℝ V.carrier 2) (hu₀ : ethickness ℝ V.carrier 0 ≤ u₀)
    (hu₁ : ethickness ℝ V.carrier 1 ≤ u₁) (hu₂ : ethickness ℝ V.carrier 2 ≤ u₂) :
    (lt_volume_convexHull.c 3 : ENNReal) * (l₀ * l₁ * l₂) ≤ volume V.carrier ∧
      volume V.carrier ≤ 8 * (u₀ * u₁ * u₂) := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hprod : ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V.carrier i =
      ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2 := by
    rw [hdim]
    simp [Finset.prod_range_succ]
  have hVconvex : Convex ℝ V.carrier := V.convex'.convex
  constructor
  · calc
      (lt_volume_convexHull.c 3 : ENNReal) * (l₀ * l₁ * l₂)
          ≤ (lt_volume_convexHull.c 3 : ENNReal) *
              (ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2) :=
            mul_le_mul' (le_refl _) (mul_le_mul' (mul_le_mul' hl₀ hl₁) hl₂)
      _ = (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
          (ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2) := by
            rw [hdim]
      _ = (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V.carrier i := by rw [← hprod]
      _ ≤ volume V.carrier := hVconvex.ethickness_prod_le_volume
  · calc
      volume V.carrier
          ≤ 2 ^ (Module.finrank ℝ E) *
              ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ V.carrier i :=
            volume_le_prod_ethickness _
      _ = (8 : ENNReal) *
          (ethickness ℝ V.carrier 0 * ethickness ℝ V.carrier 1 * ethickness ℝ V.carrier 2) := by
        rw [hprod, hdim]
        norm_num
      _ ≤ 8 * (u₀ * u₁ * u₂) :=
        mul_le_mul' (le_refl _) (mul_le_mul' (mul_le_mul' hu₀ hu₁) hu₂)

/-- **The volume of a plank** (blueprint `lem:ml1bootPlankVolume`).

An `a × b × 1` plank in `ℝ³` with comparability constant `C` — that is, a convex body `W` with
`C⁻¹ ≤ τ₀(W) ≤ C`, `C⁻¹ b ≤ τ₁(W) ≤ C b` and `C⁻¹ a ≤ τ₂(W) ≤ C a`, which is
`Kakeya.IsPlankOfDimensions C a b W` — has volume comparable to `a b`:
`C⁻³ c₃ a b ≤ |W| ≤ 8 C³ a b`.

Immediate from `Kakeya.ml1Boot.volume_bounds_of_ethickness_bounds` with
`(l₀, l₁, l₂) = (C⁻¹, C⁻¹ b, C⁻¹ a)` and `(u₀, u₁, u₂) = (C, C b, C a)`, the six hypotheses
being exactly the six inequalities of the plank predicate.  Neither `a ≤ b` nor `b ≤ 1` enters.
In the intended application `C = Kakeya.ml1Boot.plankPigeonhole.C`.

The bounds are **not** the same as item `item:plankVolume` of
`Kakeya.ml1Boot.exists_plankDimensions`, which asserts `C⁻¹ a b ≤ |W| ≤ C a b`; neither implies
the other, both failing by a factor of order `C²`.  See blueprint
`note:plankVolumeConstantGap`. -/
theorem volume_bounds_of_isPlankOfDimensions (hdim : Module.finrank ℝ E = 3) {C a b : NNReal}
    (_hC : 1 ≤ C) {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W) :
    ((C : ENNReal) ^ 3)⁻¹ * (lt_volume_convexHull.c 3 : ENNReal) * ((a : ENNReal) * b)
        ≤ volume W.carrier ∧
      volume W.carrier ≤ 8 * (C : ENNReal) ^ 3 * ((a : ENNReal) * b) := by
  obtain ⟨⟨h0l, h0u⟩, ⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩ := hW
  have h := volume_bounds_of_ethickness_bounds hdim W
    (l₀ := (C : ENNReal)⁻¹)
    (l₁ := (C : ENNReal)⁻¹ * (b : ENNReal))
    (l₂ := (C : ENNReal)⁻¹ * (a : ENNReal))
    (u₀ := (C : ENNReal))
    (u₁ := (C : ENNReal) * (b : ENNReal))
    (u₂ := (C : ENNReal) * (a : ENNReal))
    h0l h1l h2l h0u h1u h2u
  obtain ⟨hL, hU⟩ := h
  have hEqL : ((C : ENNReal) ^ 3)⁻¹ * (lt_volume_convexHull.c 3 : ENNReal) * ((a : ENNReal) * b) =
      (lt_volume_convexHull.c 3 : ENNReal) *
        (((C : ENNReal)⁻¹) * (((C : ENNReal)⁻¹) * (b : ENNReal)) *
          (((C : ENNReal)⁻¹) * (a : ENNReal))) := by
    rw [ENNReal.inv_pow]
    ring
  have hEqU : 8 * ((C : ENNReal) * ((C : ENNReal) * (b : ENNReal)) *
        ((C : ENNReal) * (a : ENNReal))) =
      8 * (C : ENNReal) ^ 3 * ((a : ENNReal) * b) := by
    ring
  constructor
  · exact le_trans (le_of_eq hEqL) hL
  · exact le_trans hU (le_of_eq hEqU)

end Volume

/-! ### The ethicknesses and the volume of a tube -/

section Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Ethicknesses of a tube** (blueprint `lem:tubeEthicknesses`).

An `s`-tube in a space of dimension at least `2` — the closed `s`-neighbourhood of a segment
whose endpoints are at distance exactly `1` — has `1 / 2 ≤ τ₀(T) ≤ 1 + s` and `τₖ(T) = s` for
every `1 ≤ k ≤ n - 1`.

The four bounds are `Tube.le_ethickness_zero`, `Tube.ethickness_zero_le`,
`Tube.ethickness_one_le` and `Tube.le_ethickness_finrank_sub_one`; the *identity* is none of
them, being obtained by gluing the last two with the antitonicity `Metric.ethickness_antitone`
of `ethickness` in its rank:
`s ≤ τ_{n-1}(T) ≤ τₖ(T) ≤ τ₁(T) ≤ s`.

The upper bound `1 + s` on `τ₀` is deliberately *not* weakened to `2`: the tube scales occurring
in `Kakeya.ml1Boot.subset_plankTube` are of the form `C b` with `C ≥ 1024`, so the usual bound
`Tube.ethickness_zero_le_two`, which needs `s ≤ 1`, is unusable there. -/
theorem tube_ethickness_bounds (hn : 2 ≤ Module.finrank ℝ E) {s : NNReal} (T : Tube s E) :
    1 / 2 ≤ ethickness ℝ T.carrier 0 ∧ ethickness ℝ T.carrier 0 ≤ 1 + (s : ENNReal) ∧
      ∀ k, 1 ≤ k → k ≤ Module.finrank ℝ E - 1 → ethickness ℝ T.carrier k = (s : ENNReal) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le zero_lt_two hn)
  constructor
  · exact T.le_ethickness_zero
  constructor
  · exact T.ethickness_zero_le
  · intro k hk1 hkfin
    apply le_antisymm
    · exact (ethickness_antitone hk1).trans T.ethickness_one_le
    · exact T.le_ethickness_finrank_sub_one.trans (ethickness_antitone hkfin)

/-- **The volume of a tube of moderate scale** (blueprint `lem:ml1bootTubeVolumeScale`).

For `0 < s ≤ 2 C` with `1 ≤ C`, an `s`-tube in `ℝ³` has `2⁻¹ c₃ s² ≤ |T| ≤ 40 C s²`.

`Kakeya.ml1Boot.tube_ethickness_bounds` supplies `1 / 2 ≤ τ₀(T) ≤ 1 + s ≤ 1 + 2 C ≤ 5 C` and
`τ₁(T) = τ₂(T) = s`; feeding `(l₀, l₁, l₂) = (1 / 2, s, s)` and `(u₀, u₁, u₂) = (5 C, s, s)`
into `Kakeya.ml1Boot.volume_bounds_of_ethickness_bounds` gives the two bounds.

The hypothesis `s ≤ 2 C` is exactly what keeps `τ₀(T)` bounded, and it is the only role it
plays.  In the intended application `s = C b` with `C = Kakeya.ml1Boot.plankPigeonhole.C` and
`b ≤ 1`, which is emphatically *not* at most `1`, so `Tube.volume_le` — which assumes the tube
scale is at most `1` — cannot be used. -/
theorem volume_bounds_of_tube (hdim : Module.finrank ℝ E = 3) {C s : NNReal} (hC : 1 ≤ C)
    (_hs0 : 0 < s) (hs : s ≤ 2 * C) (T : Tube s E) :
    (2 : ENNReal)⁻¹ * (lt_volume_convexHull.c 3 : ENNReal) * (s : ENNReal) ^ 2
        ≤ volume T.carrier ∧
      volume T.carrier ≤ 40 * (C : ENNReal) * (s : ENNReal) ^ 2 := by
  have hn : 2 ≤ Module.finrank ℝ E := by
    rw [hdim]
    norm_num
  have hbounds := tube_ethickness_bounds hn T
  rcases hbounds with ⟨hτ₀_lo, hτ₀_hi, hτ⟩
  have hτ₁ : ethickness ℝ T.carrier 1 = (s : ENNReal) :=
    hτ 1 (by norm_num) (by
      omega)
  have hτ₂ : ethickness ℝ T.carrier 2 = (s : ENNReal) :=
    hτ 2 (by norm_num) (by
      omega)
  -- weaken the upper bound on τ₀
  have hu₀ : ethickness ℝ T.carrier 0 ≤ (5 : ENNReal) * (C : ENNReal) := by
    have hsEN : (s : ENNReal) ≤ ((2 * C : NNReal) : ENNReal) := by exact_mod_cast hs
    have hCEN : (1 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC
    calc
      ethickness ℝ T.carrier 0 ≤ 1 + (s : ENNReal) := hτ₀_hi
      _ ≤ 1 + ((2 * C : NNReal) : ENNReal) := by
        gcongr
      _ = (1 : ENNReal) + (2 : ENNReal) * (C : ENNReal) := by push_cast; ring
      _ ≤ (C : ENNReal) + (2 : ENNReal) * (C : ENNReal) := by
        gcongr
      _ = (3 : ENNReal) * (C : ENNReal) := by ring
      _ ≤ (5 : ENNReal) * (C : ENNReal) := by
        gcongr
        norm_num
  have hl₀ : (2 : ENNReal)⁻¹ ≤ ethickness ℝ T.carrier 0 := by
    simpa [one_div] using hτ₀_lo
  have hl₁ : (s : ENNReal) ≤ ethickness ℝ T.carrier 1 := le_of_eq hτ₁.symm
  have hl₂ : (s : ENNReal) ≤ ethickness ℝ T.carrier 2 := le_of_eq hτ₂.symm
  have hu₁ : ethickness ℝ T.carrier 1 ≤ (s : ENNReal) := le_of_eq hτ₁
  have hu₂ : ethickness ℝ T.carrier 2 ≤ (s : ENNReal) := le_of_eq hτ₂
  have hvols := volume_bounds_of_ethickness_bounds hdim T.toConvexSpaceBody hl₀ hl₁ hl₂ hu₀ hu₁ hu₂
  rcases hvols with ⟨hvol_lo, hvol_hi⟩
  constructor
  · rw [show (2 : ENNReal)⁻¹ * (lt_volume_convexHull.c 3 : ENNReal) * (s : ENNReal) ^ 2 =
      (lt_volume_convexHull.c 3 : ENNReal) *
        ((2 : ENNReal)⁻¹ * (s : ENNReal) * (s : ENNReal)) by ring]
    exact hvol_lo
  · have h_mid : 8 * (((5 : ENNReal) * (C : ENNReal)) * (s : ENNReal) * (s : ENNReal)) =
        40 * (C : ENNReal) * (s : ENNReal) ^ 2 := by ring
    exact hvol_hi.trans h_mid.le

/-- **The volume of the `2`-dilate of a tube of moderate scale** (blueprint
`lem:ml1bootDilateTubeVolumeScale`).

For `0 < s ≤ 2 C` with `1 ≤ C`, the `2`-dilate `2 · T` of an `s`-tube in `ℝ³` — the image of
`T` under the homothety of ratio `2` about its centre, `Kakeya.Tube.dilate T 2` — satisfies
`4 c₃ s² ≤ |2 · T| ≤ 320 C s²`.

`Kakeya.Tube.tubeDilateVolume` at `C = 2 > 1` and `n = 3` gives `|2 · T| = 8 |T|`; multiplying
the two bounds `2⁻¹ c₃ s² ≤ |T| ≤ 40 C s²` of `Kakeya.ml1Boot.volume_bounds_of_tube` by `8`
gives the claim.  The dilation changes only the numerical constants, so `|2 · T|` remains
comparable to `s²`; in the intended application `C = Kakeya.ml1Boot.plankPigeonhole.C`. -/
theorem volume_bounds_of_tube_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {C s : NNReal} (hC : 1 ≤ C) (hs0 : 0 < s) (hs : s ≤ 2 * C) (T : Tube s E) :
    4 * (lt_volume_convexHull.c 3 : ENNReal) * (s : ENNReal) ^ 2
        ≤ volume (Tube.dilate T 2).carrier ∧
      volume (Tube.dilate T 2).carrier ≤ 320 * (C : ENNReal) * (s : ENNReal) ^ 2 := by
  have hred : volume (Tube.dilate T 2).carrier = (8 : ENNReal) * volume T.carrier := by
    rw [Tube.tubeDilateVolume T (show (1 : ℝ) < 2 by norm_num)]
    congr 1
    norm_num [Tube.tubeDilateVolume.C', hdim]
  have h82 : (8 : ENNReal) * (2 : ENNReal)⁻¹ = (4 : ENNReal) := by
    have h2 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    calc
      (8 : ENNReal) * (2 : ENNReal)⁻¹ = (4 : ENNReal) * (2 : ENNReal) * (2 : ENNReal)⁻¹ := by ring
      _ = (4 : ENNReal) * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by rw [mul_assoc]
      _ = (4 : ENNReal) := by rw [h2, mul_one]
  have hbounds := volume_bounds_of_tube hdim hC hs0 hs T
  rcases hbounds with ⟨hL, hU⟩
  rw [hred]
  constructor
  · calc
      4 * (lt_volume_convexHull.c 3 : ENNReal) * (s : ENNReal) ^ 2
          = (8 : ENNReal) * (((2 : ENNReal)⁻¹ * (lt_volume_convexHull.c 3 : ENNReal)) *
              (s : ENNReal) ^ 2) := by
            rw [← h82]
            ring
      _ ≤ (8 : ENNReal) * volume T.carrier := by
            exact mul_le_mul_right hL (8 : ENNReal)
  · calc
      (8 : ENNReal) * volume T.carrier
          ≤ (8 : ENNReal) * (40 * (C : ENNReal) * (s : ENNReal) ^ 2) := by
            exact mul_le_mul_right hU (8 : ENNReal)
      _ = 320 * (C : ENNReal) * (s : ENNReal) ^ 2 := by
            ring

end Tube

/-! ### A prism with normalized first half-width lies in a unit-core tube -/

section Prism

variable {E S : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace S] [NormedAddTorsor E S]

omit [FiniteDimensional ℝ E] in
/-- **Transverse distance from the long axis of a prism** (blueprint
`lem:prismTransverseDist`).

Let `P` be a rectangular prism with centre `c`, orthonormal axes `(eₖ)` and half-widths `(rₖ)`.
For `x ∈ P`, writing `t₀ = ⟪x -ᵥ c, e₀⟫`, the point `c + t₀ e₀` is within `r₁ + ⋯ + r_{n-1}` of
`x`.

Indeed `x -ᵥ c = ∑ₖ tₖ eₖ` with `|tₖ| ≤ rₖ`, so `x -ᵥ (t₀ e₀ +ᵥ c) = ∑_{k ≥ 1} tₖ eₖ` and the
triangle inequality applies.  The crude bound `‖∑_{k ≥ 1} tₖ eₖ‖ ≤ ∑_{k ≥ 1} |tₖ|` is
deliberate: in the case `n = 3` used downstream the sharp estimate `√(t₁² + t₂²)` would put a
square root into the tube scale and propagate it into every constant; see blueprint
`note:ml1bootPlankTubeNoSqrt`. -/
theorem dist_prism_transverse_le {n : ℕ} (P : PrismNDim (n + 1) E S) {x : S}
    (hx : x ∈ P.carrier) :
    dist x (P.basis.repr (x -ᵥ P.center) 0 • P.basis 0 +ᵥ P.center)
      ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ) := by
  set t := fun i : Fin (n + 1) => P.basis.repr (x -ᵥ P.center) i with ht
  have ht_sum : x -ᵥ P.center = ∑ k : Fin (n + 1), t k • P.basis k := by
    calc
      x -ᵥ P.center = ∑ k, (P.basis.repr (x -ᵥ P.center) k) • P.basis k := by
        symm; exact P.basis.sum_repr (x -ᵥ P.center)
      _ = ∑ k, t k • P.basis k := by
        simp [t]
  have hx' : ∀ k, |t k| ≤ (P.thicknesses k : ℝ) := by
    intro k
    have := (P.mem_carrier_iff x).mp hx k
    simpa [t] using this
  calc
    dist x (t 0 • P.basis 0 +ᵥ P.center) = ‖x -ᵥ (t 0 • P.basis 0 +ᵥ P.center)‖ := by
      rw [dist_eq_norm_vsub E]
    _ = ‖(x -ᵥ P.center) - t 0 • P.basis 0‖ := by
      rw [vsub_vadd_eq_vsub_sub]
    _ = ‖∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), t k • P.basis k‖ := by
      have h_eq : (x -ᵥ P.center) - t 0 • P.basis 0
          = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), t k • P.basis k := by
        calc
          (x -ᵥ P.center) - t 0 • P.basis 0 =
              (∑ k : Fin (n + 1), t k • P.basis k) - t 0 • P.basis 0 := by rw [ht_sum]
          _ = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), t k • P.basis k := by
            simp [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin (n + 1)))]
      rw [h_eq]
    _ ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), ‖t k • P.basis k‖ :=
      norm_sum_le (Finset.univ.erase (0 : Fin (n + 1))) (fun k => t k • P.basis k)
    _ = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (|t k| * ‖P.basis k‖) := by
      simp [norm_smul]
    _ = ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), |t k| := by
      simp [P.basis.orthonormal.norm_eq_one]
    _ ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ) :=
      Finset.sum_le_sum fun k _ => hx' k

end Prism

section UnitCore

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The unit segment centred at a point along a unit vector** (blueprint
`lem:unitCoreSegment`).

For `‖e‖ = 1` the endpoints `p = c - 2⁻¹ e` and `q = c + 2⁻¹ e` are at distance exactly `1`, so
`[p, q]` is a legitimate `Tube` core with no side condition to discharge, and `c + t e ∈ [p, q]`
whenever `|t| ≤ 2⁻¹`, the convex weights being `2⁻¹ - t` and `2⁻¹ + t`. -/
theorem unitCoreSegment (c : E) {e : E} (he : ‖e‖ = 1) :
    dist (c - (2⁻¹ : ℝ) • e) (c + (2⁻¹ : ℝ) • e) = 1 ∧
      ∀ t : ℝ, |t| ≤ 2⁻¹ →
        c + t • e ∈ segment ℝ (c - (2⁻¹ : ℝ) • e) (c + (2⁻¹ : ℝ) • e) := by
  constructor
  · have hsub : (c - (2⁻¹ : ℝ) • e) - (c + (2⁻¹ : ℝ) • e) = -e := by
      module
    rw [dist_eq_norm, hsub, norm_neg, he]
  · intro t ht
    rw [segment]
    refine ⟨2⁻¹ - t, 2⁻¹ + t, ?_, ?_, ?_, ?_⟩
    · linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
    · linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
    · linarith
    · module

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A prism with normalized first half-width lies in the `2`-dilate of a unit-core tube**
(blueprint `lem:prismUnitCoreTube`).

Let `P` be a rectangular prism in `E` with centre `c`, orthonormal axes `(eₖ)` and half-widths
`(rₖ)` satisfying the normalization `r₀ ≤ Λ₀` for some `Λ₀ ≥ 1`, and put `p = c - 2⁻¹ e₀`,
`q = c + 2⁻¹ e₀`.  Then `dist p q = 1`, and for every scale `s` with
`r₁ + ⋯ + r_{n-1} ≤ 2 Λ₀ s` the prism `P` lies in the `(2 Λ₀)`-dilate of the `s`-tube with core
`[p, q]`.

For `x ∈ P` put `t₀ = ⟪x - c, e₀⟫` and `y = c + t₀ e₀`.  Then `|t₀| ≤ r₀ ≤ Λ₀ = (2 Λ₀) / 2` and
`Kakeya.ml1Boot.dist_prism_transverse_le` gives `dist x y ≤ r₁ + ⋯ + r_{n-1} ≤ (2 Λ₀) s`, which is
exactly the input of `Kakeya.Tube.mem_dilate_of_dist_axis_le` at dilation ratio `c = 2 Λ₀`.

The normalization is `r₀ ≤ Λ₀` and not `r₀ ≤ 2⁻¹`, and the conclusion is correspondingly
weakened from `P ⊆ T` to `P ⊆ (2 Λ₀) · T`: the half-width `2⁻¹` is unattainable for the planks of
this development, whose first ethickness always exceeds `2⁻¹`, so the sharper form is vacuous
there (blueprint `note:ml1bootPlankInTubeVacuous`).  The side condition
`r₁ + ⋯ + r_{n-1} ≤ 2 Λ₀ s` is likewise the dilated form of `r₁ + ⋯ + r_{n-1} ≤ s`, and it is what
lets the tube scale be `C b` rather than `2 C b`.

**Why the normalization is free.**  At `Λ₀ = 1` this is the earlier statement verbatim, and the
proof spends the enlarged normalization only through `|t₀| ≤ (2 Λ₀) / 2`, which the membership
criterion asks on the nose.  The generalization is what admits a genuine
`Kakeya.IsPlankOfDimensions` plank, whose first affine thickness is its *circumradius*
`√(1 + a² + b²) > 1` and so fails
`r₀ ≤ 1` by a factor `Θ(σ²)`; blueprint `note:ml1bootEnlargementTubeStatus` records that gap and
`lem:ml1bootEnlargementPlank` names this as the first of the two generalizations that absorb it.

The statement is phrased in a normed space rather than over a torsor, because a `Tube` core is a
segment of the space itself; see blueprint `note:prismTorsorVsTube`. -/
theorem prism_subset_unitCoreTube {n : ℕ} (P : PrismNDim (n + 1) E E) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (hr₀ : (P.thicknesses 0 : ℝ) ≤ Λ₀) :
    dist (P.center - (2⁻¹ : ℝ) • P.basis 0) (P.center + (2⁻¹ : ℝ) • P.basis 0) = 1 ∧
      ∀ s : NNReal,
        (∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ)) ≤ 2 * Λ₀ * (s : ℝ) →
          ∃ T : Tube s E, T.x = P.center - (2⁻¹ : ℝ) • P.basis 0 ∧
            T.y = P.center + (2⁻¹ : ℝ) • P.basis 0 ∧
            (P.carrier : Set E) ⊆ (Tube.dilate T (2 * Λ₀)).carrier := by
  constructor
  · exact (unitCoreSegment P.center (P.basis.orthonormal.norm_eq_one 0)).1
  · intro s hsum
    let T : Tube s E :=
      Tube.mk' s (unitCoreSegment P.center (P.basis.orthonormal.norm_eq_one 0)).1
    refine ⟨T, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · intro x hx
      let t0 : ℝ := P.basis.repr (x - P.center) 0
      have ht0 : |t0| ≤ (P.thicknesses 0 : ℝ) := by
        have := (P.mem_carrier_iff x).mp hx 0
        simpa [t0] using this
      have htrans : dist x (P.center + t0 • P.basis 0) ≤
          ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ) := by
        calc
          dist x (P.center + t0 • P.basis 0)
              = dist x (P.basis.repr (x -ᵥ P.center) 0 • P.basis 0 +ᵥ P.center) := by
                  have hpt : P.center + t0 • P.basis 0
                      = P.basis.repr (x -ᵥ P.center) 0 • P.basis 0 +ᵥ P.center := by
                    simp [t0, add_comm]
                  rw [hpt]
          _ ≤ ∑ k ∈ Finset.univ.erase (0 : Fin (n + 1)), (P.thicknesses k : ℝ) :=
              dist_prism_transverse_le P hx
      have hcen : T.center = P.center := by
        simp [T, Tube.center, midpoint_eq_smul_add]
        module
      have hdir : T.direction = P.basis 0 := by
        simp [T, Tube.direction]
        module
      have hcore : T.center + t0 • T.direction = P.center + t0 • P.basis 0 := by
        rw [hcen, hdir]
      have hz : dist x (T.center + t0 • T.direction) ≤ (2 * Λ₀) * (s : ℝ) := by
        rw [hcore]
        exact le_trans htrans hsum
      have hs : |t0| ≤ (2 * Λ₀) / 2 := by
        have : (2 * Λ₀) / 2 = Λ₀ := by ring
        rw [this]
        exact ht0.trans hr₀
      exact Tube.mem_dilate_of_dist_axis_le T (C := 2 * Λ₀) (by linarith) hs hz

end UnitCore

/-! ### The tube attached to a plank -/

section PlankTube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The tube attached to a plank** (blueprint `def:ml1bootPlankTube`).

For a nonempty compact `W ⊆ ℝ³`, let `c` be the centre and `(e₀, e₁, e₂)` the orthonormal axis
frame of `outerPrism W`, whose half-width along `eₖ` is `Metric.thickness ℝ W k`
(`outerPrism.thicknesses_eq`); thus `e₀` is its long axis.  Then `plankTube` is the tube of
scale `C b` whose core is the segment of length `1` centred at `c` and directed along `e₀`;
the endpoints are at distance exactly `1` because `e₀` is a unit vector, so `Tube.mk'` applies
with no side condition.

The scale is `C b` and not `2 C b`: the factor `2` that the two transverse half-widths
`r₁ + r₂ ≤ 2 C b` would demand is paid for on the containment side instead, by
`Kakeya.ml1Boot.subset_plankTube` landing in the `2`-dilate.

Only nonemptiness and compactness of `W` are used; no hypothesis on the thicknesses of `W`
enters.  In the intended application `C = Kakeya.ml1Boot.plankPigeonhole.C`. -/
noncomputable def plankTube (hdim : Module.finrank ℝ E = 3) (C b : NNReal)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty) : Tube (C * b) E :=
  Tube.mk' (C * b)
    (x := outerPrism.center hdim hW hWne - (2⁻¹ : ℝ) • outerPrism.basis hdim hW hWne 0)
    (y := outerPrism.center hdim hW hWne + (2⁻¹ : ℝ) • outerPrism.basis hdim hW hWne 0)
    (by
      have hsub : (outerPrism.center hdim hW hWne
              - (2⁻¹ : ℝ) • outerPrism.basis hdim hW hWne 0)
            - (outerPrism.center hdim hW hWne
              + (2⁻¹ : ℝ) • outerPrism.basis hdim hW hWne 0)
          = -outerPrism.basis hdim hW hWne 0 := by
        module
      rw [dist_eq_norm, hsub, norm_neg]
      exact (outerPrism.basis hdim hW hWne).orthonormal.norm_eq_one 0)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A plank with normalized long side is contained in the `2`-dilate of the tube attached to
it** (blueprint `lem:ml1bootPlankTubeContainment`).

If `W ⊆ ℝ³` is nonempty and compact with `τ₀(W) ≤ Λ₀` for some `Λ₀ ≥ 1`, `τ₁(W) ≤ C b` and
`τ₂(W) ≤ C b`, then `W` is contained in the `(2 Λ₀)`-dilate of `Kakeya.ml1Boot.plankTube`, the tube
of scale `C b` attached to `W`.

Apply `Kakeya.ml1Boot.prism_subset_unitCoreTube` to `P = outerPrism W`, whose half-widths are
`rₖ = Metric.thickness ℝ W k` (`outerPrism.thicknesses_eq`): the normalization `r₀ ≤ Λ₀` is the
first hypothesis and the side condition `r₁ + r₂ ≤ 2 C b ≤ 2 Λ₀ (C b)` the other two together with
`1 ≤ Λ₀`, so `outerPrism W ⊆ (2 Λ₀) · plankTube`, and `W ⊆ outerPrism W` by
`outerPrism.self_subset`.  At `Λ₀ = 1` this is the earlier statement verbatim, and `1 ≤ Λ₀` is used
nowhere else.

The hypothesis on `τ₀` is `≤ Λ₀` rather than `≤ 2⁻¹`, which is what makes the lemma applicable
to the planks of this development at all; the price is that the conclusion is a containment in
`Kakeya.Tube.dilate (plankTube …) (2 Λ₀)` and not in `plankTube …` itself.  Taking `Λ₀ = C` lets a
genuine `Kakeya.IsPlankOfDimensions C a b W` plank — whose predicate already asserts
`τ₀(W) ≤ C` — be fed in directly, which is what closes the `Θ(σ²)` circumradius gap recorded at
blueprint `note:ml1bootEnlargementTubeStatus`.

This is the one statement of the group phrased in the affine thicknesses rather than the
ethicknesses, because `outerPrism.thicknesses_eq` delivers the prism's half-widths as
`Metric.thickness ℝ W k`; the three hypotheses are fed in from ethickness bounds through
`Metric.ethickness_thickness`, `W` being bounded. -/
theorem subset_plankTube (hdim : Module.finrank ℝ E = 3) (C b : NNReal) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty)
    (hτ₀ : thickness ℝ W 0 ≤ Λ₀) (hτ₁ : thickness ℝ W 1 ≤ (C : ℝ) * (b : ℝ))
    (hτ₂ : thickness ℝ W 2 ≤ (C : ℝ) * (b : ℝ)) :
    W ⊆ (Tube.dilate (plankTube hdim C b hW hWne) (2 * Λ₀)).carrier := by
  set P : PrismNDim 3 E E := outerPrism hdim hW hWne with hP_def
  -- the half-widths of P are exactly the thicknesses of W
  have hthick (i : Fin 3) : (P.thicknesses i : ℝ) = thickness ℝ W i := by
    rw [hP_def]
    rw [outerPrism.thicknesses_eq hdim hW hWne i]
    rfl
  -- the normalization r₀ = τ₀(W) ≤ Λ₀
  have hP₀ : (P.thicknesses 0 : ℝ) ≤ Λ₀ := by
    rw [hthick]
    exact hτ₀
  -- the side condition r₁ + r₂ = τ₁(W) + τ₂(W) ≤ 2 Λ₀ · (C b)
  have hsum0 : (∑ k ∈ Finset.univ.erase (0 : Fin 3), thickness ℝ W k) =
      thickness ℝ W 1 + thickness ℝ W 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 3))]
    rw [Fin.sum_univ_three]
    abel
  have hsum : (∑ k ∈ Finset.univ.erase (0 : Fin 3), (P.thicknesses k : ℝ)) ≤
      2 * Λ₀ * ((C * b : NNReal) : ℝ) := by
    have hsum' : (∑ k ∈ Finset.univ.erase (0 : Fin 3), (P.thicknesses k : ℝ)) ≤
        2 * ((C * b : NNReal) : ℝ) := by
      calc
        (∑ k ∈ Finset.univ.erase (0 : Fin 3), (P.thicknesses k : ℝ))
            = ∑ k ∈ Finset.univ.erase (0 : Fin 3), thickness ℝ W k := by
              exact Finset.sum_congr rfl (fun k _ => hthick k)
        _ = thickness ℝ W 1 + thickness ℝ W 2 := hsum0
        _ ≤ (C : ℝ) * (b : ℝ) + (C : ℝ) * (b : ℝ) :=
          add_le_add hτ₁ hτ₂
        _ = 2 * ((C * b : NNReal) : ℝ) := by
          push_cast
          ring
    calc
      (∑ k ∈ Finset.univ.erase (0 : Fin 3), (P.thicknesses k : ℝ))
          ≤ 2 * ((C * b : NNReal) : ℝ) := hsum'
      _ ≤ 2 * Λ₀ * ((C * b : NNReal) : ℝ) := by
        have hCb : 0 ≤ ((C * b : NNReal) : ℝ) := by positivity
        nlinarith
  -- apply the geometric black box to P
  rcases (prism_subset_unitCoreTube P hΛ₀ hP₀).2 (C * b) hsum with ⟨T, hxT, hyT, hcarT⟩
  -- check that T is exactly plankTube
  set T₀ : Tube (C * b) E := plankTube hdim C b hW hWne
  have hxT₀ : T.x = T₀.x := by
    rw [hxT]
    rfl
  have hyT₀ : T.y = T₀.y := by
    rw [hyT]
    rfl
  have hcar : T.carrier = T₀.carrier := by
    calc
      T.carrier = ⋃ z ∈ segment ℝ T.x T.y, closedBall z (C * b) := T.carrier_eq
      _ = ⋃ z ∈ segment ℝ T₀.x T₀.y, closedBall z (C * b) := by
            rw [hxT₀, hyT₀]
      _ = T₀.carrier := T₀.carrier_eq.symm
  have hT : T = T₀ := Tube.ext hcar hxT₀ hyT₀
  have hcarT₀ : (P.carrier : Set E) ⊆ (Tube.dilate T₀ (2 * Λ₀)).carrier := by
    rwa [hT] at hcarT
  -- W ⊆ outerPrism W ⊆ (2 Λ₀) · plankTube
  have hWP : W ⊆ P.carrier := by
    simpa [hP_def] using outerPrism.self_subset hdim hW hWne
  exact hWP.trans hcarT₀

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Every point of a nonempty compact set is close to the centre of its outer prism.**

`outerPrism.center` is pinned down only through `outerPrism.basis_repr_le`, which says that in
the orthonormal frame of the prism every point `x ∈ W` has `k`-th coordinate of `x - c` bounded
by `Metric.thickness ℝ W k`.  Since that frame is orthonormal, the Pythagorean identity turns
those `n` coordinate bounds into the single bound
`dist x c ≤ √(τ₀² + ⋯ + τ_{n-1}²)`.

This is the *only* localization of `outerPrism.center` available: the defining property is a
box containment, and it does not place the centre inside `W`, nor inside `convexHull ℝ W`. -/
theorem dist_outerPrism_center_le {n : ℕ} (hn : Module.finrank ℝ E = n)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty) {x : E} (hx : x ∈ W) :
    dist x (outerPrism.center hn hW hWne)
      ≤ Real.sqrt (∑ i : Fin n, thickness ℝ W (i : ℕ) ^ 2) := by
  let b : OrthonormalBasis (Fin n) ℝ E := outerPrism.basis hn hW hWne
  let c : E := outerPrism.center hn hW hWne
  have hrepr : ∀ i : Fin n, ‖b.repr (x - c) i‖ ≤ thickness ℝ W i := by
    intro i
    have hb : |(b.repr (x - c)) i| ≤ thickness ℝ W i := by
      simpa [b, c] using (outerPrism.basis_repr_le hn hW hWne hx i)
    rw [Real.norm_eq_abs]
    exact hb
  calc
    dist x c = ‖x - c‖ := by rw [dist_eq_norm]
    _ = ‖b.repr (x - c)‖ := by
      rw [← b.repr.norm_map (x - c)]
    _ = √ (∑ i, ‖b.repr (x - c) i‖ ^ 2) := by
      rw [EuclideanSpace.norm_eq]
    _ ≤ √ (∑ i : Fin n, thickness ℝ W (i : ℕ) ^ 2) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => ?_))
      exact pow_le_pow_left₀ (norm_nonneg _) (hrepr i) 2

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The outer-prism centre of a subset of the unit ball lies in the ball of radius `1 + √3`.**

If `W ⊆ closedBall 0 1` is nonempty and compact then each of its three thicknesses is at most
`1` (`Metric.thickness_le_of_subset_closedBall`), so `Kakeya.ml1Boot.dist_outerPrism_center_le`
gives `dist x c ≤ √3` for any `x ∈ W`, and `‖c‖ ≤ ‖x‖ + √3 ≤ 1 + √3`.

The bound is `1 + √3 ≈ 2.7321` and **not** `1`: the centre of the outer prism is not asserted to
lie in `W`, so the triangle inequality through a point of `W` is all that the interface of
`outerPrism` supports. -/
theorem norm_outerPrism_center_le (hdim : Module.finrank ℝ E = 3)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty)
    (hWball : W ⊆ closedBall (0 : E) 1) :
    ‖outerPrism.center hdim hW hWne‖ ≤ 1 + Real.sqrt 3 := by
  obtain ⟨x, hx⟩ := id hWne
  let c : E := outerPrism.center hdim hW hWne
  -- every thickness of W is at most the radius 1 of the surrounding unit ball
  have hthk (k : ℕ) : thickness ℝ W k ≤ 1 :=
    thickness_le_of_subset_closedBall hWball (by norm_num) k
  have hthk2 (i : Fin 3) : (thickness ℝ W (i : ℕ)) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (thickness_nonneg W (i : ℕ)) (hthk (i : ℕ)) 2
  -- the three squared thicknesses sum to at most 3
  have hsum3 : (∑ i : Fin 3, thickness ℝ W (i : ℕ) ^ 2) ≤ 3 := by
    rw [Fin.sum_univ_three]
    nlinarith [hthk2 (0 : Fin 3), hthk2 (1 : Fin 3), hthk2 (2 : Fin 3)]
  have hsqrt : Real.sqrt (∑ i : Fin 3, thickness ℝ W (i : ℕ) ^ 2) ≤ Real.sqrt 3 :=
    Real.sqrt_le_sqrt hsum3
  -- a chosen point of W lies in the unit ball, hence ‖x‖ ≤ 1
  have hxnorm : ‖x‖ ≤ 1 := by
    have hdx : dist x (0 : E) ≤ 1 := Metric.mem_closedBall.mp (hWball hx)
    rwa [dist_zero_right] at hdx
  -- dist x c ≤ √3 via the already-proved localisation of the centre
  have hdist : dist x c ≤ Real.sqrt 3 := by
    calc
      dist x c ≤ Real.sqrt (∑ i : Fin 3, thickness ℝ W (i : ℕ) ^ 2) := by
        simpa [c] using dist_outerPrism_center_le hdim hW hWne hx
      _ ≤ Real.sqrt 3 := hsqrt
  -- triangle inequality through the chosen point x of W
  have hnormc : ‖c‖ ≤ ‖x‖ + ‖c - x‖ := by
    calc
      ‖c‖ = ‖x + (c - x)‖ := by
        rw [show x + (c - x) = c by abel]
      _ ≤ ‖x‖ + ‖c - x‖ := norm_add_le x (c - x)
  have htotal : ‖c‖ ≤ 1 + Real.sqrt 3 := by
    calc
      ‖c‖ ≤ ‖x‖ + ‖c - x‖ := hnormc
      _ = ‖x‖ + dist c x := by rw [← dist_eq_norm]
      _ = ‖x‖ + dist x c := by rw [dist_comm]
      _ ≤ 1 + Real.sqrt 3 := by linarith
  simpa [c] using htotal

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The tube attached to a plank lies in the ball of radius `1/2 + C b` about the plank's
outer-prism centre.**

The core of `Kakeya.ml1Boot.plankTube` is the unit segment centred at
`outerPrism.center hdim hW hWne`, so that point is the midpoint of the two endpoints and
`Kakeya.Tube.carrier_subset_closedBall_midpoint` applies verbatim. -/
theorem plankTube_carrier_subset_closedBall_center (hdim : Module.finrank ℝ E = 3) (C b : NNReal)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty) :
    (plankTube hdim C b hW hWne).carrier
      ⊆ closedBall (outerPrism.center hdim hW hWne) (1 / 2 + ((C * b : NNReal) : ℝ)) := by
  have hT : (plankTube hdim C b hW hWne).carrier ⊆
      Metric.closedBall (midpoint ℝ (plankTube hdim C b hW hWne).x (plankTube hdim C b hW hWne).y)
        (1 / 2 + ((C * b : NNReal) : ℝ)) :=
    Tube.carrier_subset_closedBall_midpoint (E := E) (plankTube hdim C b hW hWne)
  have hmid : midpoint ℝ (plankTube hdim C b hW hWne).x (plankTube hdim C b hW hWne).y =
      outerPrism.center hdim hW hWne := by
    simp [plankTube, Tube.mk', midpoint_sub_add]
  simpa [hmid] using hT

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The tube attached to a plank inside the unit ball is itself located, at radius
`3/2 + √3 + C b`.**

Combining `Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_center` with
`Kakeya.ml1Boot.norm_outerPrism_center_le`: the carrier lies within `1/2 + C b` of the centre,
and the centre lies within `1 + √3` of the origin.

This locates the `b`-scale tubes *directly*, from the explicit construction, at an absolute
radius of order `1`.  Routing the same question through the exported dilate clause
`(Tb j).toConvexSpaceBody ≤ Tube.dilate (Trho j.1) plankTubeInParent.C` would instead give
`1 + 3 * plankTubeInParent.C / 2`, larger by five orders of magnitude. -/
theorem plankTube_carrier_subset_closedBall (hdim : Module.finrank ℝ E = 3) (C b : NNReal)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty)
    (hWball : W ⊆ closedBall (0 : E) 1) :
    (plankTube hdim C b hW hWne).carrier
      ⊆ closedBall (0 : E) (3 / 2 + Real.sqrt 3 + ((C * b : NNReal) : ℝ)) := by
  have hcenter : (plankTube hdim C b hW hWne).carrier ⊆
      closedBall (outerPrism.center hdim hW hWne) (1 / 2 + ((C * b : NNReal) : ℝ)) :=
    plankTube_carrier_subset_closedBall_center hdim C b hW hWne
  have hnorm : ‖outerPrism.center hdim hW hWne‖ ≤ 1 + Real.sqrt 3 :=
    norm_outerPrism_center_le hdim hW hWne hWball
  have hside : 1 / 2 + ((C * b : NNReal) : ℝ) + dist (outerPrism.center hdim hW hWne) (0 : E)
      ≤ 3 / 2 + Real.sqrt 3 + ((C * b : NNReal) : ℝ) := by
    have hdist : dist (outerPrism.center hdim hW hWne) (0 : E)
        = ‖outerPrism.center hdim hW hWne‖ := by
      rw [dist_zero_right]
    linarith
  exact hcenter.trans (Metric.closedBall_subset_closedBall' (x := outerPrism.center hdim hW hWne)
    (y := (0 : E)) (ε₁ := 1 / 2 + ((C * b : NNReal) : ℝ))
    (ε₂ := 3 / 2 + Real.sqrt 3 + ((C * b : NNReal) : ℝ)) hside)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The numerical form of `Kakeya.ml1Boot.plankTube_carrier_subset_closedBall`.**

Under the side condition `C b ≤ 1` that is already available on the Section 8 route — there in
the shape `plankPigeonhole.C * bp ≤ 1` — the radius `3/2 + √3 + C b` is at most `9/2`, since
`√3 ≤ 2`.  Under the stronger `C b ≤ 1/2` the same computation gives `4`. -/
theorem plankTube_carrier_subset_closedBall_of_le (hdim : Module.finrank ℝ E = 3) (C b : NNReal)
    {W : Set E} (hW : IsCompact W) (hWne : W.Nonempty)
    (hWball : W ⊆ closedBall (0 : E) 1) (hCb : ((C * b : NNReal) : ℝ) ≤ 1) :
    (plankTube hdim C b hW hWne).carrier ⊆ closedBall (0 : E) (9 / 2) := by
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    have hsq : (Real.sqrt 3) ^ 2 ≤ (2 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith
  have hside : 3 / 2 + Real.sqrt 3 + ((C * b : NNReal) : ℝ) ≤ 9 / 2 := by
    nlinarith
  exact (plankTube_carrier_subset_closedBall hdim C b hW hWne hWball).trans
    (closedBall_subset_closedBall hside)

end PlankTube

/-! ### The arithmetic of the constants -/

/-- **Both constant requirements of the repaired plank-in-tube lemma** (blueprint
`lem:ml1bootPlankInTubeConstantBounds`).

The declared value `256 C⁶ · Metric.volume_comparison.C 3` of
`Kakeya.ml1Boot.plankInTube.C` dominates both requirements computed in the proof of
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one`, namely `320 C⁶ / c₃` (from the ratio
`|2 · T_b| / ((b / a) |W|)`) and `2 C / c₃` (from the reverse ratio); these are exactly the two
hypotheses `hC₂`, `hC₁` of `Kakeya.ml1Boot.plank_dilate_volume_ratio`.

Writing `V = Metric.volume_comparison.C 3 = 4³ / c₃`, so that `c₃⁻¹ = V / 64`, the first reads
`(320 / 64) C⁶ V ≤ 256 C⁶ V`, i.e. `5 ≤ 256`, and the second reads
`C V / 32 ≤ 256 C⁶ V`, i.e. `1 ≤ 8192 C⁵`, which needs only `1 ≤ C`.  No tight computation is
claimed.  As explained in the module docstring, the right-hand side is the unfolding of
`Kakeya.ml1Boot.plankInTube.C` at the parameter `C`; instantiating
`C := Kakeya.ml1Boot.plankPigeonhole.C` returns the blueprint statement about
`Kakeya.ml1Boot.plankInTube.C` verbatim. -/
theorem plankInTube_constant_bounds {C : NNReal} (hC : 1 ≤ C) :
    320 * C ^ 6 / lt_volume_convexHull.c 3 ≤ 256 * C ^ 6 * volume_comparison.C 3 ∧
      2 * C / lt_volume_convexHull.c 3 ≤ 256 * C ^ 6 * volume_comparison.C 3 := by
  have hc_pos : 0 < lt_volume_convexHull.c 3 := lt_volume_convexHull.c_pos 3
  have hc_ne : lt_volume_convexHull.c 3 ≠ 0 := hc_pos.ne'
  have hV : volume_comparison.C 3 = 4 ^ 3 / lt_volume_convexHull.c 3 := rfl
  have hC6 : C ≤ C ^ 6 := by
    simpa using pow_le_pow_right₀ hC (by norm_num : 1 ≤ 6)
  constructor
  · rw [div_le_iff₀ hc_pos, hV]
    have hclear : (256 * C ^ 6 * (4 ^ 3 / lt_volume_convexHull.c 3)) * lt_volume_convexHull.c 3 =
        256 * C ^ 6 * 4 ^ 3 := by
      rw [mul_assoc, div_mul_cancel₀ (4 ^ 3) hc_ne]
    rw [hclear]
    calc
      320 * C ^ 6 ≤ 256 * 4 ^ 3 * C ^ 6 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 256 * C ^ 6 * 4 ^ 3 := by
        ring
  · rw [div_le_iff₀ hc_pos, hV]
    have hclear : (256 * C ^ 6 * (4 ^ 3 / lt_volume_convexHull.c 3)) * lt_volume_convexHull.c 3 =
        256 * C ^ 6 * 4 ^ 3 := by
      rw [mul_assoc, div_mul_cancel₀ (4 ^ 3) hc_ne]
    rw [hclear]
    calc
      2 * C ≤ 256 * 4 ^ 3 * C ^ 6 := by
        calc
          2 * C ≤ 256 * 4 ^ 3 * C := by
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ ≤ 256 * 4 ^ 3 * C ^ 6 := by
            exact mul_le_mul_of_nonneg_left hC6 (by positivity)
      _ = 256 * C ^ 6 * 4 ^ 3 := by
        ring

/-- **The volume ratio of a plank and the `2`-dilate of its tube** (blueprint
`lem:ml1bootPlankDilateVolumeRatio`).

Purely numerical: if `w` is a quantity comparable to `a b` with the constants that
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions` supplies for a plank, and `V` is a
quantity comparable to `b²` with the constants that
`Kakeya.ml1Boot.volume_bounds_of_tube_dilate` supplies for the `2`-dilate of a tube of scale
`Cw b`, then `V` is comparable to `(b / a) w` with constant `C`, provided `C` dominates the
two ratios `2 Cw / c₃` and `320 Cw⁶ / c₃`.

Splitting this off keeps the volume arithmetic of
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` — and of the variant used
by `Kakeya.ml1Boot.volume_plankTube_le` — free of any geometry: the four volume bounds and
the two constant requirements are all that enter.  In the intended application
`Cw = Kakeya.ml1Boot.plankPigeonhole.C` and `C = Kakeya.ml1Boot.plankInTube.C`, the two
constant requirements being supplied by `Kakeya.ml1Boot.plankInTube_constant_bounds`. -/
theorem plank_dilate_volume_ratio {Cw C a b : NNReal} (hCw : 1 ≤ Cw) (hC : 1 ≤ C)
    (ha0 : 0 < a) (_hab : a ≤ b) {w V : ENNReal}
    (hwlo : ((Cw : ENNReal) ^ 3)⁻¹ * (lt_volume_convexHull.c 3 : ENNReal)
      * ((a : ENNReal) * (b : ENNReal)) ≤ w)
    (hwhi : w ≤ 8 * (Cw : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal)))
    (hVlo : 4 * (lt_volume_convexHull.c 3 : ENNReal) * (Cw : ENNReal) ^ 2 * (b : ENNReal) ^ 2
      ≤ V)
    (hVhi : V ≤ 320 * (Cw : ENNReal) ^ 3 * (b : ENNReal) ^ 2)
    (hC₁ : 2 * Cw / lt_volume_convexHull.c 3 ≤ C)
    (hC₂ : 320 * Cw ^ 6 / lt_volume_convexHull.c 3 ≤ C) :
    (C : ENNReal)⁻¹ * ((b : ENNReal) / (a : ENNReal)) * w ≤ V ∧
      V ≤ (C : ENNReal) * ((b : ENNReal) / (a : ENNReal)) * w := by
  set CwE : ENNReal := (Cw : ENNReal) with hCwEdef
  set CE : ENNReal := (C : ENNReal) with hCEdef
  set bE : ENNReal := (b : ENNReal) with hbEdef
  set aE : ENNReal := (a : ENNReal) with haEdef
  set c₃ : ENNReal := (Metric.lt_volume_convexHull.c 3 : ENNReal) with hc₃def
  have hc₃pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
  have hCwE0 : CwE ≠ 0 := by
    change (Cw : ENNReal) ≠ 0
    exact ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hCw).ne'
  have hCwEtop : CwE ≠ ⊤ := ENNReal.coe_ne_top
  have hCwE3n0 : CwE ^ 3 ≠ 0 := pow_ne_zero 3 hCwE0
  have hCwE3top : CwE ^ 3 ≠ ⊤ := by
    rw [show CwE ^ 3 = CwE * CwE * CwE by ring]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hCwEtop hCwEtop) hCwEtop
  have hCE0 : CE ≠ 0 := by
    change (C : ENNReal) ≠ 0
    exact ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hC).ne'
  have hCEtop : CE ≠ ⊤ := ENNReal.coe_ne_top
  have hc₃0 : c₃ ≠ 0 := by
    change (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0
    exact_mod_cast hc₃pos.ne'
  have hc₃top : c₃ ≠ ⊤ := ENNReal.coe_ne_top
  have haE0 : aE ≠ 0 := by
    change (a : ENNReal) ≠ 0
    exact ENNReal.coe_ne_zero.mpr ha0.ne'
  have haEtop : aE ≠ ⊤ := ENNReal.coe_ne_top
  -- the two constant requirements, transferred to ENNReal
  have hcast₁ : ((2 * Cw / Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal)
      = (2 : ENNReal) * (Cw : ENNReal) / (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
    rw [ENNReal.coe_div hc₃pos.ne']
    norm_num [ENNReal.coe_mul]
  have hC₁EN : (2 : ENNReal) * CwE / c₃ ≤ CE := by
    change (2 : ENNReal) * (Cw : ENNReal) / (Metric.lt_volume_convexHull.c 3 : ENNReal)
        ≤ (C : ENNReal)
    rw [← hcast₁]
    exact_mod_cast hC₁
  have hcast₂ : ((320 * Cw ^ 6 / Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal)
      = (320 : ENNReal) * (Cw : ENNReal) ^ 6 / (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
    rw [ENNReal.coe_div hc₃pos.ne']
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
    norm_num
  have hC₂EN : (320 : ENNReal) * CwE ^ 6 / c₃ ≤ CE := by
    change (320 : ENNReal) * (Cw : ENNReal) ^ 6 / (Metric.lt_volume_convexHull.c 3 : ENNReal)
        ≤ (C : ENNReal)
    rw [← hcast₂]
    exact_mod_cast hC₂
  -- the ratio b/a · a·b = b²
  have hba : (bE / aE) * (aE * bE) = bE ^ 2 := by
    calc
      (bE / aE) * (aE * bE) = ((bE / aE) * aE) * bE := by rw [mul_assoc]
      _ = bE * bE := by rw [ENNReal.div_mul_cancel haE0 haEtop]
      _ = bE ^ 2 := by rw [pow_two]
  -- lower bound: CwE-cubed disappears against a₃⁻¹
  have hC₁eq : (4 * c₃ * CwE ^ 2) * ((2 : ENNReal) * CwE / c₃) = 8 * CwE ^ 3 := by
    calc
      (4 * c₃ * CwE ^ 2) * ((2 : ENNReal) * CwE / c₃)
          = (4 * c₃ * CwE ^ 2) * ((2 : ENNReal) * CwE * c₃⁻¹) := by
            rw [div_eq_mul_inv]
      _ = 8 * CwE ^ 3 * (c₃ * c₃⁻¹) := by ring
      _ = 8 * CwE ^ 3 := by
            rw [ENNReal.mul_inv_cancel hc₃0 hc₃top]
            ring
  have h₈ : 8 * CwE ^ 3 ≤ 4 * c₃ * CwE ^ 2 * CE := by
    calc
      8 * CwE ^ 3 = (4 * c₃ * CwE ^ 2) * ((2 : ENNReal) * CwE / c₃) := hC₁eq.symm
      _ ≤ (4 * c₃ * CwE ^ 2) * CE := mul_le_mul_right hC₁EN (4 * c₃ * CwE ^ 2)
  have hconst_lo : 8 * CwE ^ 3 * CE⁻¹ ≤ 4 * c₃ * CwE ^ 2 := by
    have h8div : 8 * CwE ^ 3 / CE ≤ 4 * c₃ * CwE ^ 2 :=
      (ENNReal.div_le_iff hCE0 hCEtop).mpr h₈
    simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using h8div
  have hAlg : CE⁻¹ * (bE / aE) * (8 * CwE ^ 3 * (aE * bE)) =
      (8 * CwE ^ 3 * CE⁻¹) * bE ^ 2 := by
    calc
      CE⁻¹ * (bE / aE) * (8 * CwE ^ 3 * (aE * bE))
          = 8 * CwE ^ 3 * CE⁻¹ * ((bE / aE) * (aE * bE)) := by ring
      _ = 8 * CwE ^ 3 * CE⁻¹ * bE ^ 2 := by rw [hba]
      _ = (8 * CwE ^ 3 * CE⁻¹) * bE ^ 2 := by ring
  have hvol_lo : CE⁻¹ * (bE / aE) * w ≤ V := by
    calc
      CE⁻¹ * (bE / aE) * w ≤ CE⁻¹ * (bE / aE) * (8 * CwE ^ 3 * (aE * bE)) :=
        mul_le_mul_right hwhi (CE⁻¹ * (bE / aE))
      _ = (8 * CwE ^ 3 * CE⁻¹) * bE ^ 2 := hAlg
      _ ≤ (4 * c₃ * CwE ^ 2) * bE ^ 2 := mul_le_mul_left hconst_lo (bE ^ 2)
      _ = 4 * c₃ * CwE ^ 2 * bE ^ 2 := by ring
      _ ≤ V := hVlo
  -- upper bound: CwE to the sixth disappears against a₃⁻¹
  have hCm : CwE ^ 6 * (CwE ^ 3)⁻¹ = CwE ^ 3 := by
    calc
      CwE ^ 6 * (CwE ^ 3)⁻¹ = (CwE ^ 3 * CwE ^ 3) * (CwE ^ 3)⁻¹ := by ring
      _ = CwE ^ 3 * (CwE ^ 3 * (CwE ^ 3)⁻¹) := by rw [mul_assoc]
      _ = CwE ^ 3 * 1 := by rw [ENNReal.mul_inv_cancel hCwE3n0 hCwE3top]
      _ = CwE ^ 3 := by rw [mul_one]
  have hD : ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃ = 320 * CwE ^ 3 := by
    calc
      ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃
          = 320 * CwE ^ 6 * (CwE ^ 3)⁻¹ * (c₃ * c₃⁻¹) := by
              rw [div_eq_mul_inv]
              ring
      _ = 320 * CwE ^ 6 * (CwE ^ 3)⁻¹ := by
              rw [ENNReal.mul_inv_cancel hc₃0 hc₃top]
              ring
      _ = 320 * CwE ^ 3 := by
              rw [show 320 * CwE ^ 6 * (CwE ^ 3)⁻¹ = 320 * (CwE ^ 6 * (CwE ^ 3)⁻¹) by ring]
              rw [hCm]
  have hUconst : 320 * CwE ^ 3 ≤ CE * (CwE ^ 3)⁻¹ * c₃ := by
    calc
      320 * CwE ^ 3 = ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃ := by rw [← hD]
      _ ≤ CE * (CwE ^ 3)⁻¹ * c₃ :=
            mul_le_mul_left (mul_le_mul_left hC₂EN (CwE ^ 3)⁻¹) c₃
  have hvol_hi : V ≤ CE * (bE / aE) * w := by
    calc
      V ≤ 320 * CwE ^ 3 * bE ^ 2 := hVhi
      _ = ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃ * bE ^ 2 := by rw [← hD]
      _ ≤ (CE * (CwE ^ 3)⁻¹ * c₃) * bE ^ 2 := by
            rw [hD]
            exact mul_le_mul_left hUconst (bE ^ 2)
      _ = CE * (bE / aE) * ((CwE ^ 3)⁻¹ * c₃ * (aE * bE)) := by
            rw [← hba]
            ring
      _ ≤ CE * (bE / aE) * w := mul_le_mul_right hwlo (CE * (bE / aE))
  exact ⟨hvol_lo, hvol_hi⟩

end ml1Boot

end Kakeya
