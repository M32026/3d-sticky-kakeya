/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Dichotomy

/-!
# Main Lemma 1, Case (ii): The Frostman constant of the fibre over a `b`-tube

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The Frostman constant of the fibre over a `b`-tube -/

/-- **The constant `C_{lem:ml1bootPlankInTubeRepaired}`** (blueprint
`def:ml1bootPlankInTubeConstant`): the volume-comparison constant of the *repaired* plank-in-tube
lemma `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one`.

For a plank `W` whose thicknesses are only comparable to `1, b, a` with constant `C_𝕎`, and the
`2`-dilate of the tube of scale `C_𝕎 b` attached to it, the ratio `|2 · T_b| / (b/a · |W|)` can
be as large as `320 C_𝕎 ^ 6 / c₃`, where `c₃ = Metric.lt_volume_convexHull.c 3` and
`Metric.volume_comparison.C 3 = 4 ^ 3 / c₃`; the reverse ratio needs `2 C_𝕎 / c₃`.  Both are
dominated by the value below, which is a deliberately generous explicit choice:
`320 C_𝕎 ^ 6 / c₃ = 5 C_𝕎 ^ 6 * Metric.volume_comparison.C 3
≤ 256 C_𝕎 ^ 6 * Metric.volume_comparison.C 3` (`Kakeya.ml1Boot.plankInTube_constant_bounds`).

The value is kept as an expression in `plankPigeonhole.C` and `Metric.volume_comparison.C 3`
and never collapsed to a numeral, so that a missing power of `C_𝕎` shows up here rather than
at a use site.  It depends only on the ambient dimension `3` and on `plankPigeonhole.C`; in
particular not on `δ̃`, `a`, `b`, `ρ`, `γ`, `j`, or the family. -/
noncomputable abbrev plankInTube.C : NNReal :=
  256 * plankPigeonhole.C ^ 6 * Metric.volume_comparison.C 3

/-- **The constant `C_{lem:ml1bootDensityTransfer}`** (blueprint
`def:ml1bootDensityTransferConstant`): the constant comparing a plank of dimensions
`a × b × 1` with the `2`-dilate of the `b`-tube that contains it.

Both the containment and the volume comparison it refers to are statements about
`Kakeya.Tube.dilate T_b 2` and not about `T_b`: that is what
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` supplies, containment of a plank in a
tube of *any* scale `O(b)` being false (blueprint `note:ml1bootPlankInTubeVacuous`).  The value
is therefore taken to be `Kakeya.ml1Boot.plankInTube.C` itself, which is exactly the constant
that lemma produces for the dilate and which already contains the factor `2 ^ 3` of
`Kakeya.Tube.tubeDilateVolume`.  The earlier value
`plankPigeonhole.C ^ 3 * Metric.volume_comparison.C 3 ^ 2` was too small by many orders of
magnitude; see blueprint `note:ml1bootDensityTransferConstantTooSmall`.

It depends only on the ambient dimension `3` and on `Kakeya.ml1Boot.plankPigeonhole.C`; in
particular not on `δ̃`, on `a`, on `b`, on `ρ`, on `γ`, on `j`, or on the family. -/
noncomputable abbrev densityTransfer.C : NNReal := plankInTube.C

/-- The density-transfer constant `C` is at least `1`. -/
theorem one_le_densityTransfer_C : (1 : NNReal) ≤ densityTransfer.C := by
  have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
    intro n
    have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      push_cast
      field_simp
    have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
      mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
      rw [hCval]
      nlinarith
    exact_mod_cast this
  dsimp [densityTransfer.C]
  have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C]
    exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
  exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 256) (one_le_pow₀ hCw))
    (one_le_volC 3)

/-- **The constant `C_{lem:ml1bootPlankTubeInParentDilate}`** (blueprint
`def:ml1bootPlankTubeParentDilateConstant`): the dilation factor `32 C_𝕎` by which a parent
`ρ`-tube has to be enlarged before it contains the tube attached to a plank inside it.

The value has been raised twice, and the reasons are worth keeping.  The original `3 C_𝕎` was
unjustified even for the undilated containment `W ⊆ Tb`: since
`Metric.ethickness ℝ W.carrier 0 ≥ 2⁻¹` gives only `diam W ≥ 2⁻¹`, an arbitrary tube `Tb` of
scale `C_𝕎 b` containing `W` is pinned to the parent axis only up to a chord angle, and the
transverse protrusion is bounded only by `5 ρ + 6 C_𝕎 ρ ≤ 11 C_𝕎 ρ`; blueprint
`note:auditPlankTubeInParentDilate` exhibits admissible data on which the `3 C_𝕎`-dilate is
genuinely left, so that form was false not a consequence of the hypotheses.  That recomputation then had to
be redone against the hypothesis the development can actually supply:
`Kakeya.ml1Boot.exists_plankTube_family` delivers only the *dilated* containment
`W ≤ Tube.dilate Tb 2`, the undilated one being unsatisfiable for these planks (blueprint
`note:ml1bootPlankInTubeStillFalse`), which roughly doubles every transverse quantity and gives
`ρ + 21 C_𝕎 ρ ≤ 22 C_𝕎 ρ`.  Longitudinally `Tb`'s core midpoint is offset by `O(1)`, not
`O(ρ)`, so `Tb` reaches `|⟪x, e⟫| ≤ 2 + ρ + 3 C_𝕎 ρ`, dominated by `c'/2 = 16 C_𝕎`; at
`c' = 1` the containment fails, so neither direction is free.  Both enlargements are free
downstream: every consumer uses nothing about `c'` beyond `1 ≤ ·`.

It depends only on the ambient dimension `3` and on `Kakeya.ml1Boot.plankPigeonhole.C`; in
particular not on `δ̃`, `a`, `b`, `ρ`, `γ`, `j`, or the family.  As elsewhere the value is
kept as an expression in `C_𝕎` and never collapsed to a closed numeral. -/
noncomputable abbrev plankTubeInParent.C : NNReal := 32 * plankPigeonhole.C

section DensityTransfer

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A plank with longitudinal spread at most `1` sits in the `2`-dilate of a comparable tube**
(blueprint `lem:ml1bootPlankInTubeRepaired`).

The hypothesis `hlong` is the *longitudinal normalization*.  The natural-looking form
`Metric.ethickness ℝ W.carrier 0 ≤ 2⁻¹` — which would give containment in `T_b` itself — is
*unsatisfiable* for the planks produced here: a plank is the convex hull of a block of
`δ̃`-tubes, each of which has a core segment of length exactly `1`
(`Kakeya.Tube.dist_eq_one`), so `Metric.ethickness ℝ W.carrier 0 ≥ 2⁻¹ + δ̃` always.  Refining
the blocks cannot help, since a block is a set of whole tubes.  The hypothesis below is
instead `≤ 1`, which is free: `W ⊆ B₁` already gives it, via
`Metric.ethickness_convexHullBiUnion_le`.

The price of the weaker hypothesis is paid on the conclusion side, in the containment only:
`W` lies in `Kakeya.Tube.dilate Tb 2`, whose core segment has length `2` and therefore covers
the range `|t₀| ≤ 1` that `hlong` allows, rather than in `Tb` itself.  The tube scale returns
to `C_𝕎 b`, and the volume comparison is for the dilate `|2 · Tb|`, which by
`Kakeya.Tube.tubeDilateVolume` is `2 ^ 3 |Tb|` and so still `∼ b ^ 2`; that is what keeps the
density transfer of `Kakeya.ml1Boot.frostmanConstIn_fibre_le` intact.  Downstream this
weakened containment is carried by `Kakeya.ml1Boot.IsParentFamilyDilate` at `c = 2`.

**The tube is located, and the location is exported.**  The witness is the explicit
`Kakeya.ml1Boot.plankTube` attached to `W`, so the construction-side bound
`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall` applies to it verbatim.  Without a clause
saying so the tube is opaque through the existential, and a consumer can recover a location only
from `W ≤ 2 · Tb` and the unit-ball hypothesis — that recovery is
`Kakeya.ml1Boot.carrier_subset_closedBall_of_le_dilate`, and it lands at the strictly coarser
radius `5 / 2 + 3 C_𝕎 b`.

*The exported radius is the parametric `3 / 2 + √3 + C_𝕎 b`, not the numeral `9 / 2`.*  The
sharp form `Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_of_le` needs `C_𝕎 b ≤ 1`, and
the hypotheses here give only `b ≤ 1`; since `C_𝕎 = 16 · Metric.volume_comparison.C 3` is far
larger than `1`, that side condition is **not** derivable and could only be added as a new
hypothesis, which would be a strengthening paid by every caller.  It is not added.  A caller
that does hold `C_𝕎 b ≤ 1` — the Section 8 route carries it as `hbq1` — gets the `9 / 2` form
out of the clause below in two lines, by `√3 ≤ 2` and
`Metric.closedBall_subset_closedBall`, so nothing is lost and no hypothesis is spent by callers
that do not need it.

This is also why `hW` is named rather than the discarded `_hW` of an earlier version: it is
exactly what `Kakeya.ml1Boot.plankTube_carrier_subset_closedBall` consumes. -/
theorem exists_plank_tube_of_thickness_le_one_located [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {a b : NNReal} (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (W : ConvexSpaceBody E) (hW : W.carrier ⊆ Metric.closedBall 0 1)
    (hdims : IsPlankOfDimensions plankPigeonhole.C a b W)
    (hlong : Metric.ethickness ℝ W.carrier 0 ≤ 1) :
    ∃ Tb : Tube (plankPigeonhole.C * b) E, W ≤ Tube.dilate Tb 2 ∧
      Tb.carrier ⊆ Metric.closedBall (0 : E)
          (3 / 2 + Real.sqrt 3 + ((plankPigeonhole.C * b : NNReal) : ℝ)) ∧
      (plankInTube.C : ENNReal)⁻¹ * ((b : ENNReal) / (a : ENNReal))
          * volume W.carrier ≤ volume (Tube.dilate Tb 2).carrier ∧
        volume (Tube.dilate Tb 2).carrier ≤ (plankInTube.C : ENNReal)
          * ((b : ENNReal) / (a : ENNReal)) * volume W.carrier := by
  classical
  have hCw : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 < plankPigeonhole.C := lt_of_lt_of_le zero_lt_one hCw
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  -- the witness
  have hWcomp : IsCompact W.carrier := W.isCompact'
  have hWne : W.carrier.Nonempty := W.nonempty'
  let Tb : Tube (plankPigeonhole.C * b) E := plankTube hdim plankPigeonhole.C b hWcomp hWne
  -- the three affine-thickness bounds, read off the ethickness bounds through
  -- Metric.toReal_ethickness (W.carrier is bounded, being compact)
  have hbdd : Bornology.IsBounded W.carrier := hWcomp.isBounded
  have hτ₀ : Metric.thickness ℝ W.carrier 0 ≤ 1 := by
    have htop : Metric.ethickness ℝ W.carrier 0 ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hlong (by simp : (1 : ENNReal) < ⊤))
    have htoReal : ENNReal.toReal (Metric.ethickness ℝ W.carrier 0) ≤
        ENNReal.toReal (1 : ENNReal) :=
      (ENNReal.toReal_le_toReal htop (by simp)).mpr hlong
    calc
      Metric.thickness ℝ W.carrier 0 = ENNReal.toReal (Metric.ethickness ℝ W.carrier 0) :=
        (Metric.toReal_ethickness hbdd 0).symm
      _ ≤ ENNReal.toReal (1 : ENNReal) := htoReal
      _ = 1 := by simp
  have hτ₁ : Metric.thickness ℝ W.carrier 1 ≤ (plankPigeonhole.C : ℝ) * (b : ℝ) := by
    have hleEN : Metric.ethickness ℝ W.carrier 1 ≤
        (plankPigeonhole.C : ENNReal) * (b : ENNReal) := hdims.2.1.2
    have htop : Metric.ethickness ℝ W.carrier 1 ≠ ⊤ := by
      have hle_top : (plankPigeonhole.C : ENNReal) * (b : ENNReal) < ⊤ :=
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
      exact ne_of_lt (lt_of_le_of_lt hleEN hle_top)
    have htoReal : ENNReal.toReal (Metric.ethickness ℝ W.carrier 1) ≤
        ENNReal.toReal ((plankPigeonhole.C : ENNReal) * (b : ENNReal)) :=
      (ENNReal.toReal_le_toReal htop
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)).mpr hleEN
    calc
      Metric.thickness ℝ W.carrier 1 = ENNReal.toReal (Metric.ethickness ℝ W.carrier 1) :=
        (Metric.toReal_ethickness hbdd 1).symm
      _ ≤ ENNReal.toReal ((plankPigeonhole.C : ENNReal) * (b : ENNReal)) := htoReal
      _ = (plankPigeonhole.C : ℝ) * (b : ℝ) := by
        rw [← ENNReal.coe_mul]
        simp [NNReal.coe_mul]
  have hτ₂ : Metric.thickness ℝ W.carrier 2 ≤ (plankPigeonhole.C : ℝ) * (b : ℝ) := by
    have hleEN : Metric.ethickness ℝ W.carrier 2 ≤
        (plankPigeonhole.C : ENNReal) * (b : ENNReal) := by
      calc
        Metric.ethickness ℝ W.carrier 2 ≤ (plankPigeonhole.C : ENNReal) * (a : ENNReal) :=
          hdims.2.2.2
        _ ≤ (plankPigeonhole.C : ENNReal) * (b : ENNReal) := by
          gcongr
    have htop : Metric.ethickness ℝ W.carrier 2 ≠ ⊤ := by
      have hle_top : (plankPigeonhole.C : ENNReal) * (b : ENNReal) < ⊤ :=
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top
      exact ne_of_lt (lt_of_le_of_lt hleEN hle_top)
    have htoReal : ENNReal.toReal (Metric.ethickness ℝ W.carrier 2) ≤
        ENNReal.toReal ((plankPigeonhole.C : ENNReal) * (b : ENNReal)) :=
      (ENNReal.toReal_le_toReal htop
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)).mpr hleEN
    calc
      Metric.thickness ℝ W.carrier 2 = ENNReal.toReal (Metric.ethickness ℝ W.carrier 2) :=
        (Metric.toReal_ethickness hbdd 2).symm
      _ ≤ ENNReal.toReal ((plankPigeonhole.C : ENNReal) * (b : ENNReal)) := htoReal
      _ = (plankPigeonhole.C : ℝ) * (b : ℝ) := by
        rw [← ENNReal.coe_mul]
        simp [NNReal.coe_mul]
  -- containment of W in the 2-dilate of the tube
  have hsub : W.carrier ⊆ (Tube.dilate Tb 2).carrier := by
    simpa [Tb] using
      subset_plankTube hdim plankPigeonhole.C b (Λ₀ := (1 : ℝ)) le_rfl hWcomp hWne hτ₀ hτ₁ hτ₂
  have hcontainW : W ≤ Tube.dilate Tb 2 := by
    exact SetLike.coe_subset_coe.mpr hsub
  -- the two volume bounds of W
  have hvolW := volume_bounds_of_isPlankOfDimensions hdim hCw hdims
  -- the two volume bounds of the 2-dilate of the tube of scale Cw * b
  have hs0 : 0 < plankPigeonhole.C * b := by positivity
  have hs : plankPigeonhole.C * b ≤ 2 * plankPigeonhole.C := by
    calc
      plankPigeonhole.C * b ≤ plankPigeonhole.C * 1 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) hCw0.le
      _ = plankPigeonhole.C := by rw [mul_one]
      _ ≤ 2 * plankPigeonhole.C := by
        calc
          plankPigeonhole.C = 1 * plankPigeonhole.C := by rw [one_mul]
          _ ≤ 2 * plankPigeonhole.C :=
            mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 2) hCw0.le
  have hvolT := volume_bounds_of_tube_dilate hdim hCw hs0 hs Tb
  have hsq : ((plankPigeonhole.C * b : NNReal) : ENNReal) ^ 2
      = (plankPigeonhole.C : ENNReal) ^ 2 * (b : ENNReal) ^ 2 := by
    rw [ENNReal.coe_mul]
    ring
  have hVlo : 4 * (Metric.lt_volume_convexHull.c 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
      * (b : ENNReal) ^ 2 ≤ volume (Tube.dilate Tb 2).carrier := by
    calc
      4 * (Metric.lt_volume_convexHull.c 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
            * (b : ENNReal) ^ 2
        = 4 * (Metric.lt_volume_convexHull.c 3 : ENNReal)
            * ((plankPigeonhole.C * b : NNReal) : ENNReal) ^ 2 := by
          rw [hsq]
          ring
      _ ≤ volume (Tube.dilate Tb 2).carrier := hvolT.1
  have hVhi : volume (Tube.dilate Tb 2).carrier ≤ 320 * (plankPigeonhole.C : ENNReal) ^ 3
      * (b : ENNReal) ^ 2 := by
    calc
      volume (Tube.dilate Tb 2).carrier
          ≤ 320 * (plankPigeonhole.C : ENNReal)
              * ((plankPigeonhole.C * b : NNReal) : ENNReal) ^ 2 := hvolT.2
      _ = 320 * (plankPigeonhole.C : ENNReal) ^ 3 * (b : ENNReal) ^ 2 := by
        rw [hsq]
        ring
  -- the constant requirements 2 Cw / c₃ ≤ C and 320 Cw⁶ / c₃ ≤ C (C = plankInTube.C)
  have hC : 1 ≤ plankInTube.C := by
    dsimp [plankInTube.C]
    have hp : (1 : NNReal) ≤ plankPigeonhole.C ^ 6 :=
      le_trans hCw (by simpa using pow_le_pow_right₀ hCw (by norm_num : 1 ≤ 6))
    have hv : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    calc
      (1 : NNReal) ≤ 256 := by norm_num
      _ ≤ 256 * (plankPigeonhole.C ^ 6 * Metric.volume_comparison.C 3) := by
        exact le_mul_of_one_le_right (by norm_num) (one_le_mul hp hv)
      _ = 256 * plankPigeonhole.C ^ 6 * Metric.volume_comparison.C 3 := by ring
  obtain ⟨hC₂, hC₁⟩ := plankInTube_constant_bounds (C := plankPigeonhole.C) hCw
  -- feed the four volume bounds and the two constant requirements into the ratio lemma
  have hratio := plank_dilate_volume_ratio
    (Cw := plankPigeonhole.C) (C := plankInTube.C) (a := a) (b := b)
    (w := volume W.carrier) (V := volume (Tube.dilate Tb 2).carrier)
    hCw hC ha0 hab hvolW.1 hvolW.2 hVlo hVhi hC₁ hC₂
  -- the location of the witness, read off the explicit construction
  have hloc : Tb.carrier ⊆ Metric.closedBall (0 : E)
      (3 / 2 + Real.sqrt 3 + ((plankPigeonhole.C * b : NNReal) : ℝ)) := by
    simpa [Tb] using
      plankTube_carrier_subset_closedBall hdim plankPigeonhole.C b hWcomp hWne hW
  exact ⟨Tb, hcontainW, hloc, hratio.1, hratio.2⟩

/-- **A plank with longitudinal spread at most `1` sits in the `2`-dilate of a comparable tube**
(blueprint `lem:ml1bootPlankInTubeRepaired`), with the tube's location forgotten.

This is `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one_located` with its location clause
dropped, and it is the form the existing consumers destructure.  Prefer the located form in new
code: the tube it hands back is the same one, and the extra clause is exactly what lets a
consumer avoid re-deriving a location generically through the existential at the coarser radius
of `Kakeya.ml1Boot.carrier_subset_closedBall_of_le_dilate`. -/
theorem exists_plank_tube_of_thickness_le_one [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {a b : NNReal} (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (W : ConvexSpaceBody E) (hW : W.carrier ⊆ Metric.closedBall 0 1)
    (hdims : IsPlankOfDimensions plankPigeonhole.C a b W)
    (hlong : Metric.ethickness ℝ W.carrier 0 ≤ 1) :
    ∃ Tb : Tube (plankPigeonhole.C * b) E, W ≤ Tube.dilate Tb 2 ∧
      (plankInTube.C : ENNReal)⁻¹ * ((b : ENNReal) / (a : ENNReal))
          * volume W.carrier ≤ volume (Tube.dilate Tb 2).carrier ∧
        volume (Tube.dilate Tb 2).carrier ≤ (plankInTube.C : ENNReal)
          * ((b : ENNReal) / (a : ENNReal)) * volume W.carrier := by
  obtain ⟨Tb, hcont, -, hlo, hhi⟩ :=
    exists_plank_tube_of_thickness_le_one_located hdim ha0 hab hb1 W hW hdims hlong
  exact ⟨Tb, hcont, hlo, hhi⟩

/-- **A Frostman constant from a uniform density comparison** (blueprint
`lem:ml1bootFibreFrostmanIn`).

If `Δ(𝕍, K) ≤ 𝒞 Δ(𝕍, B)` for *every* convex body `K ⊆ B`, then `C_F(𝕍[B], B) ≤ 𝒞`.

This is `ConvexSpaceBody.frostmanConstIn_le` together with the observation that the density
comparison is exactly the defining property of `ConvexSpaceBody.IsFrostmanIn`; it is stated
separately because the density comparison is what
`Kakeya.ml1Boot.density_dilate_ge` produces and the Frostman constant is what
`Kakeya.ml1Boot.frostmanConstIn_fibre_le` consumes.  Nothing about tubes, scales or planks
enters.

**No normalization `1 ≤ 𝒞` is required.**  An earlier version carried one, on the ground that
a Frostman constant ought to be at least `1`; it was never used — neither here nor inside
`ConvexSpaceBody.frostmanConstIn_le` — and it has been dropped, together with the hypothesis
it forced on `Kakeya.ml1Boot.frostmanConstIn_anchor_le`. -/
theorem frostmanConstIn_le_of_density_le {ι : Type*} {s : Finset ι}
    (V : ι → ConvexSpaceBody E) (B : ConvexSpaceBody E) {C : ENNReal}
    (hdens : ∀ K : ConvexSpaceBody E, K ≤ B → densityIn s V K ≤ C * densityIn s V B) :
    frostmanConstIn (familyIn s V B) V B ≤ C := by
  have hfam : ∀ K : ConvexSpaceBody E, K ≤ B →
      densityIn (familyIn s V B) V K = densityIn s V K := by
    intro K hK
    unfold familyIn
    rw [densityIn_eq_densityIn_filter]
    rw [Finset.filter_filter]
    rw [show s.filter (fun i => V i ≤ B ∧ V i ≤ K) = s.filter (fun i => V i ≤ K) by
      apply Finset.filter_congr
      intro i hi
      constructor
      · intro h; exact h.2
      · intro hVKi
        exact ⟨le_trans hVKi hK, hVKi⟩]
    rw [(densityIn_eq_densityIn_filter (s := s) (W := V) (K := K)).symm]
  apply frostmanConstIn_le
  change ∀ K' : ConvexSpaceBody E, K' ≤ B →
    densityIn (familyIn s V B) V K' ≤ C * densityIn (familyIn s V B) V B
  rw [hfam B le_rfl]
  intro K' hK'
  rw [hfam K' hK']
  exact hdens K' hK'

/-- **A density is unchanged by restricting to a subfamily that catches everything** (blueprint
`lem:ml1bootFibreDensityEq`).

Let `𝕍 = (V_i)_{i ∈ s}` be a finite family of convex bodies, let `s₀ ⊆ s` and let `K` be a
convex body caught entirely by `s₀`, i.e. `𝕍[K] ⊆ s₀`.  Then `Δ(𝕍, K) = Δ(𝕍|_{s₀}, K)`.

Both sides are the same quotient: the two index sets `𝕍[K]` and `𝕍|_{s₀}[K] = 𝕍[K] ∩ s₀`
agree, by `hcatch` in one direction and by `s₀ ⊆ s` in the other, so the numerators coincide
and the denominator `|K|` is the same.

Nothing about tubes, scales or planks enters; the lemma is stated here because it is what
`Kakeya.ml1Boot.densityIn_le_of_fibre_inclusion` uses to replace `𝕋̃''` by the fibre over `m`
inside the `2`-dilate of a `b`-tube. -/
theorem densityIn_eq_of_familyIn_subset {ι : Type*} {s s₀ : Finset ι}
    (V : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) (hs₀ : s₀ ⊆ s)
    (hcatch : familyIn s V K ⊆ s₀) :
    densityIn s V K = densityIn s₀ V K := by
  classical
  rw [densityIn_eq_densityIn_filter]
  rw [densityIn_eq_densityIn_filter s₀ V K]
  have hsets : {i ∈ s | V i ≤ K} = {i ∈ s₀ | V i ≤ K} := by
    unfold familyIn at hcatch
    exact Finset.Subset.antisymm
      (by
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hcatch (Finset.mem_filter.mpr ⟨hi.1, hi.2⟩), hi.2⟩)
      (by
        intro i hi
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hs₀ hi.1, hi.2⟩)
  rw [hsets]

/-- **The density of a block inside an arbitrary body containing its plank** (blueprint
`lem:ml1bootBlockDensityLower`).

Let `a, b > 0`, let `𝔽 = (T̃_k)_{k ∈ v}` be a family of `δ̃`-tubes, let `t ⊆ v` be a nonempty
block whose plank `W = conv (⋃_{k ∈ t} T̃_k)` captures exactly `t`, i.e. `𝔽[W] = t`, and let
`B` be an **arbitrary** convex body with `W ⊆ B` and `|B| ≤ C_T (b/a) |W|`.  Then for *any*
enlargement `𝕍 = (T̃_k)_{k ∈ u''}` of `𝔽`,

`Δ(𝕍, B) ≥ C_T⁻¹ (a/b) Δ(𝔽, W)`,

where `C_T = Kakeya.ml1Boot.densityTransfer.C`.

Only two facts are used: the numerator of `Δ(𝕍, B)` sums over a superset of `t`, every `T̃_k`
with `k ∈ t` lying in `W ⊆ B`; and the denominator is smaller than `C_T (b/a) |W|`.  Neither
uses anything about the shape of `B`, which is why the body is free.

The body is arbitrary and no dilation factor appears here: whatever dilation a caller's choice
of `B` costs has already been paid inside the constant it verifies the volume comparison with.
The `2`-dilate `B = 2 · T_b` of a `b`-tube is **one instantiation, supplied by the caller** —
that is how `Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate` reads it, the tube attached to
a plank containing it only after dilation (blueprint `def:ml1bootParentFamilyDilate`).  The
anchor `K` of `Kakeya.ml1Boot.frostmanConstIn_anchor_le` is another, of a different shape, and
it is only because the body is free that no transport between the two is needed.

The widths enter only through the ratio `b/a`, and only through its cancellation against
`a/b`, so all that is asked of them is `0 < a` and `0 < b`.  Earlier versions asked for
`0 < a ≤ b ≤ 1`: the normalization `b ≤ 1` was used nowhere and `a ≤ b` only to produce
`0 < b`. -/
theorem density_dilate_ge [Nontrivial E] (_hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hap0 : 0 < ap) (hbp0 : 0 < bp)
    {ι : Type*} {v t u'' : Finset ι} (T : ι → Tube δt E)
    (htv : t ⊆ v) (_htne : t.Nonempty) (hvu : v ⊆ u'')
    (hcapture : familyIn v (fun k => (T k).toConvexSpaceBody)
        (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody) = t)
    (B : ConvexSpaceBody E)
    (hW : (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody) ≤ B)
    (hvol : volume B.carrier
      ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal))
        * volume (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody).carrier) :
    (densityTransfer.C : ENNReal)⁻¹ * ((ap : ENNReal) / (bp : ENNReal))
          * densityIn v (fun k => (T k).toConvexSpaceBody)
              (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody)
        ≤ densityIn u'' (fun k => (T k).toConvexSpaceBody) B := by
  classical
  let V : ι → ConvexSpaceBody E := fun k => (T k).toConvexSpaceBody
  let W : ConvexSpaceBody E := t.convexHull_biUnion V
  let C : ENNReal := (densityTransfer.C : ENNReal)
  let r : ENNReal := (ap : ENNReal) / (bp : ENNReal)
  let d : ENNReal := densityIn v V W
  let D : ENNReal := densityIn u'' V B
  change C⁻¹ * r * d ≤ D
  by_cases hB0 : volume B.carrier = 0
  · have hW0 : volume W.carrier = 0 := measure_mono_null hW hB0
    have hd0 : d = 0 := densityIn_eq_zero_of_volume_eq_zero hW0
    rw [hd0]
    simp
  · have hsub : t ⊆ u''.filter (fun k => V k ≤ B) := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨hvu (htv hk), le_trans (Finset.le_convexHull_biUnion V hk) hW⟩
    have hnum : (∑ k ∈ t, volume (V k).carrier) ≤
        (∑ k ∈ u'' with V k ≤ B, volume (V k).carrier) :=
      Finset.sum_le_sum_of_subset hsub
    have h1 : (∑ k ∈ t, volume (V k).carrier) = d * volume W.carrier := by
      rw [← hcapture]
      unfold familyIn
      exact Kakeya.sum_volume_eq_densityIn_mul_volume v V W
    have h2 : (∑ k ∈ u'' with V k ≤ B, volume (V k).carrier) =
        D * volume B.carrier :=
      Kakeya.sum_volume_eq_densityIn_mul_volume u'' V B
    have hkey : d * volume W.carrier ≤ D * volume B.carrier := by
      rw [← h1, ← h2]
      exact hnum
    have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
      intro n
      have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
        dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
        push_cast
        field_simp
      have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
        mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
      have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
        rw [hCval]
        nlinarith
      exact_mod_cast this
    have hCpl : (1 : NNReal) ≤ plankInTube.C := by
      dsimp [plankInTube.C]
      have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
        dsimp [plankPigeonhole.C]
        exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
      exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 256) (one_le_pow₀ hCw))
        (one_le_volC 3)
    have hCne0 : C ≠ 0 := by
      dsimp [C, densityTransfer.C]
      exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCpl))
    have hCtet : C ≠ ⊤ := by
      dsimp [C, densityTransfer.C]
      exact ENNReal.coe_ne_top
    have hCinv : C⁻¹ * C = 1 := ENNReal.inv_mul_cancel hCne0 hCtet
    have ha0 : (ap : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hap0)
    have hb0 : (bp : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hbp0)
    have hratio : ((ap : ENNReal) / (bp : ENNReal)) * ((bp : ENNReal) / (ap : ENNReal)) = 1 := by
      rw [← ENNReal.mul_div_mul_comm (Or.inl hb0) (Or.inr ha0)]
      rw [mul_comm (bp : ENNReal) (ap : ENNReal)]
      exact ENNReal.div_self (mul_ne_zero ha0 hb0)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    have hstep : C⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) *
        (C * ((bp : ENNReal) / (ap : ENNReal))) = 1 := by
      calc
        C⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) * (C * ((bp : ENNReal) / (ap : ENNReal)))
            = (C⁻¹ * C) *
                (((ap : ENNReal) / (bp : ENNReal)) * ((bp : ENNReal) / (ap : ENNReal))) := by
              ring
        _ = 1 := by
          rw [hCinv, hratio, one_mul]
    have hmain : C⁻¹ * r * d * volume B.carrier ≤ D * volume B.carrier := by
      calc
        C⁻¹ * r * d * volume B.carrier
            ≤ C⁻¹ * r * d * (C * ((bp : ENNReal) / (ap : ENNReal)) * volume W.carrier) := by
              exact mul_le_mul_of_nonneg_left hvol zero_le
        _ = d * volume W.carrier := by
          dsimp [r]
          calc
            C⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) * d
                * (C * ((bp : ENNReal) / (ap : ENNReal)) * volume W.carrier)
                = (C⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) *
                    (C * ((bp : ENNReal) / (ap : ENNReal)))) * (d * volume W.carrier) := by
                  ring
            _ = d * volume W.carrier := by
              rw [hstep]
              rw [one_mul]
        _ ≤ D * volume B.carrier := hkey
    have hmain' : volume B.carrier * (C⁻¹ * r * d) ≤ volume B.carrier * D := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    exact (ENNReal.mul_le_mul_iff_right hB0 B.isCompact.measure_ne_top).mp hmain'

/-- The `ENNReal` cancellation `(c * (y / x) * (u / l)) * (c⁻¹ * (x / y) * l) = u`: the two
ratios `y / x` and `x / y` cancel, `c * c⁻¹ = 1`, and `(u / l) * l = u`. -/
theorem anchor_ratio_cancel {c x y l u : ENNReal}
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (hx0 : x ≠ 0) (hxtop : x ≠ ⊤)
    (hy0 : y ≠ 0) (hytop : y ≠ ⊤) (hl0 : l ≠ 0) (hltop : l ≠ ⊤) :
    (c * (y / x) * (u / l)) * (c⁻¹ * (x / y) * l) = u := by
  have hcinv : c * c⁻¹ = 1 := ENNReal.mul_inv_cancel hc0 hctop
  have hratio : (y / x) * (x / y) = 1 := by
    rw [← ENNReal.mul_div_mul_comm (Or.inl hx0) (Or.inr hy0)]
    rw [mul_comm y x]
    exact ENNReal.div_self (mul_ne_zero hx0 hy0)
      (ENNReal.mul_ne_top hxtop hytop)
  have hdiv : (u / l) * l = u := ENNReal.div_mul_cancel hl0 hltop
  calc
    (c * (y / x) * (u / l)) * (c⁻¹ * (x / y) * l)
        = (c * c⁻¹) * ((y / x) * (x / y)) * ((u / l) * l) := by
          ring
    _ = 1 * 1 * ((u / l) * l) := by
          rw [hcinv, hratio]
    _ = 1 * 1 * u := by
          rw [hdiv]
    _ = u := by
          ring

/-- **A plank captures exactly its own block.**  For any finite index set `t` and any family `V`,
the subfamily of `V|_t` contained in the plank `W = conv (⋃_{k ∈ t} V k)` of `t` is all of `t`.

This is the `hcapture` display of the denominator group of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`, and it is the reason that group's bundle
`Kakeya.ml1Boot.IsAnchorPlacement` does not carry it as a field: it is automatic.  Each `V k` with
`k ∈ t` lies in the convex hull of the union over `t`, by `Finset.le_convexHull_biUnion`, so the
predicate defining `Kakeya.familyIn` holds on all of `t`.

Nothing is asked of `V`, of `t` — not even nonemptiness — or of the ambient space beyond what
`Kakeya.familyIn` needs. -/
theorem familyIn_convexHull_biUnion_self {ι : Type*} (t : Finset ι) (V : ι → ConvexSpaceBody E) :
    familyIn t V (t.convexHull_biUnion V) = t :=
  Finset.filter_true_of_mem fun k hk => t.le_convexHull_biUnion V hk

/-- **The anchor placement of a block** (blueprint `def:ml1bootAnchorPlacement`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  For a family `𝕍 = (T̃_k)_{k ∈ s'}` of
`δ̃`-tubes, a convex body `K` — the **anchor** — and widths `ã, b̃ > 0`, a finite index set `t`
is an *anchor placement* for `(𝕍, K, ã, b̃)` if, with `W = conv (⋃_{k ∈ t} T̃_k)` the plank of
the block `t`, it satisfies `t ⊆ s'`, `t` is nonempty, `W ≤ K`, and `|K| ≤ C_T (b̃/ã) |W|`.

*This is a bundle and not a new hypothesis.*  The four fields are, verbatim, the standing
conditions on `t` and the second and third displays of the denominator hypothesis of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`.  Nothing is added, nothing is strengthened, and no
constant is introduced: `C_T` is the one of `Kakeya.ml1Boot.densityTransfer.C`, already carried
by every statement that displays this group.

The ambient index set is the *parameter* `s'` rather than being fixed to the family's own
index type, because the group is read at two different ambients: at `t ⊆ u''` by
`Kakeya.ml1Boot.frostmanConstIn_anchor_le`, whose numerator is asserted at `u''`, and at
`t ⊆ s'` with a separate `s' ⊆ u''` by
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` and its callers.

*The capture `𝕍|_t[W] = t` is deliberately not a field.*  It is derivable — every `T̃_k` with
`k ∈ t` lies in the convex hull `W` of their union, so all of `t` is caught — and putting it here
would carry a step of a proof in the data.  That derivation is
`Kakeya.ml1Boot.familyIn_convexHull_biUnion_self`, and it is what every consumer of this bundle
now uses in place of the former `hcapture` binder.

`block_nonempty` is carried but unused, in the idiom of
`Kakeya.ml1Boot.density_dilate_ge`, which binds it as the unused `_htne`.  It is what makes `t`
a *block*, and every site holds it.

*The widths are unconstrained here, and `volume_le` is vacuous at `ap = 0`.*  In `ℝ≥0∞` the
ratio `bp/ap` is `⊤` when `ap = 0 < bp`, so `volume_le` then says only `|K| ≤ ⊤`.  The pair
`0 < ap ≤ bp` is therefore **not** a field: it is not what makes this bundle a placement, it is
what the *arithmetic* of the consumers needs — `Kakeya.ml1Boot.frostmanConstIn_anchor_le` spends
it on cancelling `C_T (bp/ap)` against `C_T⁻¹ (ap/bp)` — and every consumer carries it as its own
`hap0`, `hab`.  Bundling it here would put a hypothesis of the conclusion into the hypothesis of
the placement, and would make this predicate false in the degenerate case rather than vacuous,
which is a strengthening. -/
structure IsAnchorPlacement {ι : Type*} {δt : NNReal} (T : ι → Tube δt E)
    (K : ConvexSpaceBody E) (ap bp : NNReal) (s' t : Finset ι) : Prop where
  /-- The block lies in the ambient index set. -/
  block_subset : t ⊆ s'
  /-- The block is nonempty; this is what makes `t` a block. -/
  block_nonempty : t.Nonempty
  /-- The plank of the block lies inside the anchor. -/
  plank_le : (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody) ≤ K
  /-- The anchor has volume at most `C_T (b̃/ã)` times that of the plank of the block. -/
  volume_le : volume K.carrier ≤ (densityTransfer.C : ENNReal)
    * ((bp : ENNReal) / (ap : ENNReal))
    * volume (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody).carrier

/-- **The anchor denominator at a block** (blueprint `def:ml1bootAnchorDenominator`).

In the situation of `Kakeya.ml1Boot.IsAnchorPlacement`, and with
`W = conv (⋃_{k ∈ t} T̃_k)` the plank of `t` as there, a pair `(t, L)` with `L : ℝ≥0∞` is an
*anchor denominator* for `(𝕍, K, ã, b̃)` if `t` is an anchor placement for `(𝕍, K, ã, b̃)`,
`0 < L`, and `L ≤ Δ(𝕍|_t, W)`.

*This is the denominator hypothesis of `Kakeya.ml1Boot.frostmanConstIn_anchor_le` and nothing
else.*  The placement is one field of it and the two displays above are the other two.

*`L ≠ ⊤` is deliberately not a field.*  What the proof of that lemma needs of the denominator is
`0 < L < ∞`, the identity `(U/L) * L = U` failing at `L = ⊤` in `ℝ≥0∞`; but finiteness follows
from `denom_le` alone, by
`L ≤ Δ(𝕍|_t, W) ≤ Δ_max(𝕍|_t) ≤ |t| < ∞`, that is `Kakeya.le_maxDensity` followed by
`Kakeya.maxDensity_le_card`, the block `t` being finite.  That derivation is
`Kakeya.ml1Boot.IsAnchorDenominator.denom_ne_top`, and it is what the consumers now use in place
of the former `hLtop` binder.  Dropping that binder does not change what
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` proves: its former form is the instance of the present
one at a caller who happens to hold `L ≠ ⊤`.

Six of the eight sites that display the anchor group hold this bundle entire; the two that
manufacture their own denominator out of a count —
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization` and
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count` — hold
`Kakeya.ml1Boot.IsAnchorPlacement` only.  That is the reason for two bundles rather than
one. -/
structure IsAnchorDenominator {ι : Type*} {δt : NNReal} (T : ι → Tube δt E)
    (K : ConvexSpaceBody E) (ap bp : NNReal) (s' t : Finset ι) (L : ENNReal) : Prop
    extends IsAnchorPlacement T K ap bp s' t where
  /-- The denominator is positive. -/
  denom_pos : 0 < L
  /-- The denominator is a lower bound for the density of the block at its own plank. -/
  denom_le : L ≤ densityIn t (fun k => (T k).toConvexSpaceBody)
    (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody)

/-- **An anchor denominator is finite.**  `L ≤ Δ(𝕍|_t, W) ≤ Δ_max(𝕍|_t) < ∞`, the last step being
`Kakeya.maxDensity_ne_top`, which holds because the block `t` is a finite set.

This is why `Kakeya.ml1Boot.IsAnchorDenominator` does not carry `L ≠ ⊤` as a field even though
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` needs it: the finiteness is a consequence of
`denom_le`, not an extra demand on the caller. -/
theorem IsAnchorDenominator.denom_ne_top {ι : Type*} {δt : NNReal} {T : ι → Tube δt E}
    {K : ConvexSpaceBody E} {ap bp : NNReal} {s' t : Finset ι} {L : ENNReal}
    (h : IsAnchorDenominator T K ap bp s' t L) : L ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (maxDensity_ne_top t (fun k => (T k).toConvexSpaceBody)) ?_
  exact h.denom_le.trans
    (le_maxDensity t (fun k => (T k).toConvexSpaceBody)
      (t.convexHull_biUnion fun k => (T k).toConvexSpaceBody))

/-- **(GWZ (5.10b)) The Frostman constant of the unrefined node family at the anchor**
(blueprint `lem:ml1bootAnchorFrostmanUpper`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  Let `𝕍 = (T̃_k)_{k ∈ u''}` be a family of
`δ̃`-tubes, let `K` be a convex body — the **anchor** — and let `0 < a ≤ b`.  Assume

* *the numerator* `hnum` — a uniform upper bound `Δ(𝕍, K') ≤ U` for every convex `K' ⊆ K`;
* *the denominator* `hanch` — a `Kakeya.ml1Boot.IsAnchorDenominator`: a nonempty block `t ⊆ u''`
  whose plank `W = conv (⋃_{k ∈ t} T̃_k)` lies in `K` and satisfies `|K| ≤ C_T (b/a) |W|`,
  together with `0 < L ≤ Δ(𝕍|_t, W)`.

Then `C_F(𝕍[K], K) ≤ C_T (b/a) U / L`.

This is the ratio (5.10b) of the source's Step 5c and nothing beyond it.  Both `U` and `L`
are **hypotheses**: no instantiation of either is performed here, and in particular this is
not a claim that (5.10b)'s numerical form `δ ^ (-ε') δ̃ ^ (-η_m) (b/a)` has been checked.

The anchor is **arbitrary**, and that is what makes the statement usable: it is not required
to be a tube, a dilate of one, or a concentric rescaling of one.  It enters only through the
quantifier `K' ≤ K` of `hnum`, through `hWK` and `hvol`, and through the filter `𝕍[K]`.  This
is exactly the freedom `Kakeya.ml1Boot.density_dilate_ge` was restated to provide; the source
reads it at the concentric rescaling `T̃_0 ^ (C₀ b̃)`, while
`Kakeya.ml1Boot.plankWidth_le_of_anchor` reads it at `2 · T_b`, the body the collision of
`Kakeya.ml1Boot.plankWidth_le` is actually run at, and no transport between the two shapes is
needed.

The family `𝕍` is *meant* to be the unrefined level-`b` node family `𝕋̃^♮`, so that `𝕍[K]` is
the source's `𝒩⁺ = {T ∈ 𝕋̃^♮ : T ⊆ K}`; the retained share enters only through the block `t`,
on the denominator side, where `𝕍 ⊇ 𝕍|_t` can only help.  That is the whole reason for
stating the upper bound this way rather than through the plank-in-tube chain
`Kakeya.ml1Boot.frostmanConstIn_fibre_le`, whose conclusion is about `𝕋̃''`: the collision of
`Kakeya.ml1Boot.plankWidth_le` needs both sides at one and the same family, and the lower side
is asserted only at the unrefined family.  Nothing in the statement forces `𝕍` to be that
family, so the identification is the caller's and is not a claim of this lemma.

The denominator group is taken as the single bundle `Kakeya.ml1Boot.IsAnchorDenominator` rather
than as six binders, and the two binders an earlier form carried alongside it are now discharged
inside the proof: the capture `𝕍|_t[W] = t` by
`Kakeya.ml1Boot.familyIn_convexHull_biUnion_self`, and the finiteness `L ≠ ⊤` — the Lean-side
condition, with no counterpart in the informal `L > 0`, that together with `denom_pos` lets
`(U / L) * L = U` be run in `ENNReal` — by
`Kakeya.ml1Boot.IsAnchorDenominator.denom_ne_top`.  Neither was ever a genuine assumption, and
their removal weakens the hypotheses of this lemma.

**There is no normalization hypothesis `1 ≤ C_T (b/a) U / L`.**  An earlier version carried
one, on the ground that `Kakeya.ml1Boot.frostmanConstIn_le_of_density_le` stated its constant
at `𝒞 ≥ 1`; that lemma never used the normalization and no longer asks for it, so the
hypothesis has been dropped here as well.  It is also unnecessary for the conclusion to be
meaningful: `frostmanConstIn` is an infimum, and the bound below is simply whatever the ratio
is.

The proof is `Kakeya.ml1Boot.density_dilate_ge` at `v = t` and `B = K`, giving
`Δ(𝕍, K) ≥ C_T⁻¹ (a/b) L`, followed by `Kakeya.ml1Boot.frostmanConstIn_le_of_density_le` at
`𝒞 = C_T (b/a) U / L`; the two constants cancel because `C_T` and both widths are positive and
finite, and `(U/L) * L = U` because of `denom_pos` and `denom_ne_top`. -/
theorem frostmanConstIn_anchor_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp)
    {ι : Type*} {u'' t : Finset ι} (T : ι → Tube δt E) (K : ConvexSpaceBody E)
    {U L : ENNReal}
    (hnum : ∀ K' : ConvexSpaceBody E, K' ≤ K →
      densityIn u'' (fun k => (T k).toConvexSpaceBody) K' ≤ U)
    (hanch : IsAnchorDenominator T K ap bp u'' t L) :
    frostmanConstIn (familyIn u'' (fun k => (T k).toConvexSpaceBody) K)
          (fun k => (T k).toConvexSpaceBody) K
        ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (U / L) := by
  classical
  have htu : t ⊆ u'' := hanch.block_subset
  have htne : t.Nonempty := hanch.block_nonempty
  have hWK := hanch.plank_le
  have hvol := hanch.volume_le
  have hL0 : 0 < L := hanch.denom_pos
  have hL := hanch.denom_le
  have hLtop : L ≠ ⊤ := hanch.denom_ne_top
  have hcapture := familyIn_convexHull_biUnion_self t (fun k => (T k).toConvexSpaceBody)
  let V : ι → ConvexSpaceBody E := fun k => (T k).toConvexSpaceBody
  let W : ConvexSpaceBody E := t.convexHull_biUnion (fun k => (T k).toConvexSpaceBody)
  have hbp0 : 0 < bp := lt_of_lt_of_le hap0 hab
  have hCnn : (1 : NNReal) ≤ densityTransfer.C := one_le_densityTransfer_C
  have hCne0 : (densityTransfer.C : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCnn))
  have hCtet : (densityTransfer.C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have ha0 : (ap : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hap0)
  have hb0 : (bp : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hbp0)
  have hl0 : L ≠ 0 := hL0.ne'
  have hden :
      (densityTransfer.C : ENNReal)⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) *
          densityIn t V W ≤ densityIn u'' V K := by
    exact density_dilate_ge hdim hap0 hbp0 T (v := t) (t := t) (u'' := u'')
      (htv := subset_rfl) (_htne := htne) (hvu := htu) (hcapture := hcapture)
      (B := K) (hW := hWK) (hvol := hvol)
  have hKlow :
      (densityTransfer.C : ENNReal)⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) * L ≤
          densityIn u'' V K := by
    calc
      (densityTransfer.C : ENNReal)⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) * L
          ≤ (densityTransfer.C : ENNReal)⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) *
              densityIn t V W := by
            exact mul_le_mul_of_nonneg_left hL zero_le
      _ ≤ densityIn u'' V K := hden
  exact frostmanConstIn_le_of_density_le (s := u'') (V := V) (B := K)
    (C := (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (U / L))
    (by
      intro K' hK'
      calc
        densityIn u'' V K' ≤ U := hnum K' hK'
        _ = ((densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (U / L))
            * ((densityTransfer.C : ENNReal)⁻¹ * ((ap : ENNReal) / (bp : ENNReal)) * L) := by
          rw [anchor_ratio_cancel hCne0 hCtet ha0 ENNReal.coe_ne_top hb0 ENNReal.coe_ne_top
            hl0 hLtop]
        _ ≤ ((densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (U / L))
            * densityIn u'' V K := by
          exact mul_le_mul_of_nonneg_left hKlow zero_le)

/-- **(GWZ Lemma 8.1) Density transfer from a plank to the `2`-dilate of its `b`-tube**
(blueprint `lem:ml1bootDensityTransfer`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  Let `W = W_{m,t}` be a plank of a family
that `2`-factors the fibre `fibre u'' pρ m`, and let `T_b` be a tube whose `2`-dilate
contains `W` with `|2 · T_b| ≤ C_T (b/a) |W|`.  Then

`Δ(𝕋̃'', 2 · T_b) ≥ (2 C_T)⁻¹ (a/b) Δ_max(fibre u'' pρ m)`.

This is the density half of GWZ Lemma 8.1; the Frostman half is
`Kakeya.ml1Boot.frostmanConstIn_fibre_le`, which needs strictly more hypotheses.  The
hypotheses here are deliberately reduced: no parent family beyond the fibre's index set, no
`B₁` containment, and in particular not the dilated containment
`2 · T_b ⊆ c' · T_{ρ,m}` of `Kakeya.ml1Boot.plankTube_subset_parent_dilate`.

The `2`-dilate and not `T_b` itself is what carries the plank: containment of an `a × b × 1`
plank in a tube of any scale `O(b)` is false, see blueprint `note:ml1bootPlankInTubeVacuous`
and `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one`.  The conclusion is stated in
terms of the *plank widths* `ap`, `bp`, whose ratio is what the dichotomy controls, while the
tube has the honest scale `bq ∈ [bp, C_𝕎 bp]`.

The index sets are easy to get wrong: the family whose maximal density appears on the right
is the *fibre*, which is what the factorization is about, and not `𝕋̃` or `𝕋̃''`; see
blueprint `note:ml1bootDensityTransferIndex`.  The density that the proof actually compares
is the density over the *block* `part`, which is what the factorization supplies; the
earlier appeal to the plank capturing exactly its own block was unjustified, since nothing
keeps the planks of distinct blocks from overlapping. -/
theorem maxDensity_fibre_le_density_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp) (_hb1 : bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι}
    (T : ι → Tube δt E) (pρ : ι → κ) {m : κ}
    (F : ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    {part : Finset ι} (hpart : part ∈ F.parts)
    (Tb : Tube bq E)
    (hTb : part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate Tb 2)
    (hTbvol : volume (Tube.dilate Tb 2).carrier ≤ (densityTransfer.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal))
      * volume (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier) :
    (2 * (densityTransfer.C : ENNReal))⁻¹ * ((ap : ENNReal) / (bp : ENNReal))
          * maxDensity (fibre u'' pρ m) (fun i => (T i).toConvexSpaceBody)
        ≤ densityIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2) := by
  classical
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let W : ConvexSpaceBody E := part.convexHull_biUnion V
  let C : ENNReal := (densityTransfer.C : ENNReal)
  let r : ENNReal := (ap : ENNReal) / (bp : ENNReal)
  -- `part` is a part of a `Finpartition` of the fibre, hence contained in `u''`
  have hvu : part ⊆ u'' := by
    intro k hk
    exact (Finset.mem_filter.mp (F.subset hpart hk)).1
  have htne : part.Nonempty := F.nonempty_of_mem_parts hpart
  -- the block family captures its own hull: every `V k` with `k ∈ part` lies in `W`
  have hcapture : familyIn part V W = part := by
    dsimp [W, familyIn]
    exact Finset.filter_true_of_mem (fun i hi => Finset.le_convexHull_biUnion V hi)
  -- Lemma `ml1bootBlockDensityLower` applied to the block family itself
  have hdilate : C⁻¹ * r * densityIn part V W ≤ densityIn u'' V (Tube.dilate Tb 2) := by
    simpa [C, r, W] using
      density_dilate_ge hdim (T := T) (t := part) (v := part) hap0 (lt_of_lt_of_le hap0 hab)
        (htv := subset_rfl) (_htne := htne) (hvu := hvu) (hcapture := hcapture)
        (B := Tube.dilate Tb 2) hTb hTbvol
  -- the factorization bounds the fibre's maximal density by twice the block density
  have hmax : maxDensity (fibre u'' pρ m) V ≤ 2 * densityIn part V W := by
    simpa [V, W] using F.maxDensity_le_mul part hpart
  change (2 * C)⁻¹ * r * maxDensity (fibre u'' pρ m) V ≤ densityIn u'' V (Tube.dilate Tb 2)
  calc
    (2 * C)⁻¹ * r * maxDensity (fibre u'' pρ m) V
        ≤ (2 * C)⁻¹ * r * (2 * densityIn part V W) := by
            exact mul_le_mul_right hmax ((2 * C)⁻¹ * r)
    _ = C⁻¹ * r * densityIn part V W := by
            calc
              (2 * C)⁻¹ * r * (2 * densityIn part V W)
                  = (2 * C)⁻¹ * (2 * (r * densityIn part V W)) := by ring
              _ = ((2 : ENNReal)⁻¹ * C⁻¹) * (2 * (r * densityIn part V W)) := by
                    rw [ENNReal.mul_inv (a := (2 : ENNReal)) (b := C)
                      (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
                      (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))]
              _ = (2 : ENNReal)⁻¹ * (2 : ENNReal) * (C⁻¹ * (r * densityIn part V W)) := by ring
              _ = C⁻¹ * r * densityIn part V W := by
                    rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
                      (by norm_num : (2 : ENNReal) ≠ ⊤)]
                    ring
    _ ≤ densityIn u'' V (Tube.dilate Tb 2) := hdilate

/-- **The uniform density comparison inside `2 · T_b`** (blueprint
`lem:ml1bootFibreDensityCompare`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  Under the hypotheses of
`Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate` together with the *fibre inclusion*
`hfibre` — every tube of `𝕋̃''` caught by a convex subset of `2 · T_b` lies in the fibre over
`m` — the density of `𝕋̃''` in every convex `K ⊆ 2 · T_b` is comparable to its density in
`2 · T_b`:

`Δ(𝕋̃'', K) ≤ 2 C_T (b/a) Δ(𝕋̃'', 2 · T_b)`.

The chain is: `hfibre` and `Kakeya.ml1Boot.densityIn_eq_of_familyIn_subset` replace
`Δ(𝕋̃'', K)` by the fibre's density `Δ(𝔽_m, K)`, which `Kakeya.le_maxDensity` bounds by
`Δ_max(𝔽_m)`, which `Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate` bounds by
`2 C_T (b/a) Δ(𝕋̃'', 2 · T_b)`.

`hfibre` is a genuine hypothesis and not bookkeeping: without it the Frostman conclusion that
this comparison feeds is *false*, not a consequence of the hypotheses; see blueprint
`note:ml1bootFibreInclusionNotAutomatic`.  It is satisfiable — it holds whenever `u''` meets a
single fibre — so neither this lemma nor `Kakeya.ml1Boot.frostmanConstIn_fibre_le` is vacuous.

The hypotheses that `Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate` carries but does not
use are inherited here unchanged. -/
theorem densityIn_le_of_fibre_inclusion [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι}
    (T : ι → Tube δt E) (pρ : ι → κ) {m : κ}
    (F : ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    {part : Finset ι} (hpart : part ∈ F.parts)
    (Tb : Tube bq E)
    (hTb : part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate Tb 2)
    (hTbvol : volume (Tube.dilate Tb 2).carrier ≤ (densityTransfer.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal))
      * volume (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier)
    (hfibre : ∀ K : ConvexSpaceBody E, K ≤ Tube.dilate Tb 2 →
      familyIn u'' (fun i => (T i).toConvexSpaceBody) K ⊆ fibre u'' pρ m)
    (K : ConvexSpaceBody E) (hK : K ≤ Tube.dilate Tb 2) :
    densityIn u'' (fun i => (T i).toConvexSpaceBody) K
      ≤ 2 * (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal))
        * densityIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2) := by
  classical
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let B : ConvexSpaceBody E := Tube.dilate Tb 2
  let C : ENNReal := (densityTransfer.C : ENNReal)
  let r : ENNReal := (bp : ENNReal) / (ap : ENNReal)
  let s₀ : Finset ι := fibre u'' pρ m
  change densityIn u'' V K ≤ 2 * C * r * densityIn u'' V B
  -- (1) the fibre inclusion replaces `u''` by the fibre `s₀`
  have hs₀ : s₀ ⊆ u'' := by
    simp [s₀, fibre]
  have hcatch : familyIn u'' V K ⊆ s₀ := by
    simpa [s₀, V] using hfibre K hK
  have hfibreEq : densityIn u'' V K = densityIn s₀ V K :=
    densityIn_eq_of_familyIn_subset (s := u'') (s₀ := s₀) V K hs₀ hcatch
  -- (2) the fibre density is bounded by the fibre's maximal density
  have hleMax : densityIn s₀ V K ≤ maxDensity s₀ V := le_maxDensity s₀ V K
  -- (3) the transfer bound, rearranged to `maxDensity s₀ V ≤ 2 * C * r * densityIn u'' V B`
  have hmaxle : maxDensity s₀ V ≤ 2 * C * r * densityIn u'' V B := by
    let α : ENNReal := (2 * C)⁻¹ * ((ap : ENNReal) / (bp : ENNReal))
    have hle : α * maxDensity s₀ V ≤ densityIn u'' V B := by
      simpa [α, V, s₀, C, B] using
        maxDensity_fibre_le_density_dilate hdim (T := T) (pρ := pρ) (m := m) (F := F)
          (part := part) (hpart := hpart) hap0 hab hb1 Tb hTb hTbvol
    -- non-degeneracy: `2 * C` is nonzero and finite, and the ratios cancel
    have one_le_volC : ∀ n : ℕ, (1 : NNReal) ≤ Metric.volume_comparison.C n := by
      intro n
      have hCval : Metric.volume_comparison.C n = ((4 : ℝ) ^ n * (Nat.factorial n : ℝ) : ℝ) := by
        dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
        push_cast
        field_simp
      have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) :=
        mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
      have : (1 : ℝ) ≤ (Metric.volume_comparison.C n : ℝ) := by
        rw [hCval]
        nlinarith
      exact_mod_cast this
    have hCnn : (1 : NNReal) ≤ densityTransfer.C := by
      dsimp [densityTransfer.C]
      have hCw : (1 : NNReal) ≤ plankPigeonhole.C := by
        dsimp [plankPigeonhole.C]
        exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_volC 3)
      exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 256) (one_le_pow₀ hCw))
        (one_le_volC 3)
    have hCne0 : C ≠ 0 := by
      dsimp [C]
      exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hCnn))
    have hCtet : C ≠ ⊤ := by
      dsimp [C]
      exact ENNReal.coe_ne_top
    have h2ne0 : (2 * C : ENNReal) ≠ 0 := by
      exact mul_ne_zero (by norm_num : (2 : ENNReal) ≠ 0) hCne0
    have h2neTop : (2 * C : ENNReal) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hCtet
    have hc : (2 * C)⁻¹ * (2 * C) = 1 := ENNReal.inv_mul_cancel h2ne0 h2neTop
    have ha0 : (ap : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hap0)
    have hb0n : 0 < bp := lt_of_lt_of_le hap0 hab
    have hb0 : (bp : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hb0n)
    have hratio : ((ap : ENNReal) / (bp : ENNReal)) * ((bp : ENNReal) / (ap : ENNReal)) = 1 := by
      rw [← ENNReal.mul_div_mul_comm (Or.inl hb0) (Or.inr ha0)]
      rw [mul_comm (bp : ENNReal) (ap : ENNReal)]
      exact ENNReal.div_self (mul_ne_zero ha0 hb0)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
    have hratio' : ((bp : ENNReal) / (ap : ENNReal)) * ((ap : ENNReal) / (bp : ENNReal)) = 1 := by
      simpa [mul_comm] using hratio
    have hstep : (2 * C) * r * α = 1 := by
      dsimp [r, α]
      calc
        (2 * C) * ((bp : ENNReal) / (ap : ENNReal)) *
            ((2 * C)⁻¹ * ((ap : ENNReal) / (bp : ENNReal)))
            = ((2 * C) * (2 * C)⁻¹) *
                (((bp : ENNReal) / (ap : ENNReal)) * ((ap : ENNReal) / (bp : ENNReal))) := by
              ring
        _ = 1 := by
          rw [mul_comm (2 * C) ((2 * C)⁻¹), hc, hratio', one_mul]
    calc
      maxDensity s₀ V = 1 * maxDensity s₀ V := by rw [one_mul]
      _ = ((2 * C) * r * α) * maxDensity s₀ V := by rw [← hstep]
      _ = (2 * C) * r * (α * maxDensity s₀ V) := by ring
      _ ≤ (2 * C) * r * densityIn u'' V B := by
        exact mul_le_mul_right hle ((2 * C) * r)
  -- chain the three steps
  calc
    densityIn u'' V K = densityIn s₀ V K := hfibreEq
    _ ≤ maxDensity s₀ V := hleMax
    _ ≤ 2 * C * r * densityIn u'' V B := hmaxle

/-- **(GWZ Lemma 8.1) The Frostman constant of the `b`-tube** (blueprint
`lem:ml1bootDensityTransferFrostman`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  In the situation of
`Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate`, with `T_b` the tube that
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` attaches to the plank and with the
dilated containment in the parent supplied by
`Kakeya.ml1Boot.plankTube_subset_parent_dilate`,

`C_F(𝕋̃''[2 · T_b], 2 · T_b) ≤ 2 C_T (b/a)`.

`hfibre` is a genuine hypothesis, not bookkeeping: without it the conclusion is **false**,
not a consequence of the hypotheses.  A tube `T i` with `i ∈ u''` lying inside a convex `K ⊆ 2 · T_b` need
not satisfy `pρ i = m` — the parent map is arbitrary and the parent tubes are not assumed
pairwise essentially distinct — so `𝕋̃''` may pile up tubes from other fibres inside a thin
`K`, driving `C_F` above any fixed multiple of `b/a`.  Blueprint
`note:ml1bootFibreInclusionNotAutomatic` carries the counterexample and records what would
discharge the hypothesis: essential distinctness of the parent `ρ`-tubes together with a
quantitative statement that a `δ̃`-tube inside `c' · T_{ρ,m}` has its assigned parent
essentially equal to `T_{ρ,m}`.  Until one of those is available the hypothesis stays
explicit and is inherited by every consumer.

Every occurrence of the containing body is the `2`-dilate and not `T_b`; see
`Kakeya.ml1Boot.maxDensity_fibre_le_density_dilate`. -/
theorem frostmanConstIn_fibre_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1) (hbbq : bp ≤ bq) (_hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu : u.Nonempty) (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {m : κ} (hm : m ∈ tρ) {part : Finset ι} (hpart : part ∈ (F m).parts)
    (Tb : Tube bq E)
    (hTb : part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate Tb 2)
    (hTbsub : Tube.dilate Tb 2 ≤ Tube.dilate (Tρ m) (plankTubeInParent.C : ℝ))
    (hTbvol : volume (Tube.dilate Tb 2).carrier ≤ (densityTransfer.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal))
      * volume (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier)
    (hfibre : ∀ K : ConvexSpaceBody E, K ≤ Tube.dilate Tb 2 →
      familyIn u'' (fun i => (T i).toConvexSpaceBody) K ⊆ fibre u'' pρ m) :
    frostmanConstIn (familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
          (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)
        ≤ 2 * (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) := by
  classical
  -- assemble: the uniform density comparison (from the fibre inclusion) is the density
  -- hypothesis of `frostmanConstIn_le_of_density_le`, whose conclusion is the goal
  exact frostmanConstIn_le_of_density_le (s := u'')
    (V := fun i => (T i).toConvexSpaceBody) (B := Tube.dilate Tb 2)
    (C := 2 * (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)))
    (by
      intro K hK
      exact densityIn_le_of_fibre_inclusion hdim
        (lt_of_lt_of_le hδt hδa) hab (le_trans hbρ hρ1)
        (T := T) (pρ := pρ) (m := m) (F := F m) (hpart := hpart)
        (Tb := Tb) (hTb := hTb) (hTbvol := hTbvol) (hfibre := hfibre)
        (K := K) (hK := hK))

/-- **(GWZ Lemma 8.1) The Frostman constant at the pigeonholed ratio** (blueprint
`cor:ml1bootDensityTransferFrostmanPower`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C` and let `ap' = η'_{j-1} ≥ 0`.  Under the
hypotheses of `Kakeya.ml1Boot.frostmanConstIn_fibre_le` — including the fibre inclusion
`hfibre` — and the width ratio bound `b / a ≤ δ̃ ^ (-ap')` supplied by
`Kakeya.ml1Boot.flatPrism_dichotomy`,

`C_F(𝕋̃''[2 · T_b], 2 · T_b) ≤ 2 C_T δ̃ ^ (-ap')`.

This is exactly the shape in which `Kakeya.ml1Boot.plankWidth_le` consumes the upper Frostman
bound, and it is a declaration of its own rather than a second conclusion of
`Kakeya.ml1Boot.frostmanConstIn_fibre_le` so that each statement asserts one inequality.  The
proof is that lemma followed by monotonicity of multiplication by `2 C_T`. -/
theorem frostmanConstIn_fibre_le_rpow [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1) (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ap' : ℝ} (hap' : 0 ≤ ap')
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu : u.Nonempty) (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {m : κ} (hm : m ∈ tρ) {part : Finset ι} (hpart : part ∈ (F m).parts)
    (Tb : Tube bq E)
    (hTb : part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate Tb 2)
    (hTbsub : Tube.dilate Tb 2 ≤ Tube.dilate (Tρ m) (plankTubeInParent.C : ℝ))
    (hTbvol : volume (Tube.dilate Tb 2).carrier ≤ (densityTransfer.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal))
      * volume (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier)
    (hfibre : ∀ K : ConvexSpaceBody E, K ≤ Tube.dilate Tb 2 →
      familyIn u'' (fun i => (T i).toConvexSpaceBody) K ⊆ fibre u'' pρ m) :
    frostmanConstIn (familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
          (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)
        ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
  calc
    frostmanConstIn (familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
          (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)
        ≤ 2 * (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) := by
            exact frostmanConstIn_fibre_le hdim hδt hδa hab hbρ hρ1 hbbq hbq
              T Tρ pρ hu hu'' hball hparent F hdims hm hpart Tb hTb hTbsub hTbvol hfibre
    _ ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
            gcongr

/-! #### The seam between the produced and the consumed fibre Frostman bound

`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` produces its bound at the index set
`𝕋̃''[2 · T_b]` and the body `2 · T_b`, whereas hypothesis (a) of
`Kakeya.ml1Boot.normalized_le_of_coarse` reads it at the index set `fibre u p_b l` and the body
`T_{b,l}`.  The four declarations below close that seam, and record exactly what it costs.

Both differences are handled, and only one of them costs anything:

* the **body** is free.  Shrinking the ambient body from `2 · T_b` back to `T_b` *lowers* the
  Frostman constant whenever the index set's members all lie in `T_b`, which is what the
  undilated `Kakeya.ml1Boot.IsParentFamily` of `Kakeya.ml1Boot.normalized_le_of_coarse` supplies;
  this is `Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient`, with no loss at all.  The `2`-dilate
  is therefore needed only on the *producer* side, where the plank lies in `2 · T_b` and in no
  tube of scale `O(b)` (blueprint `note:ml1bootPlankInTubeVacuous`), and does not have to be
  propagated into the consumer.
* the **index set** is not free.  `Kakeya.frostmanConstIn` is not monotone in the index set, so
  the free inclusion `fibre u p_b l ⊆ 𝕋̃''[2 · T_b]` — the containment clause of the parent
  family followed by `Kakeya.Tube.subset_dilate` — transports nothing.  What is needed is that
  the two index sets *agree*, i.e. the reverse inclusion `𝕋̃''[2 · T_b] ⊆ fibre u p_b l`: no
  `δ̃`-tube of the family lies in `2 · T_b` except those assigned to `T_b` itself.  That is a
  hypothesis of exactly the kind blueprint `note:ml1bootFibreInclusionNotAutomatic` refutes as
  automatic, read at the *plank* scale rather than at the parent scale `ρ`.

The two are one seam and not two: `Kakeya.ml1Boot.familyIn_subset_of_familyIn_subset_of_le` shows
that the `∀ K ≤ 2 · T_b` in the `hfibre` of `Kakeya.ml1Boot.frostmanConstIn_fibre_le` is
redundant — the single instance at `K = 2 · T_b` implies all of it, because `𝕋̃''[K]` is monotone
in `K` — so the plank-scale inclusion needed for the index sets to agree *implies* `hfibre`
whenever `p_b` refines `p_ρ`.

Where that inclusion cannot come from, and what replaces it:

* **not from the parent map.**  Hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse` reads
  the bound at *every* `l ∈ t_b`, so the seam needs the inclusion at every `l` at once; by
  `Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre` that is equivalent to a separation
  property of the `b`-tubes — no `δ̃`-tube of `u''` lies in two of the `2`-dilates — and once
  that fails no reassignment of `p_b` repairs it, a single `δ̃`-tube having to go to two indices.
  So it is not a fact that the *construction* of the parent map can be made to deliver.
* **not from essential distinctness, hence not from the merge.**  Pairwise
  `Kakeya.IsEssentiallyDistinct` is the only geometric information about `t_b` that
  `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` and the merge
  `Kakeya.ml1Boot.exists_merged_parentFamily` behind it export, and it is strictly weaker than
  that separation: two `σ`-tubes with parallel cores at distance `3 σ` are disjoint, hence
  essentially distinct, while both `2`-dilates contain the `δ̃`-tube whose core is the parallel
  unit segment midway between them.  Raising the merge ratio does not help: the ratio is spent
  transporting the plank clause of a *discarded* tube, never on emptying a *retained* tube's
  dilate.  The docstring of `Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre` carries
  the computation.
* **what does transport is mass.**  `Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass` and its
  tube-shaped form `Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le_of_mass` replace the
  inclusion by the share `∑_{𝕋̃''[2 · T_b]} |T_i| ≤ C ∑_{fibre} |T_i|`, at the price `C` in the
  constant.  Unlike the inclusion, the share can hold at every `l` at once.  It is the weaker
  ask that blueprint `note:ml1bootReduceToTbFrostmanIndexSet` identifies as where to attack the
  seam next, and the route through `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset` taken here
  carries none of the four side conditions of `ConvexSpaceBody.frostmanConstIn_subfamily_le`
  that the note routes it through — no nonemptiness, no equality of member volumes — so it is
  available at *every* `l` and not only at the index
  `Kakeya.ml1Boot.exists_surviving_parent_index` singles out.  Whether the share itself is
  derivable from the Case (ii) data is not settled here. -/

/-- **The catch family is monotone in the test body, so one instance of the fibre inclusion gives
all of them.**

If every member of `𝕍|_s` lying in `B` is assigned to the fibre over `l`, then the same holds
for every `K ≤ B`, since `𝕍[K] ⊆ 𝕍[B]`.

This is why the `∀ K ≤ 2 · T_b` binder of the `hfibre` hypothesis of
`Kakeya.ml1Boot.frostmanConstIn_fibre_le` and of
`Kakeya.ml1Boot.densityIn_le_of_fibre_inclusion` is not a stronger assumption than its single
instance at `K = B`: the two are equivalent. -/
theorem familyIn_subset_of_familyIn_subset_of_le {ι κ : Type*} [DecidableEq κ] {s : Finset ι}
    (V : ι → ConvexSpaceBody E) (p : ι → κ) (l : κ) {B : ConvexSpaceBody E}
    (hcatch : familyIn s V B ⊆ fibre s p l) :
    ∀ K : ConvexSpaceBody E, K ≤ B → familyIn s V K ⊆ fibre s p l := by
  classical
  intro K hK i hi
  have hmemB : i ∈ familyIn s V B := by
    simp only [familyIn, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, le_trans hi.2 hK⟩
  exact hcatch hmemB

/-- **The catch family in the dilate is the fibre.**

Let `p` assign to each member of `s` a parent index, let `B` be a body containing every member
of the fibre over `l`, and assume the fibre inclusion `𝕍[B] ⊆ fibre s p l`.  Then the two index
sets coincide: `𝕍[B] = fibre s p l`.

The inclusion `⊇` is the containment hypothesis `hle` alone; `⊆` is `hcatch`, which blueprint
`note:ml1bootFibreInclusionNotAutomatic` shows does not follow from the data of the Case (ii)
chain.  Equality of the index sets is what the seam needs, `Kakeya.frostmanConstIn` being
monotone in neither direction in its index set. -/
theorem familyIn_eq_fibre_of_familyIn_subset {ι κ : Type*} [DecidableEq κ] {s : Finset ι}
    (V : ι → ConvexSpaceBody E) (p : ι → κ) (l : κ) {B : ConvexSpaceBody E}
    (hle : ∀ i ∈ s, p i = l → V i ≤ B)
    (hcatch : familyIn s V B ⊆ fibre s p l) :
    familyIn s V B = fibre s p l := by
  classical
  unfold familyIn fibre
  exact Finset.Subset.antisymm hcatch (by
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hle i hi.1 hi.2⟩)

/-- **The geometric kernel that leaf 1 reduces to** (blueprint
`note:ml1bootDilatesUnsharedIsTheKernel`).

`DilatesUnshared s V t B` says that no member of the fine family lies in two of the bodies
`B l`: each member is caught by at most one of them.  In the application `B l = 2 · T_{b,l}`
is the doubled plank-tube, so it says that a plank-tube's double is not shared.

This is stated here because three independent attempts on
`Kakeya.ml1Boot.multTildeT_of_planksClose` have arrived at it, from three directions, and it is
the same statement each time:

* as `hcatch`, the containment `familyIn u'' 𝕍 (2 · T_b) ⊆ fibre u'' p_b l` that
  `Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow_atTube` takes as a hypothesis and that nothing
  on the route produces --- and that blueprint
  `note:ml1bootFibreInclusionNotAutomatic` refutes as automatic;
* as the *mass share* `∑_{fibre} |T̃_i| ≳ (|2·T_b| / |B₁|) ∑_{u''} |T̃_i|`, which the check of
  the exponent chain showed cannot be paid: the seam
  `Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass` multiplies `M · C`, and the `M` slot is
  already filled at `2 C_T δ̃ ^ (-ap')` by
  `Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow`, so the budget for `C` is `O(1)` and not
  `δ̃ ^ (-σ)`.  That is also why the old containment route closed with nothing to spare: there
  `C` is exactly `1`;
* as the hypothesis `hfibre` of `Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` itself, which is
  the same inclusion read at the `ρ` scale.

`Kakeya.ml1Boot.dilatesUnshared_iff_forall_familyIn_subset_fibre` below records that this is
*equivalent* to the family of `hcatch` clauses, so it is the kernel and not one more sufficient
condition.

**It is not implied by essential distinctness**, and that is the reason it is owed rather than
derived: two `σ`-tubes with parallel cores at distance `3σ` are disjoint, hence essentially
distinct, while both of their doubles contain the `δ̃`-tube on the parallel core between them
whenever `δ̃ ≤ σ / 2`.  On this route `σ = C_𝕎 · b` with `C_𝕎 ≥ 1024` and `δ̃ ≤ a ≤ b`, so the
configuration is available.  What is owed is therefore a *separation* property of the plank-tube
family, strictly stronger than the pairwise essential distinctness its producer
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` supplies.  That is tube geometry, not
Section 8 combinatorics. -/
def DilatesUnshared {ι κ : Type*} (s : Finset ι) (V : ι → ConvexSpaceBody E) (t : Finset κ)
    (B : κ → ConvexSpaceBody E) : Prop :=
  ∀ i ∈ s, ∀ l ∈ t, ∀ l' ∈ t, V i ≤ B l → V i ≤ B l' → l = l'

/-- **Unsharedness gives every `hcatch` at once.**  With the parent containment
`∀ i ∈ s, V i ≤ B (p i)` and `p` landing in `t`, unsharedness of the bodies forces the family
caught by `B l` to be exactly inside the `p`-fibre of `l` --- which is `hcatch`, for every `l`
simultaneously and with constant `1`. -/
theorem familyIn_subset_fibre_of_dilatesUnshared {ι κ : Type*} [DecidableEq κ] {s : Finset ι}
    {t : Finset κ} {V : ι → ConvexSpaceBody E} {B : κ → ConvexSpaceBody E} {p : ι → κ}
    (hun : DilatesUnshared s V t B) (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, V i ≤ B (p i)) {l : κ} (hl : l ∈ t) :
    familyIn s V (B l) ⊆ fibre s p l := by
  classical
  intro i hi
  obtain ⟨his, hiB⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨his, hun i his (p i) (hmaps i his) l hl (hle i his) hiB⟩

/-- **The kernel is exactly the family of `hcatch` clauses.**  One direction is
`Kakeya.ml1Boot.familyIn_subset_fibre_of_dilatesUnshared`; the other is
`Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre` below, read contrapositively.  So
nothing is lost by owing `DilatesUnshared` instead of owing the clauses. -/
theorem dilatesUnshared_iff_forall_familyIn_subset_fibre {ι κ : Type*} [DecidableEq κ]
    {s : Finset ι} {t : Finset κ} {V : ι → ConvexSpaceBody E} {B : κ → ConvexSpaceBody E}
    {p : ι → κ} (hmaps : ∀ i ∈ s, p i ∈ t) (hle : ∀ i ∈ s, V i ≤ B (p i)) :
    DilatesUnshared s V t B ↔ ∀ l ∈ t, familyIn s V (B l) ⊆ fibre s p l := by
  classical
  refine ⟨fun hun l hl => familyIn_subset_fibre_of_dilatesUnshared hun hmaps hle hl, ?_⟩
  intro hcatch i his l hl l' hl' hil hil'
  have h1 : p i = l := (Finset.mem_filter.mp (hcatch l hl
    (Finset.mem_filter.mpr ⟨his, hil⟩))).2
  have h2 : p i = l' := (Finset.mem_filter.mp (hcatch l' hl'
    (Finset.mem_filter.mpr ⟨his, hil'⟩))).2
  exact h1.symm.trans h2

/-- **The fibre inclusion, read at every index at once, is a separation property of the test
bodies and not of the parent map.**

Suppose the catch inclusion `𝕍[B] ⊆ fibre s p l` holds at two *distinct* indices `l ≠ l'`, with
test bodies `B` and `B'`.  Then no member of the family lies in both `B` and `B'`.

This is what makes the `hcatch` hypothesis of
`Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le` unproducible from the construction of the
parent map.  Hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse` reads its fibre Frostman
bound at *every* `l ∈ t_b`, so the seam needs `hcatch` at every `l` simultaneously, and this
lemma turns that into: the `2`-dilates of two distinct `b`-tubes never both contain the same
`δ̃`-tube of `u''`.  That is a condition on the `b`-tubes themselves.  Once it fails no
reassignment `p_b` can repair it, because a single `δ̃`-tube would have to be assigned to two
indices at once; so the missing ingredient is geometric separation and not a better parent map.

Pairwise `Kakeya.IsEssentiallyDistinct` of the `b`-tubes — the only geometric information that
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` and the merge
`Kakeya.ml1Boot.exists_merged_parentFamily` behind it export — is strictly weaker.  Two
`σ`-tubes whose cores are parallel at distance `3 σ` are *disjoint*, hence essentially distinct
at the threshold `½` of `Kakeya.IsEssentiallyDistinct`; yet each `2`-dilate is the `2 σ`-
neighbourhood of a doubled core, so both contain the `δ̃`-tube whose core is the parallel unit
segment midway between them, as soon as `δ̃ ≤ σ / 2`.  On this route that is met with room to
spare: `δ̃ ≤ a ≤ b` and the `b`-tube scale is `σ = C_𝕎 b` with `C_𝕎 ≥ 1024`.  So the merge
mechanism cannot supply `hcatch`, and neither can a merge run at any larger dilation ratio,
the ratio being spent on transporting the plank clause of a *discarded* tube and never on
excluding a fine tube from a *retained* one's dilate.

What can be assumed at every `l` at once, consistently, is the mass form: see
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass`. -/
theorem disjoint_familyIn_of_familyIn_subset_fibre {ι κ : Type*} [DecidableEq κ] {s : Finset ι}
    (V : ι → ConvexSpaceBody E) (p : ι → κ) {l l' : κ} (hll : l ≠ l')
    {B B' : ConvexSpaceBody E}
    (hcatch : familyIn s V B ⊆ fibre s p l)
    (hcatch' : familyIn s V B' ⊆ fibre s p l') :
    ∀ i ∈ s, ¬ (V i ≤ B ∧ V i ≤ B') := by
  classical
  intro i hi ⟨h1, h2⟩
  have hmemB : i ∈ familyIn s V B := by
    simp only [familyIn, Finset.mem_filter]
    exact ⟨hi, h1⟩
  have hmemB' : i ∈ familyIn s V B' := by
    simp only [familyIn, Finset.mem_filter]
    exact ⟨hi, h2⟩
  have hpl : p i = l := (Finset.mem_filter.mp (hcatch hmemB)).2
  have hpl' : p i = l' := (Finset.mem_filter.mp (hcatch' hmemB')).2
  exact hll (hpl.symm.trans hpl')

/-- **Shrinking the ambient body onto the family lowers the Frostman constant.**

If every member of `𝕍|_s` lies in `K` and `K ≤ K'`, then `C_F(𝕍|_s, K) ≤ C_F(𝕍|_s, K')`.

Both densities have the same numerator `∑_{i ∈ s} |V_i|`, so passing from `K'` to the smaller
`K` only *raises* the reference density in the denominator of the Frostman ratio, and the
admissible constants can only shrink.  Nothing is paid: unlike
`ConvexSpaceBody.frostmanConstIn_ambient_mono`, which runs in the opposite direction and charges
the volume ratio `|K'| / |K|`, this direction is loss-free.

It is what removes the `2`-dilate from the fibre Frostman bound at the consumer:
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` produces the bound in `2 · T_b`, and hypothesis
(a) of `Kakeya.ml1Boot.normalized_le_of_coarse` reads it in `T_{b,l}`, whose members are all of
the fibre by the containment clause of `Kakeya.ml1Boot.IsParentFamily`. -/
theorem frostmanConstIn_le_of_le_ambient {ι : Type*} {s : Finset ι}
    (V : ι → ConvexSpaceBody E) {K K' : ConvexSpaceBody E} (hKK' : K ≤ K')
    (hV : ∀ i ∈ s, V i ≤ K) :
    frostmanConstIn s V K ≤ frostmanConstIn s V K' := by
  classical
  -- every member of the family lies in `K'` too, and `K'` is larger than `K`
  have hV' : ∀ i ∈ s, V i ≤ K' := fun i hi => le_trans (hV i hi) hKK'
  -- the volume comparison
  have hvol : volume K.carrier ≤ volume K'.carrier :=
    measure_mono (SetLike.coe_subset_coe.mpr hKK')
  -- the density comparison
  have hden : densityIn s V K' ≤ densityIn s V K := by
    rw [densityIn_of_all_le hV', densityIn_of_all_le hV]
    exact ENNReal.div_le_div_left hvol (∑ i ∈ s, volume (V i).carrier)
  -- the Frostman property at `K'`
  apply frostmanConstIn_le
  intro K'' hK''
  calc
    densityIn s V K'' ≤ frostmanConstIn s V K' * densityIn s V K' :=
      isFrostmanIn_frostmanConstIn s V K' K'' (le_trans hK'' hKK')
    _ ≤ frostmanConstIn s V K' * densityIn s V K := by
      exact mul_le_mul_of_nonneg_left hden zero_le

/-- **(GWZ Lemma 8.1) The fibre Frostman bound in the `b`-tube itself** (the seam of blueprint
`cor:ml1bootDensityTransferFrostmanPower` with hypothesis (a) of
`lem:ml1bootReduceToTb`).

Let `T_b` be a tube, `p` a parent map, `l` an index, and suppose

* `hle` — every `δ̃`-tube of `s` assigned to `l` lies in `T_b`, which is the containment clause
  `Kakeya.ml1Boot.IsParentFamily.le_parent` of the parent family that
  `Kakeya.ml1Boot.normalized_le_of_coarse` assumes;
* `hcatch` — every `δ̃`-tube of `s` lying in `2 · T_b` is assigned to `l`;
* `hM` — the Frostman bound that `Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` produces, at the
  index set `𝕋̃[2 · T_b]` and the body `2 · T_b`.

Then the same bound holds at the index set `fibre s p l` and the body `T_b`, which is the shape
hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse` consumes.

`hcatch` is the whole price of the seam, and it is not bookkeeping: it is the plank-scale
instance of the fibre inclusion that blueprint `note:ml1bootFibreInclusionNotAutomatic` refutes
as automatic.  It is also not a fact about the parent map, so no construction of `p_b` supplies
it: read at every `l ∈ t_b`, as its consumer reads it, it is a separation property of the
`b`-tubes themselves (`Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre`), and pairwise
essential distinctness of the `b`-tubes does not imply it.
`Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le_of_mass` is the same statement with `hcatch`
weakened to a mass share, which does not carry that obstruction, at the price of the share in
the constant.  Nothing else is paid — in particular the passage from the `2`-dilate to `T_b`
is loss-free, by `Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient`, so the constant `M` is
carried across unchanged and the conclusion of
`Kakeya.ml1Boot.normalized_le_of_coarse` needs no weakening. -/
theorem frostmanConstIn_fibre_undilated_le {ι κ : Type*} [DecidableEq κ] {δt bq : NNReal}
    {s : Finset ι} {M : ENNReal} (T : ι → Tube δt E) (p : ι → κ) (l : κ) (Tb : Tube bq E)
    (hle : ∀ i ∈ s, p i = l → (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hcatch : familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)
      ⊆ fibre s p l)
    (hM : frostmanConstIn (familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
        (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2) ≤ M) :
    frostmanConstIn (fibre s p l) (fun i => (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
      ≤ M := by
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  have hself : Tb.toConvexSpaceBody ≤ Tube.dilate Tb 2 := by
    exact SetLike.coe_subset_coe.mpr (Tube.subset_dilate Tb (by norm_num : (1 : ℝ) ≤ 2))
  have heq : familyIn s V (Tube.dilate Tb 2) = fibre s p l := by
    exact familyIn_eq_fibre_of_familyIn_subset (V := V) (p := p) (l := l)
      (B := Tube.dilate Tb 2)
      (hle := fun i hi hpl => by simpa [V] using (hle i hi hpl).trans hself)
      (hcatch := hcatch)
  have hVfib : ∀ i ∈ fibre s p l, V i ≤ Tb.toConvexSpaceBody := by
    intro i hi
    simpa [V] using hle i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  calc
    frostmanConstIn (fibre s p l) V Tb.toConvexSpaceBody
        ≤ frostmanConstIn (fibre s p l) V (Tube.dilate Tb 2) := by
          exact frostmanConstIn_le_of_le_ambient (V := V) (K := Tb.toConvexSpaceBody)
            (K' := Tube.dilate Tb 2) (hKK' := hself) (hV := hVfib)
      _ = frostmanConstIn (familyIn s V (Tube.dilate Tb 2)) V (Tube.dilate Tb 2) := by
          rw [← heq]
      _ ≤ M := by
          simpa [V] using hM

/-- **The mass form of the seam: a *heavy* fibre transports the Frostman bound, at the cost of
its mass ratio.**

Let `p` assign parents, let `K ≤ B`, let every member of the fibre over `l` lie in `K`, and
suppose the fibre carries a `C⁻¹` share of the total volume of the family caught in `B`:

`∑_{i ∈ 𝕍[B]} |V_i| ≤ C ∑_{i ∈ fibre s p l} |V_i|`.

Then a Frostman bound `M` at the index set `𝕍[B]` and the body `B` gives the bound `M C` at the
index set `fibre s p l` and the body `K`.

This is `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset` — Frostman-ness passes to a heavy
subfamily — followed by the loss-free ambient shrink
`Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient`.  The free inclusion
`fibre s p l ⊆ 𝕍[B]` supplies the subfamily; `Kakeya.frostmanConstIn` is monotone in the index
set in neither direction, and the mass hypothesis is exactly what repairs that.

It is the substitute for `hcatch` in `Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le`, and it
is a *weaker* assumption in a way that matters.  At `C = 1` the two coincide up to null members,
but for `C > 1` the mass form can hold at every `l ∈ t_b` at once, whereas `hcatch` at every `l`
at once forces a geometric separation of the `b`-tubes that pairwise essential distinctness does
not deliver (`Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre`).  The price is the
factor `C` in the constant, which hypothesis (a) of
`Kakeya.ml1Boot.normalized_le_of_coarse` has no room for as stated — it fixes the constant at
`2 C_T δ̃ ^ (-ap')` — so a producer of the mass hypothesis has to be read together with exponent
room, absorbing `C` into `δ̃ ^ (-ap')` for small `δ̃` in the manner of item (4) of the ledger on
`Kakeya.ml1Boot.multTildeT_of_planksClose`.  What such a producer has to bound is the number of
`δ̃`-tubes of `u''` lying in `2 · T_{b,l}` against the number in the plank block of `l`: a
multiplicity statement at the `b`-scale, not a property of the parent map. -/
theorem frostmanConstIn_fibre_le_of_mass {ι κ : Type*} [DecidableEq κ] {s : Finset ι}
    {C M : ENNReal} (V : ι → ConvexSpaceBody E) (p : ι → κ) (l : κ) {K B : ConvexSpaceBody E}
    (hKB : K ≤ B) (hle : ∀ i ∈ s, p i = l → V i ≤ K)
    (hmass : ∑ i ∈ familyIn s V B, volume (V i).carrier
      ≤ C * ∑ i ∈ fibre s p l, volume (V i).carrier)
    (hM : frostmanConstIn (familyIn s V B) V B ≤ M) :
    frostmanConstIn (fibre s p l) V K ≤ M * C := by
  let s1 : Finset ι := familyIn s V B
  let s0 : Finset ι := fibre s p l
  have hW : ∀ i ∈ s1, V i ≤ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsub : s0 ⊆ s1 := by
    intro i hi
    simp only [s0, s1, familyIn, fibre, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, le_trans (hle i hi.1 hi.2) hKB⟩
  have hFr : IsFrostmanIn s1 V B M := isFrostmanIn_of_frostmanConstIn_le hM
  have hFr' : IsFrostmanIn s0 V B (M * C) := hFr.of_le_of_subset hW hsub hmass
  have hle0 : frostmanConstIn s0 V B ≤ M * C := frostmanConstIn_le hFr'
  have hV : ∀ i ∈ s0, V i ≤ K := by
    intro i hi
    exact hle i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2
  calc
    frostmanConstIn (fibre s p l) V K ≤ frostmanConstIn (fibre s p l) V B := by
      exact frostmanConstIn_le_of_le_ambient (V := V) (K := K) (K' := B) (hKK' := hKB)
        (hV := hV)
    _ = frostmanConstIn s0 V B := by simp [s0]
    _ ≤ M * C := hle0

/-- **The mass form of the seam, in the tube shape the seam is read in.**

`Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass` at `K = T_b` and `B = 2 · T_b`: the shape of
`Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le` with `hcatch` replaced by the mass ratio and
the constant `M` replaced by `M C`. -/
theorem frostmanConstIn_fibre_undilated_le_of_mass {ι κ : Type*} [DecidableEq κ]
    {δt bq : NNReal} {s : Finset ι} {C M : ENNReal} (T : ι → Tube δt E) (p : ι → κ) (l : κ)
    (Tb : Tube bq E)
    (hle : ∀ i ∈ s, p i = l → (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hmass : ∑ i ∈ familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2),
        volume (T i).carrier
      ≤ C * ∑ i ∈ fibre s p l, volume (T i).carrier)
    (hM : frostmanConstIn (familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
        (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2) ≤ M) :
    frostmanConstIn (fibre s p l) (fun i => (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
      ≤ M * C := by
  have hself : Tb.toConvexSpaceBody ≤ Tube.dilate Tb 2 := by
    exact SetLike.coe_subset_coe.mpr (Tube.subset_dilate Tb (by norm_num : (1 : ℝ) ≤ 2))
  exact frostmanConstIn_fibre_le_of_mass (V := fun i => (T i).toConvexSpaceBody) (p := p)
    (l := l) (K := Tb.toConvexSpaceBody) (B := Tube.dilate Tb 2) (hKB := hself) (hle := hle)
    (hmass := by simpa using hmass) (hM := hM)

/-- **The mass form of the seam, restated as a count.**

All the `T i` are tubes of one scale `δt`, so their carriers have exactly equal volume
(`Tube.volume_carrier_eq_volume_carrier`) and a volume share is a cardinality share at the same
factor, with nothing lost.  `Tube.mul_sum_volume_le_iff_mul_card_le` is that equivalence; the
reference tube `T₀` is what makes the common volume nameable when the index sets may be empty,
and `0 < δt` is what stops the common volume from being `0` (at `δt = 0` every side vanishes and
the volume form is vacuous while the count form is not).

So the hypothesis of `Kakeya.ml1Boot.multTildeT_of_planksClose` is not a measure-theoretic
statement at all.  What has to be produced, uniformly in `l ∈ t_b`, is

`|{i ∈ 𝕋̃'' : T̃_i ⊆ 2 · T_{b,l}}| ≤ C · |fibre 𝕋̃'' p_b l|`,

a count of fine tubes caught in a `b`-tube against the count in the plank block of that `b`-tube,
with `C` small enough to be absorbed by the exponent room of `planksClose_numerics`. -/
theorem frostmanConstIn_fibre_undilated_le_of_card [Nontrivial E] {ι κ : Type*} [DecidableEq κ]
    {δt bq : NNReal} (hδt : 0 < δt) {s : Finset ι} {C M : ENNReal} (T : ι → Tube δt E)
    (T₀ : Tube δt E) (p : ι → κ) (l : κ) (Tb : Tube bq E)
    (hle : ∀ i ∈ s, p i = l → (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hcard : ((familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)).card : ENNReal)
      ≤ C * ((fibre s p l).card : ENNReal))
    (hM : frostmanConstIn (familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
        (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2) ≤ M) :
    frostmanConstIn (fibre s p l) (fun i => (T i).toConvexSpaceBody) Tb.toConvexSpaceBody
      ≤ M * C := by
  classical
  have hmass : (∑ i ∈ familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2),
      volume (T i).carrier)
      ≤ C * ∑ i ∈ fibre s p l, volume (T i).carrier := by
    simpa [one_mul] using
      (_root_.Tube.mul_sum_volume_le_iff_mul_card_le (E := E) hδt
        (T := T) (T₀ := T₀)
        (s := familyIn s (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
        (r := fibre s p l) (c := 1) (d := C)).mpr (by simpa using hcard)
  exact frostmanConstIn_fibre_undilated_le_of_mass (T := T) (p := p) (l := l) (Tb := Tb)
    (hle := hle) (hmass := hmass) (hM := hM)

/-- **The numerator of the seam's count is a Frostman consequence, not a density assumption.**

`Kakeya.ConvexSpaceBody.IsFrostmanIn` (Frostman.lean:31) is *literally* a density comparison:
`∀ K' ≤ K, densityIn s 𝕍 K' ≤ C · densityIn s 𝕍 K`.  So a Frostman bound at the big body `K`
bounds the mass of the subfamily caught in any smaller body `B ≤ K` by that body's share of `K`,
times the total mass of the family.  Nothing about a maximiser, and nothing about
`Kakeya.maxDensity`, is involved.

This matters for `Kakeya.ml1Boot.multTildeT_of_planksClose`, whose open item (3) needs the count
`|{i ∈ 𝕋̃'' : T̃_i ⊆ 2 · T_{b,l}}| ≤ C · |fibre 𝕋̃'' p_b l|`.  Bounding the numerator through
`Kakeya.card_familyIn_le` charges `maxDensity 𝕋̃'' 𝕍`, which that statement does not hypothesise
and which nothing on the route bounds.  Routing it through this lemma instead charges
`frostmanConstIn 𝕋̃'' 𝕍 B₁`, which that statement *does* hypothesise, at `δ̃ ^ (-aF)`.  What is
left is then a lower bound on the fibre's share of the total mass, which is a statement about the
plank blocks alone.

The four volume side conditions are discharged for tubes and balls by `Kakeya.Tube.le_volume`
(positivity) and `Kakeya.Tube.isCompact` with `IsCompact.measure_lt_top` (finiteness); they are
what lets the two density quotients be cross-multiplied. -/
theorem sum_volume_familyIn_le_of_frostmanConstIn {ι : Type*} {s : Finset ι}
    {M : ENNReal} (V : ι → ConvexSpaceBody E) {B K : ConvexSpaceBody E}
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    (hB0 : volume B.carrier ≠ 0) (hBtop : volume B.carrier ≠ ⊤)
    (hBK : B ≤ K) (hM : frostmanConstIn s V K ≤ M) :
    (∑ i ∈ familyIn s V B, volume (V i).carrier) * volume K.carrier
      ≤ M * (volume B.carrier * ∑ i ∈ s, volume (V i).carrier) := by
  classical
  let NB : ENNReal := ∑ i ∈ familyIn s V B, volume (V i).carrier
  let NK : ENNReal := ∑ i ∈ familyIn s V K, volume (V i).carrier
  let S : ENNReal := ∑ i ∈ s, volume (V i).carrier
  change NB * volume K.carrier ≤ M * (volume B.carrier * S)
  have hFr : IsFrostmanIn s V K M := isFrostmanIn_of_frostmanConstIn_le hM
  have hdens : densityIn s V B ≤ M * densityIn s V K := hFr B hBK
  have hq : NB / volume B.carrier ≤ M * (NK / volume K.carrier) := by
    simpa [NB, NK, densityIn, familyIn] using hdens
  have hNK : NK ≤ S := by
    dsimp [NK, S]
    unfold familyIn
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hcross : NB * volume K.carrier ≤ M * (volume B.carrier * NK) := by
    calc
      NB * volume K.carrier
          = ((NB / volume B.carrier) * volume B.carrier) * volume K.carrier := by
              rw [ENNReal.div_mul_cancel hB0 hBtop]
      _ = (NB / volume B.carrier) * (volume B.carrier * volume K.carrier) := by
              rw [mul_assoc]
      _ ≤ (M * (NK / volume K.carrier)) * (volume B.carrier * volume K.carrier) := by
              exact mul_le_mul_of_nonneg_right hq zero_le
      _ = M * ((NK / volume K.carrier) * (volume B.carrier * volume K.carrier)) := by
              rw [mul_assoc]
      _ = M * (volume B.carrier * NK) := by
              congr 1
              calc
                (NK / volume K.carrier) * (volume B.carrier * volume K.carrier)
                    = (NK / volume K.carrier) * (volume K.carrier * volume B.carrier) := by
                        rw [mul_comm (volume B.carrier)]
                _ = ((NK / volume K.carrier) * volume K.carrier) * volume B.carrier := by
                        rw [← mul_assoc]
                _ = NK * volume B.carrier := by
                        rw [ENNReal.div_mul_cancel hK0 hKtop]
                _ = volume B.carrier * NK := by
                        rw [mul_comm]
  calc
    NB * volume K.carrier
        ≤ M * (volume B.carrier * NK) := hcross
    _ ≤ M * (volume B.carrier * S) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNK zero_le) zero_le

/-- **A part of a factorization carries its hull's share of the whole family's mass.**

This is the *local* half of the share the seam of `Kakeya.ml1Boot.multTildeT_of_planksClose`
needs, and it is already implied by the density clause of
`Kakeya.ConvexSpaceBody.Factorization` (Factorization.lean:96) — nothing new is assumed.

Read `densityIn s 𝕍 K ≤ maxDensity s 𝕍` (`Kakeya.le_maxDensity`, Density.lean:157) against
`maxDensity s 𝕍 ≤ C · densityIn t 𝕍 (hull t)` (the field `maxDensity_le_mul`).  With every
member of `s` inside `K`, the left quotient is the whole family's mass over `|K|`; with every
member of `t` inside its own hull, the right one is the part's mass over `|hull t|`.  Cross
multiplying gives the conclusion: a part's mass is at least `C⁻¹ · (|hull t| / |K|)` times the
family's.

For the seam this is applied at `s = fibre u'' pρ m`, `K = B₁`, `t` the plank block and `C = 2`,
where the two-sided hull volume of clause (iv) of `Kakeya.ml1Boot.exists_plankDimensions` turns
`|hull t|` into `a_p b_p`.  What it does **not** give is a share of the *whole* family `u''`: it
is stated at the index set the factorization is over, which is the `ρ`-parent fibre.  Averaging
that last step over the `ρ`-parents costs `|tρ|`, which `Kakeya.ml1Boot.card_le` bounds by
`C ρ ^ (-4) = C δ̃ ^ (-24 ε)` — a *small* power, unlike the `|t_b| ≲ b ^ (-4)` that averaging over
the `b`-tubes would cost, `b` being allowed down to `δ̃`. -/
theorem volume_convexHull_mul_sum_le_of_factorization {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {C : NNReal} (V : ι → ConvexSpaceBody E) (F : ConvexSpaceBody.Factorization s V C)
    {t : Finset ι} (ht : t ∈ F.parts) {K : ConvexSpaceBody E}
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    (hhull0 : volume (t.convexHull_biUnion V).carrier ≠ 0)
    (hhulltop : volume (t.convexHull_biUnion V).carrier ≠ ⊤)
    (hVK : ∀ i ∈ s, V i ≤ K) :
    volume (t.convexHull_biUnion V).carrier * (∑ i ∈ s, volume (V i).carrier)
      ≤ (C : ENNReal) * (volume K.carrier * ∑ i ∈ t, volume (V i).carrier) := by
  classical
  let A : ENNReal := ∑ i ∈ s, volume (V i).carrier
  let B : ENNReal := ∑ i ∈ t, volume (V i).carrier
  let H : ENNReal := volume (t.convexHull_biUnion V).carrier
  change H * A ≤ (C : ENNReal) * (volume K.carrier * B)
  -- the density comparison `Δ(𝕍, K) ≤ C · Δ(𝕍|_t, hull t)` from the two density facts
  have hchain : densityIn s V K ≤ (C : ENNReal) *
      densityIn t V (t.convexHull_biUnion V) :=
    (le_maxDensity s V K).trans (F.maxDensity_le_mul t ht)
  -- the left quotient is the whole family's mass over `|K|`, every `V i` (i ∈ s) lying in `K`
  have hleft : densityIn s V K = A / volume K.carrier := by
    dsimp [A]
    exact densityIn_of_all_le hVK
  -- the right quotient is the part's mass over `|hull|`, every `V i` (i ∈ t) lying in the hull
  have hright : densityIn t V (t.convexHull_biUnion V) = B / H := by
    dsimp [B, H]
    exact densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi)
  have hq : A / volume K.carrier ≤ (C : ENNReal) * (B / H) := by
    rw [← hleft, ← hright]
    exact hchain
  -- cross-multiply the density inequality
  have hcross : A * H ≤ (C : ENNReal) * (volume K.carrier * B) := by
    calc
      A * H = ((A / volume K.carrier) * volume K.carrier) * H := by
              rw [ENNReal.div_mul_cancel hK0 hKtop]
      _ = (A / volume K.carrier) * (volume K.carrier * H) := by
              rw [mul_assoc]
      _ ≤ ((C : ENNReal) * (B / H)) * (volume K.carrier * H) := by
              exact mul_le_mul_of_nonneg_right hq zero_le
      _ = (C : ENNReal) * ((B / H) * (volume K.carrier * H)) := by
              rw [mul_assoc]
      _ = (C : ENNReal) * (volume K.carrier * B) := by
              congr 1
              calc
                (B / H) * (volume K.carrier * H)
                    = (B / H) * (H * volume K.carrier) := by
                        rw [mul_comm (volume K.carrier)]
                _ = ((B / H) * H) * volume K.carrier := by
                        rw [← mul_assoc]
                _ = B * volume K.carrier := by
                        rw [ENNReal.div_mul_cancel hhull0 hhulltop]
                _ = volume K.carrier * B := by
                        rw [mul_comm]
  calc
    H * A = A * H := by rw [mul_comm]
    _ ≤ (C : ENNReal) * (volume K.carrier * B) := hcross

/-- **(GWZ Lemma 8.1) The fibre Frostman bound in the shape hypothesis (a) consumes**
(blueprint `cor:ml1bootDensityTransferFrostmanPower` composed with the seam).

`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow` followed by
`Kakeya.ml1Boot.frostmanConstIn_fibre_undilated_le`: under the hypotheses of the former —
including the fibre inclusion `hfibre` at the parent scale and the volume comparison `hTbvol` —
together with the plank-scale data

* `pb`, `l` — the `b`-tube parent map and the index of `Tb`,
* `hle` — the containment clause of the undilated parent family at `Tb`,
* `hcatch` — the plank-scale fibre inclusion,

the bound reads

`C_F(𝕋̃''[T_{b,l}]-fibre, T_{b,l}) ≤ 2 C_T δ̃ ^ (-ap')`,

which is verbatim hypothesis (a) of `Kakeya.ml1Boot.normalized_le_of_coarse` at the family
`u''`.  The consumer names its family `u`, so the call is the one that instantiates the
assembly at `u := u''`; the two `u`'s of this statement are the producer's pair, `u''` being
the family the planks factor.

This declaration exists to make the seam checkable in one place: it takes what the density
transfer produces and returns what the assembly asks for, with the same constant and the same
exponent, and it names the two hypotheses that are not supplied by the chain — `hfibre` and
`hcatch`, which are the same assumption at two scales by
`Kakeya.ml1Boot.familyIn_subset_of_familyIn_subset_of_le`, and `hTbvol`, which
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` does produce at exactly this constant but
which `Kakeya.ml1Boot.exists_plankTube_parentFamily` does not export. -/
theorem frostmanConstIn_fibre_le_rpow_atTube [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1) (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ap' : ℝ} (hap' : 0 ≤ ap')
    (hratio : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ap'))
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu : u.Nonempty) (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {m : κ} (hm : m ∈ tρ) {part : Finset ι} (hpart : part ∈ (F m).parts)
    (Tb : Tube bq E)
    (hTb : part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate Tb 2)
    (hTbsub : Tube.dilate Tb 2 ≤ Tube.dilate (Tρ m) (plankTubeInParent.C : ℝ))
    (hTbvol : volume (Tube.dilate Tb 2).carrier ≤ (densityTransfer.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal))
      * volume (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier)
    (hfibre : ∀ K : ConvexSpaceBody E, K ≤ Tube.dilate Tb 2 →
      familyIn u'' (fun i => (T i).toConvexSpaceBody) K ⊆ fibre u'' pρ m)
    {κ' : Type*} [DecidableEq κ'] (pb : ι → κ') (l : κ')
    (hle : ∀ i ∈ u'', pb i = l → (T i).toConvexSpaceBody ≤ Tb.toConvexSpaceBody)
    (hcatch : familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)
      ⊆ fibre u'' pb l) :
    frostmanConstIn (fibre u'' pb l) (fun i => (T i).toConvexSpaceBody)
        Tb.toConvexSpaceBody
      ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
  exact frostmanConstIn_fibre_undilated_le (T := T) (p := pb) (l := l) (Tb := Tb) hle hcatch
    (frostmanConstIn_fibre_le_rpow hdim hδt hδa hab hbρ hρ1 hbbq hbq hap' hratio
      T Tρ pρ hu hu'' hball hparent F hdims hm hpart Tb hTb hTbsub hTbvol hfibre)

/-- **The exponent arithmetic behind the plank-width contradiction** (blueprint
`lem:ml1bootSmallBExponent`).

Let `0 < δ̃ ≤ 1`, `A ≥ 1`, `ε, n > 0` and `e, ap' ≥ 0` with `ap' + e ≤ ε n / 2`.  If
`δ̃ ^ (e - ε n) < A δ̃ ^ (-ap')` then `δ̃ ^ (-ε n / 2) < A`.  Equivalently: once
`δ̃ ^ (-ε n / 2) ≥ A`, the displayed inequality is impossible.

This is the whole content of the "for `δ̃` small" step of
`Kakeya.ml1Boot.plankWidth_le`, isolated so that the geometric lemma is a contradiction
between two Frostman bounds and nothing more.  `n` is `η_j` and `ap'` is `η'_{j-1}`. -/
theorem plankWidth_exponent_contradiction {δt : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1)
    {A : ENNReal} (_hA : 1 ≤ A) (_hAtop : A ≠ ⊤)
    {ε n e ap' : ℝ} (_hε0 : 0 < ε) (_hn : 0 < n) (_he : 0 ≤ e) (_hap' : 0 ≤ ap')
    (hsmall : ap' + e ≤ ε * n / 2)
    (hlt : (δt : ENNReal) ^ (e - ε * n) < A * (δt : ENNReal) ^ (-ap')) :
    (δt : ENNReal) ^ (-(ε * n / 2)) < A := by
  let d : ENNReal := (δt : ENNReal)
  have hd0ne : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (ne_of_gt hδt0)
  have hdtop : d ≠ ⊤ := by
    dsimp [d]
    exact ENNReal.coe_ne_top
  have hd1 : d ≤ 1 := by
    dsimp [d]
    exact_mod_cast hδt1
  have hmult0 : d ^ ap' ≠ 0 := by
    dsimp
    simp [ENNReal.rpow_eq_zero_iff, hd0ne, hdtop]
  have hmulttop : d ^ ap' ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hd0ne hdtop
  -- multiply `hlt` on the right by `d ^ ap'`
  have hmult : d ^ (e - ε * n) * d ^ ap' < (A * d ^ (-ap')) * d ^ ap' := by
    have h1 := (ENNReal.mul_lt_mul_iff_right (a := d ^ ap') hmult0 hmulttop).mpr hlt
    rwa [mul_comm (d ^ ap'), mul_comm (d ^ ap')] at h1
  have hL : d ^ (e - ε * n + ap') < (A * d ^ (-ap')) * d ^ ap' := by
    rwa [← ENNReal.rpow_add (e - ε * n) ap' hd0ne hdtop] at hmult
  have hRHS : (A * d ^ (-ap')) * d ^ ap' = A := by
    rw [mul_assoc]
    rw [← ENNReal.rpow_add (-ap') ap' hd0ne hdtop]
    rw [neg_add_cancel, ENNReal.rpow_zero, mul_one]
  have hmid : d ^ (e - ε * n + ap') < A := by
    rwa [hRHS] at hL
  have hmono : d ^ (-(ε * n / 2)) ≤ d ^ (e - ε * n + ap') := by
    apply ENNReal.rpow_le_rpow_of_exponent_ge hd1
    linarith [hsmall]
  exact lt_of_le_of_lt hmono hmid

/-- **(GWZ Lemma 8.1) The plank width `b` is nearly as small as `δ̃`** (blueprint
`lem:ml1bootSmallB`).

Let `ap' = η'_{j-1}`, `n = η_j` and a loss exponent `e ≥ 0` satisfy the first inequality of
`eq:ml1bootEtaPrimeBounds` in its loss-corrected form, `ap' + e ≤ ε n / 2`, and let `C ≥ 1` be
the constant of `Kakeya.ml1Boot.exists_normalizedMiddleData`.  Then for all sufficiently small
`δ̃ > 0` the plank width satisfies `b ≤ δ̃ ^ (1 - ε)`.

The loss here is a power of the *rescaled* scale `δ̃`, whereas
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) supplies it as a power `δ ^ e₀` of the outer
scale.  Only `δ̃ ≤ δ ^ ε` relates the two, so `δ ^ e₀ ≥ δ̃ ^ (e₀ / ε)` and the exponent to be
paid for here is `e = e₀ / ε`; with the intended `e₀ = η₀` that is `e = η₀ / ε`, which is
exactly the summand in the corrected bound of `Kakeya.ml1Boot.params_spec`(iii).

The proof is by contradiction: if `b > δ̃ ^ (1 - ε)` then `b` lies in the interval of
`tildeDeltaLargeFrostman`, whose lower bound `C⁻¹ δ̃ ^ e (b/δ̃) ^ n > C⁻¹ δ̃ ^ (e - ε n)`
contradicts the upper bound `2 C_T δ̃ ^ (-ap')` of
`Kakeya.ml1Boot.frostmanConstIn_fibre_le` once `δ̃` is small, precisely because
`e - ε n < -ap'`.  This is the one place where the lower Frostman bound of
`dividingScalesLemmaA`(ii) is used at all, and the hypothesis is stated exactly in the
conditional form, and with exactly the loss `δ̃ ^ e`, in which it is available.

The scale `bq` here is the **honest tube scale** of the `b`-tube, i.e. `b♯ ∈ [b, C_𝕎 b]` in
the notation of `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one`, and not the plank
width `b`: the two hypotheses are both statements about one and the same tube `Tb`, so the
argument has to run at that tube's scale.  The requirement `bq ≤ δt ^ ε` is what places `bq`
inside the interval `[δ̃ ^ (1 - ε), δ̃ ^ ε]` on which
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) supplies the lower bound.

The window half-width `ε` here is a *free parameter*, not the package's `ε`: the assembly
instantiates it at `5 p.ε`, because that is the window on which
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) — and behind it
`Kakeya.ml1Boot.exists_caseTwoData`(iv) — speaks.  At that instantiation the requirement
`bq ≤ δ̃ ^ (5 p.ε)` holds because the plank data is produced at parent scale
`ρ = δ̃ ^ (6 p.ε)`, so `bq ≤ C_𝕎 δ̃ ^ (6 p.ε) ≤ δ̃ ^ (5 p.ε)` for small `δ̃`; the smallness
hypothesis `ap' + e ≤ ε n / 2` becomes the *relaxed* budget `ap' + e ≤ 5 p.ε n / 2`, which
`Kakeya.ml1Boot.Params.Spec.etaPrimeLossLe` supplies a fortiori; and the conclusion becomes
`bq ≤ δ̃ ^ (1 - 5 p.ε)`, which is what `Kakeya.ml1Boot.multiplicity_coarse_le` consumes.  See
blueprint `note:ml1bootWindowConsumers`(3).

Both Frostman hypotheses are statements about `Kakeya.Tube.dilate Tb 2` and not about `Tb`.
The upper one has to be, since that is the shape in which
`Kakeya.ml1Boot.frostmanConstIn_fibre_le` produces it; and the argument compares the two
bounds for one and the same convex body, so the lower one must be read on the dilate as well.
This is the obligation that `Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) is strengthened
to discharge: it supplies its lower bound for `Kakeya.Tube.dilate Tρ 2`. -/
theorem plankWidth_le [Nontrivial E]
    {ε ap' n e : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (_hap' : 0 < ap') (hn : 0 < n) (_he : 0 ≤ e)
    (hsmall : ap' + e ≤ ε * n / 2) (C : NNReal) (hC : 1 ≤ C) :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ bq : NNReal, δt ≤ bq → bq ≤ δt ^ ε →
      ∀ {ι : Type*} {u'' : Finset ι} (T : ι → Tube δt E) (Tb : Tube bq E),
        u''.Nonempty →
        ((δt : NNReal) ^ (1 - ε) ≤ bq →
          (C : ENNReal)⁻¹ * (δt : ENNReal) ^ e * ((bq / δt : NNReal) : ENNReal) ^ n
            ≤ frostmanConstIn
                (familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
                (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)) →
        frostmanConstIn
            (familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
            (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)
          ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') →
        bq ≤ δt ^ (1 - ε) := by
  set M0 : ENNReal := 2 * (C : ENNReal) * (densityTransfer.C : ENNReal) with hM0def
  set M : ENNReal := M0 + 1 with hMdef
  let α : ℝ := ε * n / 2
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hM0top : M0 ≠ ⊤ := by
    dsimp [M0]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ne_of_lt ENNReal.coe_lt_top) ENNReal.coe_ne_top) ENNReal.coe_ne_top
  have hMone : 1 ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_left (by positivity : 0 ≤ M0)
  have hMpos : 0 < M := zero_lt_one.trans_le hMone
  have hMtop : M ≠ ⊤ := by
    dsimp [M]
    exact ENNReal.add_ne_top.mpr ⟨hM0top, ENNReal.coe_ne_top⟩
  have hMpowtop : M ^ (-1 / α) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hMpos hMtop
  have hδ₁ : (0 : NNReal) < min 1 (M ^ (-1 / α)).toNNReal :=
    lt_min zero_lt_one (by
      rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal hMpowtop]
      exact ENNReal.rpow_pos hMpos hMtop)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)]
    with δt (hδt_pos : 0 < δt) hδt_lt
  intro bq _hδbq _hbqε ι u'' T Tb _hu'' hfrost_low hfrost_up
  by_contra hnot
  have h1ε : (δt : NNReal) ^ (1 - ε) < bq := lt_of_not_ge hnot
  have h1εle : (δt : NNReal) ^ (1 - ε) ≤ bq := h1ε.le
  have hlow := hfrost_low h1εle
  have hchain := hlow.trans hfrost_up
  have hdne : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδt_pos.ne'
  have hdnetop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδt1 : δt ≤ 1 := hδt_lt.le.trans (min_le_left _ _)
  have hd1 : (δt : ENNReal) ≤ 1 := by exact_mod_cast hδt1
  have h1εleE : (δt : ENNReal) ^ (1 - ε) ≤ (bq : ENNReal) := by
    rw [ENNReal.rpow_ofNNReal (by linarith : 0 ≤ 1 - ε)]
    exact_mod_cast h1εle
  have hdiv : (δt : ENNReal) ^ (-ε) ≤ ((bq / δt : NNReal) : ENNReal) := by
    calc
      (δt : ENNReal) ^ (-ε) = (δt : ENNReal) ^ ((1 - ε) + (-1 : ℝ)) := by congr 1; ring
      _ = (δt : ENNReal) ^ (1 - ε) * (δt : ENNReal) ^ (-1 : ℝ) := by
        rw [ENNReal.rpow_add (x := (δt : ENNReal)) (1 - ε) (-1 : ℝ) hdne hdnetop]
      _ ≤ (bq : ENNReal) * (δt : ENNReal) ^ (-1 : ℝ) :=
        mul_le_mul_left h1εleE ((δt : ENNReal) ^ (-1 : ℝ))
      _ = (bq : ENNReal) / (δt : ENNReal) := by
        rw [ENNReal.rpow_neg (x := (δt : ENNReal)) (1 : ℝ)]
        simp [div_eq_mul_inv]
      _ = ((bq / δt : NNReal) : ENNReal) := by
        rw [ENNReal.coe_div hδt_pos.ne']
  have hpow : (δt : ENNReal) ^ (-(ε * n)) ≤ ((bq / δt : NNReal) : ENNReal) ^ n := by
    calc
      (δt : ENNReal) ^ (-(ε * n)) = ((δt : ENNReal) ^ (-ε)) ^ n := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
      _ ≤ ((bq / δt : NNReal) : ENNReal) ^ n := ENNReal.rpow_le_rpow hdiv hn.le
  have hA : (C : ENNReal)⁻¹ * (δt : ENNReal) ^ e * (δt : ENNReal) ^ (-(ε * n))
      ≤ (C : ENNReal)⁻¹ * (δt : ENNReal) ^ e * ((bq / δt : NNReal) : ENNReal) ^ n := by
    exact mul_le_mul_right hpow ((C : ENNReal)⁻¹ * (δt : ENNReal) ^ e)
  have hB : (C : ENNReal)⁻¹ * (δt : ENNReal) ^ e * (δt : ENNReal) ^ (-(ε * n))
      ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') :=
    hA.trans hchain
  have hB' : (C : ENNReal)⁻¹ * (δt : ENNReal) ^ (e - ε * n)
      ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') := by
    calc
      (C : ENNReal)⁻¹ * (δt : ENNReal) ^ (e - ε * n)
          = (C : ENNReal)⁻¹ * ((δt : ENNReal) ^ e * (δt : ENNReal) ^ (-(ε * n))) := by
            rw [sub_eq_add_neg]
            rw [ENNReal.rpow_add (x := (δt : ENNReal)) e (-(ε * n)) hdne hdnetop]
      _ = (C : ENNReal)⁻¹ * (δt : ENNReal) ^ e * (δt : ENNReal) ^ (-(ε * n)) := by rw [← mul_assoc]
      _ ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') := hB
  have hCne0 : (C : ENNReal) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (zero_lt_one.trans_le hC) : 0 < (C : ENNReal))
  have hCnetop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCmul := mul_le_mul_right hB' (C : ENNReal)
  have hC : (δt : ENNReal) ^ (e - ε * n)
      ≤ (C : ENNReal) * (2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap')) := by
    calc
      (δt : ENNReal) ^ (e - ε * n)
          = (C : ENNReal) * ((C : ENNReal)⁻¹ * (δt : ENNReal) ^ (e - ε * n)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hCne0 hCnetop, one_mul]
      _ ≤ (C : ENNReal) * (2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap')) := hCmul
  have hXd : (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ ap' = 1 := by
    calc
      (δt : ENNReal) ^ (-ap') * (δt : ENNReal) ^ ap' = (δt : ENNReal) ^ (-ap' + ap') := by
        rw [ENNReal.rpow_add (x := (δt : ENNReal)) (-ap') ap' hdne hdnetop]
      _ = (δt : ENNReal) ^ (0 : ℝ) := by congr 1; ring
      _ = 1 := by simp
  have hD := mul_le_mul_left hC ((δt : ENNReal) ^ ap')
  have hD' : (δt : ENNReal) ^ (e - ε * n + ap') ≤ M0 := by
    calc
      (δt : ENNReal) ^ (e - ε * n + ap') = (δt : ENNReal) ^ (e - ε * n) * (δt : ENNReal) ^ ap' := by
        rw [ENNReal.rpow_add (x := (δt : ENNReal)) (e - ε * n) ap' hdne hdnetop]
      _ ≤ (C : ENNReal) * (2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap'))
            * (δt : ENNReal) ^ ap' := hD
      _ = M0 := by
        dsimp [M0]
        rw [mul_assoc, mul_assoc]
        rw [hXd]
        ring
  have hsmallE : e - ε * n + ap' ≤ -α := by
    dsimp [α]
    nlinarith [hsmall]
  have hmain : (δt : ENNReal) ^ (-α) ≤ M0 := by
    calc
      (δt : ENNReal) ^ (-α) ≤ (δt : ENNReal) ^ (e - ε * n + ap') :=
        ENNReal.rpow_le_rpow_of_exponent_ge hd1 hsmallE
      _ ≤ M0 := hD'
  have hM0ltM : M0 < M := by
    dsimp [M]
    exact ENNReal.lt_add_right hM0top (by norm_num : (1 : ENNReal) ≠ 0)
  have hMle : M ≤ (δt : ENNReal) ^ (-α) := by
    have hδ : (δt : ENNReal) ≤ M ^ (-1 / α) := by
      calc
        (δt : ENNReal) ≤ ((M ^ (-1 / α)).toNNReal : ENNReal) :=
          ENNReal.coe_le_coe.mpr (hδt_lt.le.trans (min_le_right _ _))
        _ = M ^ (-1 / α) := ENNReal.coe_toNNReal hMpowtop
    have h := ENNReal.rpow_le_rpow hδ hα0.le
    rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ hα0.ne', ENNReal.rpow_neg_one] at h
    rw [ENNReal.rpow_neg (δt : ENNReal) α]
    exact ENNReal.le_inv_iff_le_inv.mp h
  exact (not_lt_of_ge hmain) (lt_of_lt_of_le hM0ltM hMle)

/-- **(GWZ Lemma 8.1) The plank width is small, from the anchor route** (blueprint
`cor:ml1bootSmallBAnchor`).

Write `C_T = Kakeya.ml1Boot.densityTransfer.C`.  For all sufficiently small `δ̃ > 0`: let
`δ̃ ≤ b♯ ≤ δ̃ ^ ε`, let `T_b` be a tube of scale `b♯`, put `K = 2 · T_b` — the body at which
`Kakeya.ml1Boot.plankWidth_le` runs its collision — and let `𝕍 = (T̃_k)_{k ∈ u''}` be the
*unrefined* family, `u''` nonempty.  Assume

* *the lower side* `hfrost_low` — the free-scale Frostman lower bound of
  `Kakeya.ml1Boot.plankWidth_le`, read at the ambient family `𝕍` and at the `2`-dilate;
* *the upper side* — the numerator hypothesis of
  `Kakeya.ml1Boot.frostmanConstIn_anchor_le` and its denominator bundle
  `Kakeya.ml1Boot.IsAnchorDenominator`, at `𝕍`, at this anchor `K`, with data `U, L, t, a, b`
  (there is no normalization hypothesis: that lemma no longer has one);
* *the exponent collection* `hcollect` — `C_T (b/a) U / L ≤ 2 C_T δ̃ ^ (-ap')`.

Then `b♯ ≤ δ̃ ^ (1 - ε)`.

This is a two-line composition and is a declaration of its own for exactly that reason: it is
`Kakeya.ml1Boot.frostmanConstIn_anchor_le` followed by `Kakeya.ml1Boot.plankWidth_le`, and
nothing else.  **No exponent arithmetic happens here**: all of it is inside
`Kakeya.ml1Boot.plankWidth_exponent_contradiction`, which `Kakeya.ml1Boot.plankWidth_le`
already carries, and the smallness condition on `δ̃` is that lemma's.

**`hcollect` is a hypothesis, not a discharged step.**  It is the one place where the two
sides of Step 5c's collision are made to be about the same power of `δ̃`, and this development
does not establish that the intended instantiations of `U` and `L` — `U` from
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` read at the container `B = K`, and `L` a
constant multiple of `Δ_max` of the retained share — satisfy it.  Making that substitution is
a separate obligation and is not performed here or anywhere below.

The window half-width `ε` is a *free parameter*, as in `Kakeya.ml1Boot.plankWidth_le`; the
assembly instantiates it at `5 p.ε`.  Both Frostman sides are statements about
`Kakeya.Tube.dilate Tb 2` and not about `Tb`, and about one and the same family `𝕍`, which is
what makes them collidable at all. -/
theorem plankWidth_le_of_anchor [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {ε ap' n e : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hap' : 0 < ap') (hn : 0 < n) (he : 0 ≤ e)
    (hsmall : ap' + e ≤ ε * n / 2) (C : NNReal) (hC : 1 ≤ C) :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ bq : NNReal, δt ≤ bq → bq ≤ δt ^ ε →
      ∀ {ι : Type*} (u'' t : Finset ι) (T : ι → Tube δt E) (Tb : Tube bq E)
        (ap bp : NNReal) (U L : ENNReal),
        u''.Nonempty → 0 < ap → ap ≤ bp →
        ((δt : NNReal) ^ (1 - ε) ≤ bq →
          (C : ENNReal)⁻¹ * (δt : ENNReal) ^ e * ((bq / δt : NNReal) : ENNReal) ^ n
            ≤ frostmanConstIn
                (familyIn u'' (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2))
                (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tb 2)) →
        (∀ K' : ConvexSpaceBody E, K' ≤ Tube.dilate Tb 2 →
          densityIn u'' (fun i => (T i).toConvexSpaceBody) K' ≤ U) →
        IsAnchorDenominator T (Tube.dilate Tb 2) ap bp u'' t L →
        (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * (U / L)
            ≤ 2 * (densityTransfer.C : ENNReal) * (δt : ENNReal) ^ (-ap') →
        bq ≤ δt ^ (1 - ε) := by
  filter_upwards [plankWidth_le (E := E) hε0 hε1 hap' hn he hsmall C hC] with δt hδt
  intro bq hδbq hbqε ι u'' t T Tb ap bp U L hu'' hap0 hab hfrost_low hnum hanch hcollect
  exact hδt bq hδbq hbqε (u'' := u'') (T := T) (Tb := Tb) hu'' hfrost_low
    (le_trans
      (frostmanConstIn_anchor_le (hdim := hdim) (δt := δt) (ap := ap) (bp := bp) (ι := ι)
        (u'' := u'') (t := t) (T := T) (K := Tube.dilate Tb 2) (U := U) (L := L)
        (hap0 := hap0) (hab := hab) (hnum := hnum) (hanch := hanch))
      hcollect)

end DensityTransfer

end ml1Boot

end Kakeya
