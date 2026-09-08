/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreFrostmanReduction
public import Kakeya.FrostmanConstant

/-!
# The Frostman hypothesis for the extracted tube subfamily

`Kakeya.FrostmanEstimate.multiplicity_bound` (GWZ Lemma 3.9) consumes
`ConvexSpaceBody.IsFrostmanIn sub (fun Q ↦ (T Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall CF`.
Section 6 produces instead the *scalar* bound

`C_F(fibre, S) ≤ Cloc · CF · (|𝒯| / |fibre|) · |S|`

on the fibre's **prisms** (`Plank.frostmanThickenedSlabFibre`). This module carries that bound to
the extracted pairwise-essentially-distinct tube subfamily.

## The route

Everything is carried in `Kakeya.maxDensity`, never in a Frostman predicate, so that only existing
API is needed; the predicate is entered exactly once, at the very end, through
`Kakeya.isFrostmanIn_of_maxDensity_mul_volume_le` (i.e. `IsFrostmanIn.of_maxDensity_le`):

1. `Plank.maxDensity_fibre_prisms_le` clears the division in the hypothesis
   (`Kakeya.maxDensity_mul_volume_le_of_frostmanConstant_le`) and cancels `|S|` against itself and
   `1 / |fibre|` against `∑_{fibre} |Q| = |fibre| · 8 θ b²`. The factor `|𝒯|` **survives** and is
   visible in the statement — it is needed for the later summation over slabs.
2. `Plank.maxDensity_slabFibreTubes_le` transports that to the tubes:
   * prisms ⊆ `Cfib`-dilated shading bodies, with volume ratio `Cfib³`
     (`Kakeya.maxDensity_le_of_subset_of_volume_le`);
   * the normalising map is invisible to `Δ_max` (`Kakeya.maxDensity_mapAffine`);
   * tubes versus normalised shading bodies costs `Plank.fibreTubeLoss Cfib`
     (`Plank.maxDensity_ktTubeFamily_le`);
   * passing to `sub ⊆ fibre` only decreases `Δ_max` (`Kakeya.maxDensity_mono`) — this is why no
     cardinality retention is needed for the Frostman side.
3. `Plank.isFrostmanIn_slabFibreTubes_sub` assembles the two and enters the predicate.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

variable {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}

/-- The total prism volume of a fibre: every `Plank.ThickenedPlank θ b` has volume `8 (θ b) b`. -/
theorem sum_volume_thickenedPlank (fibre : Finset (ThickenedPlank θ b hθ1 hb1)) :
    ∑ Q ∈ fibre, volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (fibre.card : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal) := by
  have hvol : ∀ Q : ThickenedPlank θ b hθ1 hb1,
      volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ((8 * (θ * b) * b : ℝ≥0) : ENNReal) := fun Q => by
    rw [Prism3D.volume_carrier Q, ENNReal.coe_one, mul_one]
    rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
  rw [Finset.sum_congr rfl (fun Q _ => hvol Q), Finset.sum_const, nsmul_eq_mul]

/-- **The maximal density of the fibre prisms, with `|S|` and `1 / |fibre|` cancelled.**

Clearing the division in the Section 6 Frostman hypothesis and substituting
`∑_{fibre} |Q| = |fibre| · 8 θ b²` cancels the reference volume `|S|` outright and turns
`|𝒯| / |fibre|` into a bare `|𝒯|`. Nothing is hidden: the surviving `|𝒯| · 8 θ b²` is exactly what
the per-slab estimate needs to keep for the later summation over slabs. -/
theorem maxDensity_fibre_prisms_le {fibre 𝒯 : Finset (ThickenedPlank θ b hθ1 hb1)}
    {S : Slab θ hθ1} {Cloc : ℝ≥0} {CF : ENNReal}
    (hθ0 : 0 < θ) (hb0 : 0 < b) (hfibre_ne : fibre.Nonempty)
    (hS0 : volume S.carrier ≠ 0)
    (hfrost : Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
      ≤ (Cloc : ENNReal) * CF * ((𝒯.card : ENNReal) / (fibre.card : ENNReal))
          * volume S.carrier) :
    Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody)
      ≤ (Cloc : ENNReal) * CF * (𝒯.card : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal) := by
  let v : ENNReal := ((8 * (θ * b) * b : ℝ≥0) : ENNReal)
  let n : ENNReal := (fibre.card : ENNReal)
  let m : ENNReal := (𝒯.card : ENNReal)
  let A : ENNReal := (Cloc : ENNReal) * CF
  let Sv : ENNReal := volume S.carrier
  let M : ENNReal := Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody)
  have hcard0 : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Finset.card_ne_zero.mpr hfibre_ne)
  have hcardtop : n ≠ ⊤ := by
    dsimp [n]
    exact ENNReal.natCast_ne_top fibre.card
  have hv0 : v ≠ 0 := by
    dsimp [v]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (by positivity : 0 < ((8 * (θ * b) * b : ℝ≥0))))
  have hmass : (∑ Q ∈ fibre, volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ≠ 0 := by
    rw [Plank.sum_volume_thickenedPlank fibre]
    exact mul_ne_zero hcard0 hv0
  have h1 := Kakeya.maxDensity_mul_volume_le_of_frostmanConstant_le hmass hfrost
  rw [Plank.sum_volume_thickenedPlank fibre] at h1
  have h1' : M * Sv ≤ (A * (m / n)) * Sv * (n * v) := by
    simpa [M, Sv, A, m, n, v] using h1
  have hkey : (m / n) * n = m := by
    dsimp [m, n]
    exact ENNReal.div_mul_cancel hcard0 hcardtop
  have hle : M * Sv ≤ (A * m * v) * Sv := by
    calc
      M * Sv ≤ (A * (m / n)) * Sv * (n * v) := h1'
      _ = (A * ((m / n) * n) * v) * Sv := by ac_rfl
      _ = (A * m * v) * Sv := by rw [hkey]
  have hS0' : Sv ≠ 0 := by
    dsimp [Sv]
    exact hS0
  have hStop : Sv ≠ ⊤ := by
    dsimp [Sv]
    exact S.toConvexSpaceBody.isCompact.measure_ne_top
  change M ≤ A * m * v
  exact (ENNReal.mul_le_mul_iff_left hS0' hStop).mp hle

variable {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
  {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
  {S : Slab θ hθ1} {Cfib : ℝ≥0}

/-- **The total carrier volume of a fibre's shading bodies.** Each `Yθ Q` is the `Cfib`-dilation of
the prism `Q` (`Plank.SlabFibreGeometry.shade_body`), so its volume is `Cfib³ · 8 (θ b) b`.

Together with `ShadedBody.sum_shade_eq_fullness'_mul` this turns the Section 6 fullness hypothesis
`c₂ a^{4η} ≤ λ(fibre, Yθ)` into the shade-mass lower bound that
`Plank.sum_shade_le_of_multiplicity_le` consumes. -/
theorem sum_volume_carrier_shadeBody (h : SlabFibreGeometry fibre Yθ S Cfib) :
    ∑ Q ∈ fibre, volume ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((Cfib : ℝ≥0) : ENNReal) ^ 3
          * ((fibre.card : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal)) := by
  have hpoint : ∀ Q ∈ fibre,
      volume ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ((Cfib : ℝ≥0) : ENNReal) ^ 3
            * volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro Q hQ
    rw [h.shade_body Q hQ]
    rw [PrismNDim.volume_dilation]
  rw [Finset.sum_congr rfl (fun Q hQ => hpoint Q hQ), ← Finset.mul_sum,
    sum_volume_thickenedPlank fibre]

/-- The `Cfib`-dilated shading body of a fibre prism contains the prism and has `Cfib³` times its
volume — the two pointwise inputs of `Kakeya.maxDensity_le_of_subset_of_volume_le`. -/
theorem maxDensity_shadeBody_le (h : SlabFibreGeometry fibre Yθ S C) (hCfib : 1 ≤ C) :
    Kakeya.maxDensity fibre (fun Q => (Yθ Q).toConvexSpaceBody)
      ≤ ((C : ℝ≥0) : ENNReal) ^ 3
          * Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody) := by
  refine Kakeya.maxDensity_le_of_subset_of_volume_le fibre
      (fun Q => Q.toConvexSpaceBody) (fun Q => (Yθ Q).toConvexSpaceBody) ?_ ?_
  · intro Q hQ
    rw [h.shade_body Q hQ]
    exact PrismNDim.self_subset_dilation Q.toPrismNDim hCfib
  · intro Q hQ
    rw [h.shade_body Q hQ]
    rw [PrismNDim.volume_dilation]

/-- **Maximal density transport: fibre prisms to the extracted tube subfamily.**

`Δ_max(sub, T) ≤ fibreTubeLoss Cfib · Cfib³ · Δ_max(fibre, prisms)`. Passing to the subfamily
costs nothing (`Kakeya.maxDensity_mono`), the normalising map costs nothing
(`Kakeya.maxDensity_mapAffine`), the tube-versus-core inflation costs `Plank.fibreTubeLoss Cfib`,
and the prism-versus-dilated-shading-body inflation costs `Cfib³`. -/
theorem maxDensity_slabFibreTubes_le (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {sub : Finset (ThickenedPlank θ b hθ1 hb1)} (hsub : sub ⊆ fibre) :
    Kakeya.maxDensity sub
        (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody)
      ≤ ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3
          * Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody) := by
  calc
    Kakeya.maxDensity sub (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody)
      ≤ Kakeya.maxDensity fibre
          (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody) :=
        Kakeya.maxDensity_mono _ hsub
    _ ≤ ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) *
          Kakeya.maxDensity fibre (fun Q => ((Yθ Q).toConvexSpaceBody).mapAffine
            (slabFibreNormalisation Cfib S hθ0)) := by
      calc
        Kakeya.maxDensity fibre
            (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody)
          ≤ (40 * (1 + ((3 * Cfib : ℝ≥0) : ENNReal)) ^ 3 * (1 + ((Cfib : ℝ≥0) : ENNReal)) ^ 3) *
              Kakeya.maxDensity fibre (fun Q => ((Yθ Q).toConvexSpaceBody).mapAffine
                (slabFibreNormalisation Cfib S hθ0)) := by
            simpa [slabFibreTubes, slabFibreNormalisation, fibreTubeConst] using
              (maxDensity_ktTubeFamily_le (s := fibre) (V := fun Q => Q) (Y := Yθ)
                (Cset := Cfib) (Cdil := Cfib) (Cang := 3 * Cfib) (S := S)
                hθ0 hCfib (fun Q hQ => h.mem_slabFamilyC hQ)
                (fun Q hQ => slabFibre_shade_body_thickened h hQ))
        _ = ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) *
              Kakeya.maxDensity fibre (fun Q => ((Yθ Q).toConvexSpaceBody).mapAffine
                (slabFibreNormalisation Cfib S hθ0)) := by
          congr 1
    _ = ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) *
          Kakeya.maxDensity fibre (fun Q => (Yθ Q).toConvexSpaceBody) := by
        rw [Kakeya.maxDensity_mapAffine]
    _ ≤ ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) *
          (((Cfib : ℝ≥0) : ENNReal) ^ 3 *
            Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody)) := by
        gcongr
        exact maxDensity_shadeBody_le h hCfib
    _ = ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3 *
          Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody) := by
        ring

/-- **The Frostman hypothesis for the extracted tube subfamily, in the exact form GWZ Lemma 3.9
consumes.**

The constant `CFtube` is left free, constrained only by the displayed inequality: the caller
(`Plank.frostmanSlabUnionVolumeLowerBound`) picks it together with the lower bound
`∑_{sub} |T Q| ≥ |sub| · c₃ · (b/8)²` coming from `Tube.le_volume`. The factor `|𝒯| · 8 θ b²` is
kept explicit, as it must be for the summation over slabs. -/
theorem isFrostmanIn_slabFibreTubes_sub {𝒯 : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Cloc : ℝ≥0} {CF CFtube : ENNReal}
    (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) (hb0 : 0 < b) (hfibre_ne : fibre.Nonempty) (hS0 : volume S.carrier ≠ 0)
    {sub : Finset (ThickenedPlank θ b hθ1 hb1)} (hsub : sub ⊆ fibre)
    (hfrost : Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
      ≤ (Cloc : ENNReal) * CF * ((𝒯.card : ENNReal) / (fibre.card : ENNReal))
          * volume S.carrier)
    (hCFtube :
      ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3
          * ((Cloc : ENNReal) * CF * (𝒯.card : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))
          * volume (ConvexSpaceBody.closedUnitBall :
              ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
        ≤ CFtube * ∑ Q ∈ sub,
            volume ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) :
    ConvexSpaceBody.IsFrostmanIn sub
      (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall CFtube := by
  refine Kakeya.isFrostmanIn_of_maxDensity_mul_volume_le
    (s := sub) (W := fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody)
    (K := ConvexSpaceBody.closedUnitBall) (C := CFtube) ?_ ?_ ?_
  · intro Q _
    exact SetLike.coe_subset_coe.mp
      (slabFibreTubes_carrier_subset_closedBall h hCfib hθ0 Q)
  · rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact (Metric.measure_closedBall_pos volume 0 (by norm_num : (0:ℝ) < 1)).ne'
  · calc
      Kakeya.maxDensity sub (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toConvexSpaceBody)
          * volume (ConvexSpaceBody.closedUnitBall :
              ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
        ≤ (((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3 *
            Kakeya.maxDensity fibre (fun Q => Q.toConvexSpaceBody)) *
            volume (ConvexSpaceBody.closedUnitBall :
              ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier := by
          gcongr
          exact maxDensity_slabFibreTubes_le h hCfib hθ0 hsub
      _ ≤ (((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3 *
            ((Cloc : ENNReal) * CF * (𝒯.card : ENNReal) *
              ((8 * (θ * b) * b : ℝ≥0) : ENNReal))) *
            volume (ConvexSpaceBody.closedUnitBall :
              ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier := by
          gcongr
          exact maxDensity_fibre_prisms_le hθ0 hb0 hfibre_ne hS0 hfrost
      _ ≤ CFtube * ∑ Q ∈ sub,
            volume ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) := by
        simpa [mul_assoc] using hCFtube

end Plank

end
