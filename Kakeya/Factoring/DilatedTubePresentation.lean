/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Homothety
public import Kakeya.Factoring.RhoTubes
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.EDUpToMult
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.Tube.Rescale

/-!
# Presenting dilated tube factors as honest tubes

The outer factor produced by the dilated Proposition 5.1 pipeline is body-valued: its carrier is
the homothetic dilate `c · T` of a tube.  A single homothety about the origin with ratio `c⁻¹`
turns every such carrier into an honest tube of the original radius.  Since the same map is used
for the whole family, multiplicity, fullness and Frostman constants are transported exactly.

The resulting honest tubes need not remain pairwise essentially distinct.  The last theorem in
this file records the correct replacement: if the original tubes are pairwise essentially
distinct, then the presented family is essentially distinct up to an explicit constant depending
only on the ambient dimension and on `c`.  This is enough for a weighted ED extraction after the
factor has been selected.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Tube

private theorem norm_sub_inner_smul_le_local {G : E} (hG : ‖G‖ = 1) (x : E) :
    ‖x - inner ℝ G x • G‖ ≤ ‖x‖ := by
  have hGG : (inner ℝ G G : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hG]
    norm_num
  have hsq : ‖x - inner ℝ G x • G‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ G x : ℝ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, hGG,
      conj_trivial, real_inner_comm G x]
    ring
  have hle : ‖x - inner ℝ G x • G‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (inner ℝ G x : ℝ)]
  nlinarith [norm_nonneg (x - inner ℝ G x • G), norm_nonneg x, hle]

/-- The honest tube obtained by applying the common homothety `x ↦ c⁻¹ x` to `c · T`.

Its direction and radius are those of `T`; only its centre is translated, from `T.center` to
`c⁻¹ • T.center`. -/
def undilateAtZero {ρ : NNReal} (c : ℝ) (T : Tube ρ E) : Tube ρ E :=
  T.translate ((c⁻¹ - 1) • T.center)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem undilateAtZero_carrier {ρ : NNReal} (c : ℝ) (T : Tube ρ E) :
    (undilateAtZero c T).carrier = ((c⁻¹ - 1) • T.center + ·) '' T.carrier := rfl

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem undilateAtZero_center {ρ : NNReal} (c : ℝ) (T : Tube ρ E) :
    (undilateAtZero c T).center = c⁻¹ • T.center := by
  let v : E := (c⁻¹ - 1) • T.center
  change midpoint ℝ (v + T.x) (v + T.y) = c⁻¹ • T.center
  have hm : v + midpoint ℝ T.x T.y = midpoint ℝ (v + T.x) (v + T.y) := by
    simpa only [vadd_eq_add, midpoint_self] using
      (midpoint_vadd_midpoint (R := ℝ) v v T.x T.y)
  rw [← hm]
  dsimp only [v]
  module

/-- A common inverse presentation enlarges a centred ambient ball by at most a factor of two.

The tube is translated by `(c⁻¹ - 1) T.center`.  For `c ≥ 1` this vector has norm at most the
norm of the original centre, which is itself bounded by `R` whenever the tube lies in `B_R`. -/
theorem undilateAtZero_carrier_subset_closedBall {ρ : NNReal} {c R : ℝ} (hc : 1 ≤ c)
    (T : Tube ρ E) (hball : T.carrier ⊆ Metric.closedBall 0 R) :
    (undilateAtZero c T).carrier ⊆ Metric.closedBall 0 (2 * R) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcinv0 : 0 ≤ c⁻¹ := (inv_pos.mpr hc0).le
  have hcinv1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).2 hc
  have hcenterMem : T.center ∈ T.carrier :=
    T.convex.midpoint_mem (_root_.Tube.x_mem_carrier T) (_root_.Tube.y_mem_carrier T)
  have hcenterBall := hball hcenterMem
  rw [undilateAtZero_carrier]
  rintro z ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hcenterBall ⊢
  have hxBall := hball hx
  rw [Metric.mem_closedBall, dist_zero_right] at hxBall
  have hcoeff : |c⁻¹ - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hcinv1)]
    linarith
  calc
    ‖(c⁻¹ - 1) • T.center + x‖
        ≤ ‖(c⁻¹ - 1) • T.center‖ + ‖x‖ := norm_add_le _ _
    _ = |c⁻¹ - 1| * ‖T.center‖ + ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * R + R := by gcongr
    _ = 2 * R := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Tube dilation commutes with translating the tube and the resulting convex body by the same
vector. -/
theorem dilate_translate {ρ : NNReal} (T : Tube ρ E) (v : E) (c : ℝ) :
    Tube.dilate (T.translate v) c = (Tube.dilate T c).translate v := by
  have hcenter : (T.translate v).center = v + T.center := by
    change midpoint ℝ (v + T.x) (v + T.y) = v + midpoint ℝ T.x T.y
    simpa only [vadd_eq_add, midpoint_self] using
      (midpoint_vadd_midpoint (R := ℝ) v v T.x T.y).symm
  apply ConvexSpaceBody.ext
  change (Tube.dilate (T.translate v) c).carrier =
    ((Tube.dilate T c).translate v).carrier
  rw [Tube.dilate_carrier]
  change AffineMap.homothety (T.translate v).center c '' (T.translate v).carrier =
    (v + ·) '' (Tube.dilate T c).carrier
  rw [Tube.dilate_carrier]
  rw [_root_.Tube.translate_carrier, ← Set.image_add_left, hcenter]
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1
  funext x
  simp only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  change c • ((v + x) - (v + T.center)) + (v + T.center) =
    v + (c • (x - T.center) + T.center)
  module

omit [MeasurableSpace E] [BorelSpace E] in
/-- A common inverse homothety turns a centred tube dilate into `undilateAtZero`. -/
theorem homothety_dilate_eq_undilateAtZero {ρ : NNReal} {c : ℝ} (hc : c ≠ 0)
    (T : Tube ρ E) :
    (Tube.dilate T c).homothety 0 c⁻¹ = (undilateAtZero c T).toConvexSpaceBody := by
  apply ConvexSpaceBody.ext
  rw [ConvexSpaceBody.coe_homothety, Tube.dilate_carrier]
  rw [← Set.image_comp]
  change (AffineMap.homothety 0 c⁻¹ ∘ AffineMap.homothety T.center c) '' T.carrier =
    (((c⁻¹ - 1) • T.center + ·) '' T.carrier)
  congr 1
  funext x
  simp only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    smul_add, smul_sub, inv_smul_smul₀ hc, sub_zero]
  module

omit [MeasurableSpace E] [BorelSpace E] in
/-- Applying the inverse common homothety after an additional centred dilation multiplies the
two dilation ratios. -/
theorem homothety_dilate_undilateAtZero {ρ : NNReal} {c : ℝ} (hc : c ≠ 0)
    (T : Tube ρ E) (D : ℝ) :
    (Tube.dilate (undilateAtZero c T) D).homothety 0 c = Tube.dilate T (c * D) := by
  apply ConvexSpaceBody.ext
  rw [ConvexSpaceBody.coe_homothety, Tube.dilate_carrier]
  change _ = (Tube.dilate T (c * D)).carrier
  rw [Tube.dilate_carrier]
  rw [← Set.image_comp]
  rw [undilateAtZero_carrier, ← Set.image_comp]
  congr 1
  funext x
  rw [undilateAtZero_center]
  simp only [Function.comp_apply, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
    smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul, sub_zero]
  module

/-- A common inverse homothety preserves a dilated parent relation up to a fixed enlargement.

If `U` lies in the `D`-dilate of `V` and `c ≥ 1`, then the honest tubes obtained from the
common `undilateAtZero c` presentation satisfy the same kind of relation at ratio `6 + 4 D`.
The estimate is uniform in both tube scales.  In particular it has no smallness hypothesis such
as `D * ρ ≤ 1`, which is essential when the adapter is used at an arbitrary coarse node scale.

The proof separates displacement from the child centre into its axial and transverse parts.
The child direction differs transversely from the parent direction by at most `2 D ρ`, while
the inverse homothety contracts the displacement between the two centres. -/
theorem undilateAtZero_le_dilate_of_le_dilate {σ ρ : NNReal} (hσρ : σ ≤ ρ) (hρ1 : ρ ≤ 1)
    {c D : ℝ} (hc : 1 ≤ c) (hD : 0 < D) (U : Tube σ E) (V : Tube ρ E)
    (hUV : U.toConvexSpaceBody ≤ Tube.dilate V D) :
    (undilateAtZero c U).toConvexSpaceBody ≤
      Tube.dilate (undilateAtZero c V) (6 + 4 * D) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcinv0 : 0 ≤ c⁻¹ := (inv_pos.mpr hc0).le
  have hcinv1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).2 hc
  have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hρ1R : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  have hσρR : (σ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hσρ
  have hL0 : 0 < 6 + 4 * D := by linarith
  have hUVset : U.carrier ⊆ (Tube.dilate V D).carrier :=
    SetLike.coe_subset_coe.mpr hUV
  have hcenterU : U.center ∈ U.carrier :=
    U.convex.midpoint_mem (_root_.Tube.x_mem_carrier U) (_root_.Tube.y_mem_carrier U)
  have hcenter := _root_.Tube.abs_inner_and_perp_le_of_mem_dilate V hD (hUVset hcenterU)
  have hdir := (_root_.Tube.parameters_mem_of_subset_dilate_free hD V U hUVset).2.2
  let U' : Tube σ E := undilateAtZero c U
  let V' : Tube ρ E := undilateAtZero c V
  have hU'dir : U'.direction = U.direction := by
    change ((U.translate ((c⁻¹ - 1) • U.center)).y -
      (U.translate ((c⁻¹ - 1) • U.center)).x) = U.y - U.x
    simp only [_root_.Tube.translate_y, _root_.Tube.translate_x]
    abel
  have hV'dir : V'.direction = V.direction := by
    change ((V.translate ((c⁻¹ - 1) • V.center)).y -
      (V.translate ((c⁻¹ - 1) • V.center)).x) = V.y - V.x
    simp only [_root_.Tube.translate_y, _root_.Tube.translate_x]
    abel
  have hcentres : U'.center - V'.center = c⁻¹ • (U.center - V.center) := by
    rw [show U'.center = c⁻¹ • U.center by exact undilateAtZero_center c U]
    rw [show V'.center = c⁻¹ • V.center by exact undilateAtZero_center c V]
    module
  have hcenterAx : |inner ℝ V'.direction (U'.center - V'.center)| ≤
      D / 2 + D * (ρ : ℝ) := by
    rw [hcentres, hV'dir, inner_smul_right, abs_mul, abs_of_nonneg hcinv0]
    calc
      c⁻¹ * |inner ℝ V.direction (U.center - V.center)|
          ≤ 1 * |inner ℝ V.direction (U.center - V.center)| := by gcongr
      _ ≤ D / 2 + D * (ρ : ℝ) := by simpa [real_inner_comm] using hcenter.1
  have hcenterPerp :
      ‖(U'.center - V'.center) -
          inner ℝ V'.direction (U'.center - V'.center) • V'.direction‖
        ≤ D * (ρ : ℝ) := by
    rw [hcentres, hV'dir, inner_smul_right]
    have heq :
        c⁻¹ • (U.center - V.center) -
            (c⁻¹ * inner ℝ V.direction (U.center - V.center)) • V.direction =
          c⁻¹ • ((U.center - V.center) -
            inner ℝ V.direction (U.center - V.center) • V.direction) := by module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcinv0]
    calc
      c⁻¹ * ‖(U.center - V.center) -
            inner ℝ V.direction (U.center - V.center) • V.direction‖
          ≤ 1 * ‖(U.center - V.center) -
            inner ℝ V.direction (U.center - V.center) • V.direction‖ := by gcongr
      _ ≤ D * (ρ : ℝ) := by simpa using hcenter.2
  intro z hz
  have hz1 : z ∈ (Tube.dilate U' 1).carrier := Tube.subset_dilate U' le_rfl hz
  have hlocal := _root_.Tube.abs_inner_and_perp_le_of_mem_dilate U' one_pos hz1
  let s : ℝ := inner ℝ U'.direction (z - U'.center)
  let g : E := z - U'.center - s • U'.direction
  have hs : |s| ≤ 1 / 2 + (σ : ℝ) := by
    simpa [s, real_inner_comm] using hlocal.1
  have hg : ‖g‖ ≤ (σ : ℝ) := by simpa [g, s] using hlocal.2
  have hdecomp : z - U'.center = s • U'.direction + g := by
    dsimp only [g]
    abel
  have hdir' :
      ‖U'.direction - inner ℝ V'.direction U'.direction • V'.direction‖
        ≤ 2 * D * (ρ : ℝ) := by simpa [hU'dir, hV'dir] using hdir
  have hlocalNorm : ‖z - U'.center‖ ≤ 1 / 2 + 2 * (ρ : ℝ) := by
    rw [hdecomp]
    calc
      ‖s • U'.direction + g‖ ≤ ‖s • U'.direction‖ + ‖g‖ := norm_add_le _ _
      _ = |s| + ‖g‖ := by rw [norm_smul, Real.norm_eq_abs, hU'dir, U.norm_direction, mul_one]
      _ ≤ (1 / 2 + (σ : ℝ)) + (σ : ℝ) := add_le_add hs hg
      _ ≤ 1 / 2 + 2 * (ρ : ℝ) := by linarith
  have hlocalPerp :
      ‖(z - U'.center) -
          inner ℝ V'.direction (z - U'.center) • V'.direction‖
        ≤ (1 + 3 * D) * (ρ : ℝ) := by
    rw [hdecomp, inner_add_right, inner_smul_right]
    have heq :
        s • U'.direction + g -
            (s * inner ℝ V'.direction U'.direction + inner ℝ V'.direction g) •
              V'.direction =
          s • (U'.direction -
              inner ℝ V'.direction U'.direction • V'.direction) +
            (g - inner ℝ V'.direction g • V'.direction) := by module
    rw [heq]
    calc
      ‖s • (U'.direction -
              inner ℝ V'.direction U'.direction • V'.direction) +
            (g - inner ℝ V'.direction g • V'.direction)‖
          ≤ ‖s • (U'.direction -
              inner ℝ V'.direction U'.direction • V'.direction)‖ +
            ‖g - inner ℝ V'.direction g • V'.direction‖ := norm_add_le _ _
      _ ≤ |s| * (2 * D * (ρ : ℝ)) + ‖g‖ := by
        gcongr
        · simpa [norm_smul, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left hdir' (abs_nonneg s)
        · exact norm_sub_inner_smul_le_local (by simpa [hV'dir] using V.norm_direction) g
      _ ≤ (1 / 2 + (σ : ℝ)) * (2 * D * (ρ : ℝ)) + (σ : ℝ) := by gcongr
      _ ≤ (1 / 2 + (ρ : ℝ)) * (2 * D * (ρ : ℝ)) + (ρ : ℝ) := by
        gcongr
      _ ≤ (1 + 3 * D) * (ρ : ℝ) := by
        have hρsq : (ρ : ℝ) * (ρ : ℝ) ≤ (ρ : ℝ) := by nlinarith
        nlinarith
  let t : ℝ := inner ℝ V'.direction (z - V'.center)
  have hax : |t| ≤ (6 + 4 * D) / 2 := by
    have hsum : z - V'.center = (z - U'.center) + (U'.center - V'.center) := by abel
    dsimp only [t]
    rw [hsum, inner_add_right]
    calc
      |inner ℝ V'.direction (z - U'.center) +
          inner ℝ V'.direction (U'.center - V'.center)|
          ≤ |inner ℝ V'.direction (z - U'.center)| +
            |inner ℝ V'.direction (U'.center - V'.center)| := abs_add_le _ _
      _ ≤ ‖z - U'.center‖ + (D / 2 + D * (ρ : ℝ)) := by
        gcongr
        calc
          |inner ℝ V'.direction (z - U'.center)|
              ≤ ‖V'.direction‖ * ‖z - U'.center‖ :=
                abs_real_inner_le_norm V'.direction (z - U'.center)
          _ = ‖z - U'.center‖ := by rw [hV'dir, V.norm_direction, one_mul]
      _ ≤ (1 / 2 + 2 * (ρ : ℝ)) + (D / 2 + D * (ρ : ℝ)) := by gcongr
      _ ≤ (6 + 4 * D) / 2 := by nlinarith
  have hperp : dist z (V'.center + t • V'.direction) ≤
      (6 + 4 * D) * (ρ : ℝ) := by
    rw [dist_eq_norm, sub_add_eq_sub_sub]
    have hsum : z - V'.center = (z - U'.center) + (U'.center - V'.center) := by abel
    dsimp only [t]
    rw [hsum, inner_add_right]
    have heq :
        (z - U'.center) + (U'.center - V'.center) -
            (inner ℝ V'.direction (z - U'.center) +
              inner ℝ V'.direction (U'.center - V'.center)) • V'.direction =
          ((z - U'.center) -
              inner ℝ V'.direction (z - U'.center) • V'.direction) +
            ((U'.center - V'.center) -
              inner ℝ V'.direction (U'.center - V'.center) • V'.direction) := by module
    rw [heq]
    calc
      ‖((z - U'.center) -
              inner ℝ V'.direction (z - U'.center) • V'.direction) +
            ((U'.center - V'.center) -
              inner ℝ V'.direction (U'.center - V'.center) • V'.direction)‖
          ≤ ‖(z - U'.center) -
              inner ℝ V'.direction (z - U'.center) • V'.direction‖ +
            ‖(U'.center - V'.center) -
              inner ℝ V'.direction (U'.center - V'.center) • V'.direction‖ :=
                norm_add_le _ _
      _ ≤ (1 + 3 * D) * (ρ : ℝ) + D * (ρ : ℝ) := add_le_add hlocalPerp hcenterPerp
      _ ≤ (6 + 4 * D) * (ρ : ℝ) := by nlinarith
  exact mem_dilate_of_dist_axis_le V' hL0 hax hperp

omit [MeasurableSpace E] [BorelSpace E] in
/-- The `1`-dilate of a tube, as a convex body. -/
theorem dilate_one_body {ρ : NNReal} (T : Tube ρ E) :
    Tube.dilate T (1 : ℝ) = T.toConvexSpaceBody := by
  apply ConvexSpaceBody.ext
  change (Tube.dilate T (1 : ℝ)).carrier = T.carrier
  rw [Tube.dilate_carrier]
  simp

/-- Enlarging every member of a tube family by the same centred dilation increases maximal
density by at most the corresponding volume factor.

This comparison is deliberately one-sided.  Although the dilations have different centres,
every original tube is contained in its own dilate; hence every dilated tube counted inside a
test body contributes an original tube counted inside the same test body. -/
theorem maxDensity_dilate_le {ρ : NNReal} {ι : Type v} (s : Finset ι) (T : ι → Tube ρ E)
    {c : ℝ} (hc : 1 < c) :
    maxDensity s (fun i => Tube.dilate (T i) c) ≤
      ENNReal.ofReal (c ^ Module.finrank ℝ E) *
        maxDensity s (fun i => (T i).toConvexSpaceBody) := by
  classical
  let A : ENNReal := ENNReal.ofReal (c ^ Module.finrank ℝ E)
  rw [maxDensity_le_iff]
  intro K
  rw [densityIn_le_iff]
  let sd : Finset ι := s.filter fun i => Tube.dilate (T i) c ≤ K
  let st : Finset ι := s.filter fun i => (T i).toConvexSpaceBody ≤ K
  have hsub : sd ⊆ st := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi'.1,
      (Tube.subset_dilate (T i) hc.le).trans hi'.2⟩
  have hvol : ∀ i, volume (Tube.dilate (T i) c).carrier =
      A * volume (T i).carrier := by
    intro i
    simpa only [A, Tube.tubeDilateVolume.C'] using Tube.tubeDilateVolume (T i) hc
  calc
    ∑ i ∈ s with Tube.dilate (T i) c ≤ K, volume (Tube.dilate (T i) c).carrier =
        ∑ i ∈ sd, volume (Tube.dilate (T i) c).carrier := by rfl
    _ = A * ∑ i ∈ sd, volume (T i).carrier := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hvol i
    _ ≤ A * ∑ i ∈ st, volume (T i).carrier := by
      gcongr
    _ = A * ∑ i ∈ s with (T i).toConvexSpaceBody ≤ K, volume (T i).carrier := by rfl
    _ ≤ A * (maxDensity s (fun i => (T i).toConvexSpaceBody) * volume K.carrier) := by
      gcongr
      exact sum_volume_le_maxDensity_mul_volume s
        (fun i => (T i).toConvexSpaceBody) K
    _ = (A * maxDensity s (fun i => (T i).toConvexSpaceBody)) * volume K.carrier := by ring

/-- A common centred dilation preserves relative Frostman control, apart from changing the
ambient body.

Although the individual dilations have different centres, `maxDensity_dilate_le` costs exactly
the common volume factor `c ^ dim E`.  The reference density in the new ambient gains the same
factor, so it cancels.  The only remaining loss is the honest ambient-volume ratio
`|L| / |K|`. -/
theorem frostmanConstIn_dilate_le {ρ : NNReal} {ι : Type v} (s : Finset ι)
    (T : ι → Tube ρ E) {K L : ConvexSpaceBody E} {c : ℝ} (hc : 1 < c)
    (hTK : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K)
    (hTL : ∀ i ∈ s, Tube.dilate (T i) c ≤ L)
    (hK0 : volume K.carrier ≠ 0) (hL0 : volume L.carrier ≠ 0) :
    frostmanConstIn s (fun i ↦ Tube.dilate (T i) c) L ≤
      volume L.carrier / volume K.carrier *
        frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody) K := by
  classical
  let A : ENNReal := ENNReal.ofReal (c ^ Module.finrank ℝ E)
  let C : ENNReal := frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody) K
  let R : ENNReal := volume L.carrier / volume K.carrier
  have hTorigL : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ L := by
    intro i hi
    exact (Tube.subset_dilate (T i) hc.le).trans (hTL i hi)
  have hFrK : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) K C :=
    isFrostmanIn_frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody) K
  have hFrL : IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody) L (C * R) := by
    simpa only [C, R] using hFrK.change_ambient hTK hTorigL hK0 hL0
  have hvolume : ∀ i, volume (Tube.dilate (T i) c).carrier =
      A * volume (T i).carrier := by
    intro i
    simpa only [A, Tube.tubeDilateVolume.C'] using Tube.tubeDilateVolume (T i) hc
  have hdensity : densityIn s (fun i ↦ Tube.dilate (T i) c) L =
      A * densityIn s (fun i ↦ (T i).toConvexSpaceBody) L := by
    rw [densityIn_of_all_le hTL, densityIn_of_all_le hTorigL]
    calc
      (∑ i ∈ s, volume (Tube.dilate (T i) c).carrier) / volume L.carrier =
          (∑ i ∈ s, A * volume (T i).carrier) / volume L.carrier := by
            apply congrArg (fun x : ENNReal ↦ x / volume L.carrier)
            apply Finset.sum_congr rfl
            intro i _
            exact hvolume i
      _ = (A * ∑ i ∈ s, volume (T i).carrier) / volume L.carrier := by
        rw [Finset.mul_sum]
      _ = A * ((∑ i ∈ s, volume (T i).carrier) / volume L.carrier) := by
        rw [mul_div_assoc]
  apply frostmanConstIn_le
  apply IsFrostmanIn.of_maxDensity_le
  calc
    maxDensity s (fun i ↦ Tube.dilate (T i) c) ≤
        A * maxDensity s (fun i ↦ (T i).toConvexSpaceBody) :=
      maxDensity_dilate_le s T hc
    _ ≤ A * ((C * R) * densityIn s (fun i ↦ (T i).toConvexSpaceBody) L) := by
      gcongr
      exact hFrL.maxDensity_le_of_carrier_subset hTorigL
    _ = (R * C) * densityIn s (fun i ↦ Tube.dilate (T i) c) L := by
      rw [hdensity]
      ring

/-- Present a uniformly dilated tube family as honest tubes by the common inverse homothety.

This is the Frostman counterpart of `homothety_dilate_eq_undilateAtZero`.  It packages the
centred-dilation comparison above with the exact common presentation used by the product-only
factorizations. -/
theorem frostmanConstIn_undilateAtZero_le {ρ : NNReal} {ι : Type v} (s : Finset ι)
    (T : ι → Tube ρ E) {K L : ConvexSpaceBody E} {c : ℝ} (hc : 1 < c)
    (hTK : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K)
    (hTL : ∀ i ∈ s, Tube.dilate (T i) c ≤ L)
    (hK0 : volume K.carrier ≠ 0) (hL0 : volume L.carrier ≠ 0) :
    frostmanConstIn s (fun i ↦ (undilateAtZero c (T i)).toConvexSpaceBody)
        (L.homothety 0 c⁻¹) ≤
      volume L.carrier / volume K.carrier *
        frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody) K := by
  have hc0 : c ≠ 0 := ne_of_gt (zero_lt_one.trans hc)
  have hbody : (fun i ↦ (undilateAtZero c (T i)).toConvexSpaceBody) =
      (fun i ↦ (Tube.dilate (T i) c).homothety 0 c⁻¹) := by
    funext i
    exact (homothety_dilate_eq_undilateAtZero hc0 (T i)).symm
  rw [hbody]
  rw [frostmanConstIn_homothety s (fun i ↦ Tube.dilate (T i) c) L 0
    (inv_ne_zero hc0)]
  exact frostmanConstIn_dilate_le s T hc hTK hTL hK0 hL0

namespace undilateAtZeroConflict

/-- Constant controlling the ED conflict degree after presenting `c`-dilated tubes honestly. -/
noncomputable def C (n : ℕ) (c : ℝ) : NNReal :=
  Tube.essDistinctTubesInSelfDilate.C n
    (c * Tube.tubeOverlapCoreClose.C n)

/-- Integer version of `undilateAtZeroConflict.C`, used by `IsEDUpToMult`. -/
noncomputable def M (n : ℕ) (c : ℝ) : ℕ := Nat.ceil (C n c : ℝ)

/-- Total weighted-extraction loss, including the selected colour itself. -/
noncomputable def D (n : ℕ) (c : ℝ) : NNReal := M n c + 1

/-- The weighted-extraction loss is at least one. -/
theorem one_le_D (n : ℕ) (c : ℝ) : 1 ≤ D n c := by
  dsimp [D]
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le (M n c))

end undilateAtZeroConflict

/-- A pairwise-ED tube family remains ED up to an absolute multiplicity after the common
undilation presentation.  The loss depends only on the ambient dimension and on the fixed
dilation ratio. -/
theorem isEDUpToMult_undilateAtZero [Nontrivial E]
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {ι : Type v} (s : Finset ι) (T : ι → Tube ρ E) {c : ℝ} (hc : 1 ≤ c)
    (hED : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    IsEDUpToMult s (fun i => (undilateAtZero c (T i)).carrier)
      (undilateAtZeroConflict.M (Module.finrank ℝ E) c) := by
  classical
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcne : c ≠ 0 := hc0.ne'
  let Cn : ℝ := Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  have hCn1 : 1 ≤ Cn := (Tube.tubeOverlapCoreClose.one_lt_C _).le
  have hcCn : 1 ≤ c * Cn := by nlinarith
  unfold IsEDUpToMult
  intro i hi
  let bad := notEssDistinctSet s (fun j => (undilateAtZero c (T j)).carrier)
    (undilateAtZero c (T i)).carrier
  have hbadED : (bad : Set ι).Pairwise fun j k =>
      IsEssentiallyDistinct (T j).carrier (T k).carrier := by
    intro j hj k hk hjk
    exact hED (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hk).1 hjk
  have hbadSub : ∀ j ∈ bad, (T j).carrier ⊆
      (Tube.dilate (T i) (c * Cn)).carrier := by
    intro j hj
    have hnot : ¬ IsEssentiallyDistinct
        (undilateAtZero c (T i)).carrier (undilateAtZero c (T j)).carrier := by
      have hji := (Finset.mem_filter.mp hj).2
      exact fun hij => hji (isEssentiallyDistinct_symm hij)
    have hUsub : (undilateAtZero c (T j)).carrier ⊆
        (Tube.dilate (undilateAtZero c (T i)) Cn).carrier := by
      apply Tube.tubeOverlapCoreClose hρ0 hρ1
      have hvol : volume (undilateAtZero c (T j)).carrier =
          volume (undilateAtZero c (T i)).carrier :=
        Tube.volume_carrier_eq_volume_carrier _ _
      rw [IsEssentiallyDistinct, hvol, max_self] at hnot
      exact lt_of_not_ge hnot
    have hhom :
        ((undilateAtZero c (T j)).toConvexSpaceBody).homothety 0 c ≤
          (Tube.dilate (undilateAtZero c (T i)) Cn).homothety 0 c :=
      (ConvexSpaceBody.homothety_le_homothety_iff 0 hcne).2 hUsub
    have hleft : ((undilateAtZero c (T j)).toConvexSpaceBody).homothety 0 c =
        Tube.dilate (T j) c := by
      calc
        ((undilateAtZero c (T j)).toConvexSpaceBody).homothety 0 c =
            (Tube.dilate (undilateAtZero c (T j)) 1).homothety 0 c := by
              rw [dilate_one_body]
        _ = Tube.dilate (T j) (c * 1) :=
          homothety_dilate_undilateAtZero hcne (T j) 1
        _ = Tube.dilate (T j) c := by rw [mul_one]
    have hright : (Tube.dilate (undilateAtZero c (T i)) Cn).homothety 0 c =
        Tube.dilate (T i) (c * Cn) :=
      homothety_dilate_undilateAtZero hcne (T i) Cn
    have hdil : Tube.dilate (T j) c ≤ Tube.dilate (T i) (c * Cn) := by
      rwa [hleft, hright] at hhom
    exact (Tube.subset_dilate (T j) hc).trans hdil
  have hpack := Tube.essDistinctTubesInSelfDilate hcCn hρ0 hρ1 (T i) bad T hbadED hbadSub
  have hpackR : (bad.card : ℝ) ≤ (undilateAtZeroConflict.C
      (Module.finrank ℝ E) c : ℝ) := by
    exact_mod_cast hpack
  change bad.card ≤ undilateAtZeroConflict.M (Module.finrank ℝ E) c
  exact_mod_cast hpackR.trans (Nat.le_ceil _)

end Tube

end Kakeya

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace ShadedBody

/-- Re-present a shaded body whose carrier is an honest tube as a `ShadedTube`. -/
def toShadedTubeOfCarrier {ρ : NNReal} (S : ShadedBody E) (T : Tube ρ E)
    (h : S.toConvexSpaceBody = T.toConvexSpaceBody) : ShadedTube ρ E where
  toTube := T
  shade := S.shade
  measurableSet_shade := S.measurableSet_shade
  shade_subset := by
    rw [← h]
    exact S.shade_subset

omit [BorelSpace E] in
@[simp]
theorem toShadedTubeOfCarrier_toTube {ρ : NNReal} (S : ShadedBody E) (T : Tube ρ E)
    (h : S.toConvexSpaceBody = T.toConvexSpaceBody) :
    (S.toShadedTubeOfCarrier T h).toTube = T := rfl

omit [BorelSpace E] in
@[simp]
theorem toShadedTubeOfCarrier_shade {ρ : NNReal} (S : ShadedBody E) (T : Tube ρ E)
    (h : S.toConvexSpaceBody = T.toConvexSpaceBody) :
    (S.toShadedTubeOfCarrier T h).shade = S.shade := rfl

/-- An empty shading on a prescribed honest tube. -/
def emptyShadedTube {ρ : NNReal} (T : Tube ρ E) : ShadedTube ρ E where
  toTube := T
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

omit [BorelSpace E] in
@[simp]
theorem emptyShadedTube_toTube {ρ : NNReal} (T : Tube ρ E) :
    (emptyShadedTube T).toTube = T := rfl

omit [BorelSpace E] in
@[simp]
theorem emptyShadedTube_shade {ρ : NNReal} (T : Tube ρ E) :
    (emptyShadedTube T).shade = ∅ := rfl

/-- Re-present a family on honest tube carriers over the selected support, with empty shading
off that support. -/
noncomputable def toShadedTubeOfCarrierOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = (T i).toConvexSpaceBody) :
    ι → ShadedTube ρ E := by
  classical
  exact fun i => if hi : i ∈ s then (S i).toShadedTubeOfCarrier (T i) (h i hi)
    else emptyShadedTube (T i)

omit [BorelSpace E] in
@[simp]
theorem toShadedTubeOfCarrierOn_toTube {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = (T i).toConvexSpaceBody) (i : ι) :
    (toShadedTubeOfCarrierOn s S T h i).toTube = T i := by
  classical
  simp only [toShadedTubeOfCarrierOn]
  split <;> rfl

omit [BorelSpace E] in
@[simp]
theorem toShadedTubeOfCarrierOn_shade_of_mem {ρ : NNReal} {ι : Type v}
    {s : Finset ι} (S : ι → ShadedBody E) (T : ι → Tube ρ E)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = (T i).toConvexSpaceBody)
    {i : ι} (hi : i ∈ s) :
    (toShadedTubeOfCarrierOn s S T h i).shade = (S i).shade := by
  classical
  simp only [toShadedTubeOfCarrierOn, dif_pos hi, toShadedTubeOfCarrier_shade]

/-- Re-presenting selected shaded bodies on their honest tube carriers preserves multiplicity. -/
theorem multiplicity_toShadedTubeOfCarrierOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = (T i).toConvexSpaceBody) :
    multiplicity s (fun i ↦ (toShadedTubeOfCarrierOn s S T h i).toShadedBody) =
      multiplicity s S := by
  apply _root_.Tube.multiplicity_congr_of_shading_eq
  intro i hi
  exact toShadedTubeOfCarrierOn_shade_of_mem S T h hi

/-- Re-presenting selected shaded bodies on their honest tube carriers preserves fullness. -/
theorem fullness_toShadedTubeOfCarrierOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = (T i).toConvexSpaceBody) :
    fullness s (fun i ↦ (toShadedTubeOfCarrierOn s S T h i).toShadedBody) = fullness s S := by
  change (fullness' s (fun i ↦ (toShadedTubeOfCarrierOn s S T h i).toShadedBody)).toNNReal =
    (fullness' s S).toNNReal
  congr 1
  unfold fullness'
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    change volume (toShadedTubeOfCarrierOn s S T h i).shade = volume (S i).shade
    rw [toShadedTubeOfCarrierOn_shade_of_mem S T h hi]
  · apply Finset.sum_congr rfl
    intro i hi
    change volume (toShadedTubeOfCarrierOn s S T h i).carrier = volume (S i).carrier
    rw [show (toShadedTubeOfCarrierOn s S T h i).carrier = (T i).carrier by
      exact congrArg (fun U : Tube ρ E ↦ U.carrier)
        (toShadedTubeOfCarrierOn_toTube s S T h i)]
    exact (congrArg (fun B : ConvexSpaceBody E ↦ volume B.carrier) (h i hi)).symm

/-- The honest shaded tube presentation of a body carried by `c · T`. -/
def undilateTubePresentation {ρ : NNReal} {c : ℝ} (hc : c ≠ 0)
    (S : ShadedBody E) (T : Tube ρ E) (h : S.toConvexSpaceBody = Kakeya.Tube.dilate T c) :
    ShadedTube ρ E :=
  let S' := S.homothety 0 (inv_ne_zero hc)
  S'.toShadedTubeOfCarrier (Kakeya.Tube.undilateAtZero c T) <| by
    rw [homothety_toConvexSpaceBody, h]
    exact Kakeya.Tube.homothety_dilate_eq_undilateAtZero hc T

@[simp]
theorem undilateTubePresentation_toTube {ρ : NNReal} {c : ℝ} (hc : c ≠ 0)
    (S : ShadedBody E) (T : Tube ρ E) (h : S.toConvexSpaceBody = Kakeya.Tube.dilate T c) :
    (S.undilateTubePresentation hc T h).toTube = Kakeya.Tube.undilateAtZero c T := rfl

@[simp]
theorem undilateTubePresentation_shade {ρ : NNReal} {c : ℝ} (hc : c ≠ 0)
    (S : ShadedBody E) (T : Tube ρ E) (h : S.toConvexSpaceBody = Kakeya.Tube.dilate T c) :
    (S.undilateTubePresentation hc T h).shade =
      (S.homothety 0 (inv_ne_zero hc)).shade := rfl

@[simp]
theorem undilateTubePresentation_toConvexSpaceBody {ρ : NNReal} {c : ℝ} (hc : c ≠ 0)
    (S : ShadedBody E) (T : Tube ρ E) (h : S.toConvexSpaceBody = Kakeya.Tube.dilate T c) :
    (S.undilateTubePresentation hc T h).toConvexSpaceBody =
      (S.homothety 0 (inv_ne_zero hc)).toConvexSpaceBody := by
  rw [undilateTubePresentation_toTube]
  rw [homothety_toConvexSpaceBody, h]
  exact (Kakeya.Tube.homothety_dilate_eq_undilateAtZero hc T).symm

/-- Present a family of dilated-tube bodies honestly over a selected support, with empty shading
off that support. -/
noncomputable def undilateTubePresentationOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c) :
    ι → ShadedTube ρ E := by
  classical
  exact fun i => if hi : i ∈ s then (S i).undilateTubePresentation hc (T i) (h i hi)
    else emptyShadedTube (Kakeya.Tube.undilateAtZero c (T i))

@[simp]
theorem undilateTubePresentationOn_toTube {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c) (i : ι) :
    (undilateTubePresentationOn s S T hc h i).toTube =
      Kakeya.Tube.undilateAtZero c (T i) := by
  classical
  simp only [undilateTubePresentationOn]
  split <;> rfl

@[simp]
theorem undilateTubePresentationOn_carrier {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c) (i : ι) :
    (undilateTubePresentationOn s S T hc h i).carrier =
      (Kakeya.Tube.undilateAtZero c (T i)).carrier := by
  exact congrArg (fun U : Tube ρ E => U.carrier)
    (undilateTubePresentationOn_toTube s S T hc h i)

@[simp]
theorem undilateTubePresentationOn_shade_of_mem {ρ : NNReal} {ι : Type v}
    {s : Finset ι} (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c)
    {i : ι} (hi : i ∈ s) :
    (undilateTubePresentationOn s S T hc h i).shade =
      ((S i).homothety 0 (inv_ne_zero hc)).shade := by
  classical
  simp only [undilateTubePresentationOn, dif_pos hi, undilateTubePresentation_shade]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Two shaded bodies agree when both their convex carriers and shades agree. -/
theorem eq_of_toConvexSpaceBody_eq_of_shade_eq {A B : ShadedBody E}
    (hbody : A.toConvexSpaceBody = B.toConvexSpaceBody) (hshade : A.shade = B.shade) :
    A = B := by
  cases A
  cases B
  simp_all

/-- On the selected support, the honest presentation is exactly the common inverse homothety
of the body-valued factor. -/
theorem undilateTubePresentationOn_toShadedBody_of_mem {ρ : NNReal} {ι : Type v}
    {s : Finset ι} (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c)
    {i : ι} (hi : i ∈ s) :
    (undilateTubePresentationOn s S T hc h i).toShadedBody =
      (S i).homothety 0 (inv_ne_zero hc) := by
  apply eq_of_toConvexSpaceBody_eq_of_shade_eq
  · classical
    simp only [undilateTubePresentationOn, dif_pos hi]
    exact undilateTubePresentation_toConvexSpaceBody hc (S i) (T i) (h i hi)
  · exact undilateTubePresentationOn_shade_of_mem S T hc h hi

/-- The honest presentation preserves the selected factor's multiplicity. -/
theorem multiplicity_undilateTubePresentationOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c) :
    multiplicity s (fun i => (undilateTubePresentationOn s S T hc h i).toShadedBody) =
      multiplicity s S := by
  calc
    multiplicity s (fun i => (undilateTubePresentationOn s S T hc h i).toShadedBody) =
        multiplicity s (fun i => (S i).homothety 0 (inv_ne_zero hc)) := by
      apply _root_.Tube.multiplicity_congr_of_shading_eq
      intro i hi
      exact congrArg ShadedBody.shade
        (undilateTubePresentationOn_toShadedBody_of_mem S T hc h hi)
    _ = multiplicity s S := multiplicity_homothety s S 0 (inv_ne_zero hc)

/-- The honest presentation preserves the selected factor's average fullness. -/
theorem fullness_undilateTubePresentationOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c) :
    fullness s (fun i => (undilateTubePresentationOn s S T hc h i).toShadedBody) =
      fullness s S := by
  calc
    fullness s (fun i => (undilateTubePresentationOn s S T hc h i).toShadedBody) =
        fullness s (fun i => (S i).homothety 0 (inv_ne_zero hc)) := by
      change (fullness' s (fun i =>
        (undilateTubePresentationOn s S T hc h i).toShadedBody)).toNNReal =
          (fullness' s (fun i => (S i).homothety 0 (inv_ne_zero hc))).toNNReal
      congr 1
      unfold fullness'
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simpa only using congrArg (fun B : ShadedBody E => volume B.shade)
          (undilateTubePresentationOn_toShadedBody_of_mem S T hc h hi)
      · apply Finset.sum_congr rfl
        intro i hi
        simpa only using congrArg (fun B : ShadedBody E => volume B.carrier)
          (undilateTubePresentationOn_toShadedBody_of_mem S T hc h hi)
    _ = fullness s S := fullness_homothety s S 0 (inv_ne_zero hc)

/-- The honest presentation preserves maximal density under its common inverse homothety. -/
theorem maxDensity_undilateTubePresentationOn {ρ : NNReal} {ι : Type v}
    (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c) :
    Kakeya.maxDensity s (fun i ↦
      (undilateTubePresentationOn s S T hc h i).toConvexSpaceBody) =
      Kakeya.maxDensity s (fun i ↦ (S i).toConvexSpaceBody) := by
  calc
    Kakeya.maxDensity s (fun i ↦
        (undilateTubePresentationOn s S T hc h i).toConvexSpaceBody) =
        Kakeya.maxDensity s (fun i ↦ ((S i).toConvexSpaceBody).homothety 0 c⁻¹) := by
      apply Kakeya.maxDensity_congr
      intro i hi
      simpa only [homothety_toConvexSpaceBody] using congrArg ShadedBody.toConvexSpaceBody
        (undilateTubePresentationOn_toShadedBody_of_mem S T hc h hi)
    _ = Kakeya.maxDensity s (fun i ↦ (S i).toConvexSpaceBody) :=
      Kakeya.maxDensity_homothety s (fun i ↦ (S i).toConvexSpaceBody) 0 (inv_ne_zero hc)

/-- Weighted ED extraction after presenting a selected dilated-tube factor honestly.

The same subfamily simultaneously retains shade mass and cardinality up to the explicit
`undilateAtZeroConflict.M + 1` loss. -/
theorem exists_pairwise_undilateTubePresentation_weighted [Nontrivial E]
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {ι : Type v} (s : Finset ι) (S : ι → ShadedBody E) (T : ι → Tube ρ E)
    {c : ℝ} (hc : 1 ≤ c)
    (hcarrier : ∀ i ∈ s, (S i).toConvexSpaceBody = Kakeya.Tube.dilate (T i) c)
    (hED : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    let P := undilateTubePresentationOn s S T
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hc)) hcarrier
    let M := Kakeya.Tube.undilateAtZeroConflict.M (Module.finrank ℝ E) c
    ∃ s' ⊆ s,
      ((s' : Set ι).Pairwise fun i j =>
        IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      (∑ i ∈ s, volume (P i).shade) ≤
        ((M : ENNReal) + 1) * ∑ i ∈ s', volume (P i).shade ∧
      s.card ≤ (M + 1) * s'.card := by
  classical
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let P := undilateTubePresentationOn s S T hc0.ne' hcarrier
  let M := Kakeya.Tube.undilateAtZeroConflict.M (Module.finrank ℝ E) c
  have hUpTo : Kakeya.IsEDUpToMult s (fun i => (P i).carrier) M := by
    have hbase := Kakeya.Tube.isEDUpToMult_undilateAtZero hρ0 hρ1 s T hc hED
    rw [Kakeya.IsEDUpToMult] at hbase ⊢
    intro i hi
    have hset : Kakeya.notEssDistinctSet s (fun j => (P j).carrier) (P i).carrier =
        Kakeya.notEssDistinctSet s (fun j =>
          (Kakeya.Tube.undilateAtZero c (T j)).carrier)
            (Kakeya.Tube.undilateAtZero c (T i)).carrier := by
      ext j
      simp only [Kakeya.notEssDistinctSet, Finset.mem_filter]
      rw [show (P i).carrier = (Kakeya.Tube.undilateAtZero c (T i)).carrier by
        simp only [P, undilateTubePresentationOn_carrier]]
      rw [show (P j).carrier = (Kakeya.Tube.undilateAtZero c (T j)).carrier by
        simp only [P, undilateTubePresentationOn_carrier]]
    rw [hset]
    exact hbase i hi
  have hfin : ∀ i ∈ s, volume (P i).shade ≠ ⊤ := by
    intro i _
    exact ne_top_of_le_ne_top (P i).isCompact'.measure_ne_top
      (measure_mono (P i).shade_subset)
  simpa only [P, M] using
    (hUpTo.exists_pairwise_subset_with_measure_and_card
      (fun i => volume (P i).shade) hfin)

end ShadedBody

end

end

#print axioms Kakeya.Tube.homothety_dilate_eq_undilateAtZero
#print axioms Kakeya.Tube.undilateAtZero_le_dilate_of_le_dilate
#print axioms Kakeya.Tube.frostmanConstIn_undilateAtZero_le
#print axioms ShadedBody.multiplicity_undilateTubePresentationOn
#print axioms ShadedBody.fullness_undilateTubePresentationOn
#print axioms ShadedBody.maxDensity_undilateTubePresentationOn

@[expose] public section

namespace Kakeya.ml1CoarseHonestW45

open MeasureTheory Convexity ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

noncomputable section

universe u v w

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The active fine fibre over a retained parent.  This local definition keeps the producer
independent of the historical `BodyProductOnly` module. -/
def activeFibre {ι : Type v} {κ : Type w} [DecidableEq κ]
    (s : Finset ι) (parent : ι → κ) (j : κ) : Finset ι :=
  s.filter fun i ↦ parent i = j

/-- The product-only output obtained by honestly presenting the body-valued coarse factor.

The output keeps the raw factor's index sets and parent map.  Its fine shades are merely
re-presented on their original honest tubes, while every coarse shade is moved by the same
inverse homothety and is therefore carried by `undilateAtZero c Tρ`.  Consequently the product,
coarse fullness, and coarse maximal density are all transported without a pigeonhole loss. -/
structure HonestDilateProductOutput
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    (F : ShadedBody.FactorFamily E ι κ) (T : ι → ShadedTube δ E)
    (Tρ : κ → Tube ρ E)
    (fineSet : Finset ι) (coarseSet : Finset κ)
    (fineShade : ι → ShadedTube δ E) (coarseShade : κ → ShadedTube ρ E)
    (parent : ι → κ) (productConstant : NNReal) : Prop where
  fine_subset : fineSet ⊆ F.innerSet
  coarse_subset : coarseSet ⊆ F.outerSet
  coarse_nonempty : coarseSet.Nonempty
  parent_eq : parent = F.parent
  parent_mem : ∀ i ∈ fineSet, parent i ∈ coarseSet
  fine_eq_filter : fineSet = F.innerSet.filter fun i ↦ parent i ∈ coarseSet
  fine_tube : ∀ i, (fineShade i).toTube = (T i).toTube
  fine_refinement : IsCRefinement fineSet (fun i ↦ (fineShade i).toShadedBody)
    F.innerSet F.innerBody productConstant⁻¹
  coarse_tube : ∀ j, (coarseShade j).toTube =
    Tube.undilateAtZero (c : ℝ) (Tρ j)
  product : ∀ j ∈ coarseSet,
    multiplicity F.innerSet F.innerBody ≤
      (productConstant : ENNReal) *
        multiplicity coarseSet (fun k ↦ (coarseShade k).toShadedBody) *
        multiplicity (activeFibre fineSet parent j)
          (fun i ↦ (fineShade i).toShadedBody)
  coarse_fullness : productConstant⁻¹ * fullness F.innerSet F.innerBody ≤
    fullness coarseSet (fun j ↦ (coarseShade j).toShadedBody)
  coarse_maxDensity :
    maxDensity coarseSet (fun j ↦ (coarseShade j).toConvexSpaceBody) =
      maxDensity coarseSet (fun j ↦ Tube.dilate (Tρ j) (c : ℝ))
  raw_parent_containment : ∀ i ∈ fineSet,
    (T i).toConvexSpaceBody ≤ Tube.dilate (Tρ (parent i)) (c : ℝ)
  presented_parent_containment : ∀ i ∈ fineSet,
    (Tube.undilateAtZero (c : ℝ) (T i).toTube).toConvexSpaceBody ≤
      Tube.dilate (Tube.undilateAtZero (c : ℝ) (Tρ (parent i)))
        (6 + 4 * (c : ℝ))

/-- The clean raw dilated Proposition 5.1 output admits an honest, product-only presentation.

There is no spatial cover and no shade pigeonhole here.  A single common inverse homothety is
applied to the whole coarse family, so its multiplicity and fullness are unchanged. -/
theorem exists_honestDilateProductOutput
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hc : 1 ≤ c)
    (F : ShadedBody.FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = Tube.dilate (Tρ j) (c : ℝ))
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank ℝ E) F.innerSet.card δ c
    ∃ (fineSet : Finset ι) (coarseSet : Finset κ)
      (fineShade : ι → ShadedTube δ E) (coarseShade : κ → ShadedTube ρ E)
      (parent : ι → κ),
      HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade parent
        cprod := by
  classical
  let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
    (Module.finrank ℝ E) F.innerSet.card δ c
  obtain ⟨G, hGouter, hGinner, hGparent, hGouterBody, hGinnerBody,
      hGnonempty, hGfull, hGref, hGproduct, hGcontain, hGvolume, _hGthick⟩ :=
    shadingMultiplicityEstimateForRhoTubesDilate hδ hρ hc F T Tρ hinner houter hball
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hcR0 : (0 : ℝ) < (c : ℝ) := zero_lt_one.trans_le hcR
  have hfineCarrier : ∀ i ∈ G.innerSet,
      (G.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody := by
    intro i hi
    exact (hGinnerBody i (hGref.1.1 hi)).trans (congrArg ShadedBody.toConvexSpaceBody
      (hinner i (hGref.1.1 hi)))
  have hcoarseCarrier : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = Tube.dilate (Tρ j) (c : ℝ) := by
    intro j hj
    exact (hGouterBody j hj).trans (houter j (hGouter hj))
  let Zfine := toShadedTubeOfCarrierOn G.innerSet G.innerBody
    (fun i ↦ (T i).toTube) hfineCarrier
  let Zcoarse := undilateTubePresentationOn G.outerSet G.outerBody Tρ hcR0.ne'
    hcoarseCarrier
  have hcoarseMult :
      multiplicity G.outerSet (fun j ↦ (Zcoarse j).toShadedBody) =
        multiplicity G.outerSet G.outerBody := by
    exact multiplicity_undilateTubePresentationOn G.outerSet G.outerBody Tρ hcR0.ne'
      hcoarseCarrier
  have hfineMult (j : κ) :
      multiplicity (G.fiber j) (fun i ↦ (Zfine i).toShadedBody) =
        multiplicity (G.fiber j) G.innerBody := by
    apply _root_.Tube.multiplicity_congr_of_shading_eq
    intro i hi
    have hiInner : i ∈ G.innerSet := by
      have hipair : i ∈ G.innerSet ∧ G.parent i = j := by
        simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
      exact hipair.1
    exact toShadedTubeOfCarrierOn_shade_of_mem G.innerBody (fun i ↦ (T i).toTube)
      hfineCarrier hiInner
  have hfibre (j : κ) : activeFibre G.innerSet G.parent j = G.fiber j := by
    ext i
    simp only [activeFibre, ShadedFactorFamily.fiber, Finset.mem_filter]
  have hZfineEq (i : ι) (hi : i ∈ G.innerSet) :
      (Zfine i).toShadedBody = G.innerBody i := by
    apply eq_of_toConvexSpaceBody_eq_of_shade_eq
    · have hztube : (Zfine i).toTube = (T i).toTube :=
        toShadedTubeOfCarrierOn_toTube G.innerSet G.innerBody
          (fun k ↦ (T k).toTube) hfineCarrier i
      exact (congrArg (fun U : Tube δ E ↦ U.toConvexSpaceBody) hztube).trans
        (hfineCarrier i hi).symm
    · exact toShadedTubeOfCarrierOn_shade_of_mem G.innerBody
        (fun k ↦ (T k).toTube) hfineCarrier hi
  have hZfineRef : IsCRefinement G.innerSet (fun i ↦ (Zfine i).toShadedBody)
      F.innerSet F.innerBody cprod⁻¹ := by
    refine ⟨⟨hGref.1.1, ?_⟩, ?_⟩
    · intro i hi
      change (Zfine i).toShadedBody.toConvexSpaceBody =
          (F.innerBody i).toConvexSpaceBody ∧
        (Zfine i).toShadedBody.shade ⊆ (F.innerBody i).shade
      rw [hZfineEq i hi]
      exact hGref.1.2 i hi
    · have hret : ((cprod⁻¹ : NNReal) : ENNReal) *
          ∑ i ∈ F.innerSet, volume (F.innerBody i).shade ≤
            ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
        simpa only [cprod] using hGref.2
      calc
        ((cprod⁻¹ : NNReal) : ENNReal) * ∑ i ∈ F.innerSet,
            volume (F.innerBody i).shade ≤
            ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := hret
        _ = ∑ i ∈ G.innerSet, volume (Zfine i).shade := by
          apply Finset.sum_congr rfl
          intro i hi
          exact congrArg (fun W : ShadedBody E ↦ volume W.shade) (hZfineEq i hi).symm
  refine ⟨G.innerSet, G.outerSet, Zfine, Zcoarse, G.parent, ?_⟩
  exact
    { fine_subset := hGref.1.1
      coarse_subset := hGouter
      coarse_nonempty := hGnonempty hmass
      parent_eq := hGparent
      parent_mem := fun i hi ↦ G.parent_mem i hi
      fine_eq_filter := by
        ext i
        rw [hGinner]
        simp only [Finset.mem_filter]
        rw [hGparent]
      fine_tube := fun i ↦ toShadedTubeOfCarrierOn_toTube G.innerSet G.innerBody
        (fun i ↦ (T i).toTube) hfineCarrier i
      fine_refinement := hZfineRef
      coarse_tube := fun j ↦ undilateTubePresentationOn_toTube G.outerSet G.outerBody
        Tρ hcR0.ne' hcoarseCarrier j
      product := by
        intro j hj
        calc
          multiplicity F.innerSet F.innerBody ≤
              (cprod : ENNReal) * multiplicity G.outerSet G.outerBody *
                multiplicity (G.fiber j) G.innerBody := hGproduct j hj
          _ = (cprod : ENNReal) *
              multiplicity G.outerSet (fun k ↦ (Zcoarse k).toShadedBody) *
                multiplicity (activeFibre G.innerSet G.parent j)
                  (fun i ↦ (Zfine i).toShadedBody) := by
            rw [hcoarseMult, hfibre, hfineMult]
      coarse_fullness := by
        calc
          cprod⁻¹ * fullness F.innerSet F.innerBody ≤
              fullness G.outerSet G.outerBody := hGfull
          _ = fullness G.outerSet (fun j ↦ (Zcoarse j).toShadedBody) := by
            symm
            exact fullness_undilateTubePresentationOn G.outerSet G.outerBody Tρ
              hcR0.ne' hcoarseCarrier
      coarse_maxDensity := by
        calc
          maxDensity G.outerSet (fun j ↦ (Zcoarse j).toConvexSpaceBody) =
              maxDensity G.outerSet (fun j ↦ (G.outerBody j).toConvexSpaceBody) :=
            maxDensity_undilateTubePresentationOn G.outerSet G.outerBody Tρ
              hcR0.ne' hcoarseCarrier
          _ = maxDensity G.outerSet (fun j ↦ Tube.dilate (Tρ j) (c : ℝ)) := by
            apply maxDensity_congr
            intro j hj
            exact hcoarseCarrier j hj
      raw_parent_containment := by
        intro i hi
        rw [hGparent]
        calc
          (T i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody :=
            congrArg ShadedBody.toConvexSpaceBody (hinner i (hGref.1.1 hi)).symm
          _ ≤ F.outerBody (F.parent i) := F.inner_le_parent i (hGref.1.1 hi)
          _ = Tube.dilate (Tρ (F.parent i)) (c : ℝ) :=
            houter (F.parent i) (F.parent_mem i (hGref.1.1 hi))
      presented_parent_containment := by
        intro i hi
        apply Tube.undilateAtZero_le_dilate_of_le_dilate hρ.1 hρ.2 hcR hcR0
        simpa only [hGparent] using
          (show (T i).toConvexSpaceBody ≤ Tube.dilate (Tρ (G.parent i)) (c : ℝ) by
            rw [hGparent]
            calc
              (T i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody :=
                congrArg ShadedBody.toConvexSpaceBody (hinner i (hGref.1.1 hi)).symm
              _ ≤ F.outerBody (F.parent i) := F.inner_le_parent i (hGref.1.1 hi)
              _ = Tube.dilate (Tρ (F.parent i)) (c : ℝ) :=
                houter (F.parent i) (F.parent_mem i (hGref.1.1 hi))) }

/-- The presented honest coarse family inherits the plank-family maximal-density estimate with
only the fixed volume factor of the common dilation. -/
theorem HonestDilateProductOutput.coarse_maxDensity_le
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    (hc : 1 < (c : ℝ)) :
    maxDensity coarseSet (fun j ↦ (coarseShade j).toConvexSpaceBody) ≤
      ENNReal.ofReal ((c : ℝ) ^ Module.finrank ℝ E) *
        maxDensity coarseSet (fun j ↦ (Tρ j).toConvexSpaceBody) := by
  calc
    maxDensity coarseSet (fun j ↦ (coarseShade j).toConvexSpaceBody) =
        maxDensity coarseSet (fun j ↦ Tube.dilate (Tρ j) (c : ℝ)) :=
      h.coarse_maxDensity
    _ ≤ ENNReal.ofReal ((c : ℝ) ^ Module.finrank ℝ E) *
        maxDensity coarseSet (fun j ↦ (Tρ j).toConvexSpaceBody) :=
      Tube.maxDensity_dilate_le coarseSet Tρ hc

/-- A centred ball bound for the original plank tubes gives a radius-doubled ball bound for the
honest presented coarse output. -/
theorem HonestDilateProductOutput.coarse_carrier_subset_closedBall
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    (hc : 1 ≤ (c : ℝ)) {R : ℝ}
    (hball : ∀ j ∈ coarseSet, (Tρ j).carrier ⊆ Metric.closedBall 0 R) :
    ∀ j ∈ coarseSet, (coarseShade j).carrier ⊆ Metric.closedBall 0 (2 * R) := by
  intro j hj
  rw [congrArg (fun U : Tube ρ E ↦ U.carrier) (h.coarse_tube j)]
  exact Tube.undilateAtZero_carrier_subset_closedBall hc (Tρ j) (hball j hj)

/-- Frostman transport for the exact honest coarse witness returned by the producer. -/
theorem HonestDilateProductOutput.coarse_frostmanConstIn_le
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ} {T : ι → ShadedTube δ E}
    {Tρ : κ → Tube ρ E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι → ShadedTube δ E} {coarseShade : κ → ShadedTube ρ E}
    {parent : ι → κ} {productConstant : NNReal}
    (h : HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
      parent productConstant)
    {K L : ConvexSpaceBody E} (hc : 1 < (c : ℝ))
    (hTK : ∀ j ∈ coarseSet, (Tρ j).toConvexSpaceBody ≤ K)
    (hTL : ∀ j ∈ coarseSet, Tube.dilate (Tρ j) (c : ℝ) ≤ L)
    (hK0 : volume K.carrier ≠ 0) (hL0 : volume L.carrier ≠ 0) :
    frostmanConstIn coarseSet (fun j ↦ (coarseShade j).toConvexSpaceBody)
        (L.homothety 0 ((c : ℝ)⁻¹)) ≤
      volume L.carrier / volume K.carrier *
        frostmanConstIn coarseSet (fun j ↦ (Tρ j).toConvexSpaceBody) K := by
  have hbody : (fun j ↦ (coarseShade j).toConvexSpaceBody) =
      (fun j ↦ (Tube.undilateAtZero (c : ℝ) (Tρ j)).toConvexSpaceBody) := by
    funext j
    exact congrArg (fun U : Tube ρ E ↦ U.toConvexSpaceBody) (h.coarse_tube j)
  rw [hbody]
  exact Tube.frostmanConstIn_undilateAtZero_le coarseSet Tρ hc hTK hTL hK0 hL0

/-- Package an already-refined honest parent family as the raw input expected by the clean
dilated Proposition 5.1 theorem.  This is intentionally downstream of any merge, plank
selection, or parent deduplication. -/
noncomputable def factorFamilyOfParentDilate
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal} {u : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E) (p : ι → κ)
    (hmaps : ∀ i ∈ u, p i ∈ t)
    (hle : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ Tube.dilate (Tρ (p i)) (c : ℝ)) :
    ShadedBody.FactorFamily E ι κ where
  innerSet := u
  innerBody := fun i ↦ (T i).toShadedBody
  outerSet := t
  outerBody := fun j ↦ Tube.dilate (Tρ j) (c : ℝ)
  parent := p
  parent_mem := hmaps
  inner_le_parent := hle

/-- Reordered composition interface: first construct/refine the honest parent family, then run
the raw dilated factor, and only then apply the common honest presentation.

This theorem consumes exactly the `IsParentFamilyDilate` conclusion exported by the plank-parent
producers.  Thus `exists_merged_rhoParentFamily` and
`exists_plankTube_parentFamily_dilate` may run before this theorem; no parent or plank refinement
is attempted after product factorization. -/
theorem exists_honestProduct_after_parentRefinement
    {ι : Type v} {κ : Type w} [DecidableEq κ]
    {δ ρ c : NNReal} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1) (hc : 1 ≤ c)
    {u : Finset ι} {t : Finset κ}
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E) (p : ι → κ)
    (hmaps : ∀ i ∈ u, p i ∈ t)
    (hle : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ Tube.dilate (Tρ (p i)) (c : ℝ))
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ u, volume (T i).shade) :
    let F := factorFamilyOfParentDilate T Tρ p hmaps hle
    let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank ℝ E) u.card δ c
    ∃ (fineSet : Finset ι) (coarseSet : Finset κ)
      (fineShade : ι → ShadedTube δ E) (coarseShade : κ → ShadedTube ρ E)
      (parent : ι → κ),
      HonestDilateProductOutput (c := c) F T Tρ fineSet coarseSet fineShade coarseShade
        parent cprod := by
  let F := factorFamilyOfParentDilate T Tρ p hmaps hle
  simpa only [F, factorFamilyOfParentDilate] using
    (exists_honestDilateProductOutput hδ ⟨hδρ, hρ1⟩ hc F T Tρ
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (by simpa [F, factorFamilyOfParentDilate] using hball)
      (by simpa [F, factorFamilyOfParentDilate] using hmass))

end

end Kakeya.ml1CoarseHonestW45

#print axioms Kakeya.ml1CoarseHonestW45.exists_honestDilateProductOutput
#print axioms Kakeya.ml1CoarseHonestW45.exists_honestProduct_after_parentRefinement
#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.coarse_maxDensity_le
#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.coarse_carrier_subset_closedBall
#print axioms Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput.coarse_frostmanConstIn_le

end
