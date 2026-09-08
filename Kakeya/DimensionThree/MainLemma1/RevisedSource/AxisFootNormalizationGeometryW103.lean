module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceAssignedNormalizationW97
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Hybrid
public import Kakeya.ConvexBody.DilateWitness

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem tube_eq_of_center_direction_w103 {r : NNReal} (T V : Tube r E)
    (hc : T.center = V.center) (hd : T.direction = V.direction) : T = V := by
  have hx : T.x = V.x := by rw [Tube.x_eq_center_sub, Tube.x_eq_center_sub, hc, hd]
  have hy : T.y = V.y := by rw [Tube.y_eq_center_add, Tube.y_eq_center_add, hc, hd]
  apply Tube.ext ?_ hx hy
  rw [T.carrier_eq, V.carrier_eq, hx, hy]

def axisFootTubeW103 {r : NNReal} (s : NNReal) (L : E ≃ᵃ[Real] E) (T : Tube r E) :
    Tube s E :=
  let v := L.linear T.direction
  have hv : ‖v‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hd : T.direction = 0 := L.linear.injective (h.trans (map_zero L.linear).symm)
    have := T.norm_direction
    rw [hd, norm_zero] at this
    norm_num at this
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv]
  Tube.ofMidpointDirection s (L T.center - inner Real (L T.center) u • u) u hu

theorem axisFootTube_direction_w103 {r s : NNReal} (L : E ≃ᵃ[Real] E) (T : Tube r E) :
    (axisFootTubeW103 s L T).direction = ‖L.linear T.direction‖⁻¹ • L.linear T.direction := by
  simp only [axisFootTubeW103, Tube.direction_ofMidpointDirection']

theorem axisFootTube_center_w103 {r s : NNReal} (L : E ≃ᵃ[Real] E) (T : Tube r E) :
    (axisFootTubeW103 s L T).center = L T.center -
      inner Real (L T.center) (axisFootTubeW103 s L T).direction •
        (axisFootTubeW103 s L T).direction := by
  rw [axisFootTube_direction_w103]
  have hmid (V : Tube s E) : V.center = V.midpoint := by
    simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
    norm_num
  rw [hmid]
  simp only [axisFootTubeW103, Tube.midpoint_ofMidpointDirection']

theorem axisFootTube_centred_w103 {r s : NNReal} (L : E ≃ᵃ[Real] E) (T : Tube r E) :
    centredTubeW94 (axisFootTubeW103 s L T) := by
  unfold centredTubeW94
  rw [axisFootTube_center_w103, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, Tube.norm_direction]
  norm_num

theorem axisFootTube_unique_w103 {r s : NNReal} (L : E ≃ᵃ[Real] E) (T : Tube r E)
    (V : Tube s E)
    (hd : V.direction = ‖L.linear T.direction‖⁻¹ • L.linear T.direction)
    (hc : V.center = L T.center - inner Real (L T.center) V.direction • V.direction) :
    V = axisFootTubeW103 s L T := by
  apply tube_eq_of_center_direction_w103
  · rw [hc, axisFootTube_center_w103, hd, axisFootTube_direction_w103]
  · rw [hd, axisFootTube_direction_w103]

theorem axisFootTube_center_norm_w103 {r s : NNReal} (L : E ≃ᵃ[Real] E) (T : Tube r E) :
    ‖(axisFootTubeW103 s L T).center‖ <= ‖L T.center‖ := by
  rw [axisFootTube_center_w103, real_inner_comm]
  exact Tube.norm_perp_le _ _

theorem axisFootTube_image_w103 {r theta R : NNReal} (hr : 0 < r)
    (hrt : r <= theta) (ht1 : theta <= 1) (hR : 1 <= R)
    (hRn : Tube.normalization.C (Module.finrank Real E) <= R)
    (top : Tube theta E) (T : Tube r E) (hT : T.toConvexSpaceBody <= top.toConvexSpaceBody)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real)) :
    L '' T.carrier ⊆ (axisFootTubeW103 (r / theta) L T).carrier ∧
      ‖(axisFootTubeW103 (r / theta) L T).center‖ <= 1 / 4 := by
  have ht : 0 < theta := hr.trans_le hrt
  have hRpos : (0 : Real) < R := zero_lt_one.trans_le hR
  have hball : L '' top.carrier ⊆ Metric.closedBall 0 (1 / 4 : Real) := by
    change L.toAffineMap '' top.carrier ⊆ _
    rw [hL]
    exact Tube.rescale_image_ambient_subset_closedBall ht ht1 hRpos hRn top
  let W := axisFootTubeW103 (r / theta) L T
  let u := W.direction
  let v := L.linear T.direction
  let x := L T.center
  have hv : ‖v‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hz : T.direction = 0 := L.linear.injective (h.trans (map_zero L.linear).symm)
    have := T.norm_direction
    rw [hz, norm_zero] at this
    norm_num at this
  have hu : ‖u‖ = 1 := W.norm_direction
  have hvu : ‖v‖ • u = v := by
    dsimp only [u, W]
    rw [axisFootTube_direction_w103, smul_smul, mul_inv_cancel₀ hv, one_smul]
  have hmidpoint (V : Tube r E) : V.midpoint = V.center := by
    simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
    norm_num
  have hx : ‖x‖ <= 1 / 4 := by
    have hc : T.center ∈ T.carrier := hmidpoint T ▸ Tube.midpoint_mem_carrier hr T
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball ⟨T.center, hT hc, rfl⟩
  have hWc : ‖W.center‖ <= 1 / 4 := (axisFootTube_center_norm_w103 L T).trans hx
  have haxis : ∀ p ∈ segment Real T.x T.y,
      L p = W.center + inner Real (L p) u • u := by
    rintro p ⟨a, b, ha, hb, hab, rfl⟩
    have hpoint : a • T.x + b • T.y = T.center + (b - 1 / 2 : Real) • T.direction := by
      rw [Tube.x_eq_center_sub, Tube.y_eq_center_add, show a = 1 - b by linarith]
      module
    have himage : L (a • T.x + b • T.y) = x + ((b - 1 / 2) * ‖v‖) • u := by
      rw [hpoint, add_comm T.center, show L ((b - 1 / 2 : Real) • T.direction + T.center) =
          L.linear ((b - 1 / 2 : Real) • T.direction) + L T.center from
            L.map_vadd T.center ((b - 1 / 2 : Real) • T.direction), map_smul]
      change (b - 1 / 2 : Real) • v + x = _
      conv_lhs => rw [← hvu]
      rw [smul_smul, add_comm]
    rw [himage]
    have huu : inner Real u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
    simp only [inner_add_left, real_inner_smul_left, huu, mul_one]
    rw [show W.center = x - inner Real x u • u from axisFootTube_center_w103 L T]
    module
  have hcore : ∀ p ∈ segment Real T.x T.y, L p ∈ segment Real W.x W.y := by
    intro p hp
    have hpT : p ∈ T.carrier := by
      rw [T.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self r.coe_nonneg⟩
    have hpNorm : ‖L p‖ <= 1 / 4 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball ⟨p, hT hpT, rfl⟩
    have hcoord : |inner Real (L p) u| <= 1 / 4 := by
      calc |inner Real (L p) u| <= ‖L p‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ <= 1 / 4 := by rw [hu, mul_one]; exact hpNorm
    have hseg := W.midpoint_add_smul_direction_mem_segment (s := inner Real (L p) u)
      (by linarith [(abs_le.mp hcoord).1]) (by linarith [(abs_le.mp hcoord).2])
    have hmidW : W.midpoint = W.center := by
      simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
      norm_num
    rw [hmidW, ← haxis p hp] at hseg
    exact hseg
  refine ⟨?_, hWc⟩
  rintro z ⟨y, hy, rfl⟩
  rw [T.carrier_eq] at hy
  obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
  change L y ∈ W.carrier
  rw [W.carrier_eq]
  refine Set.mem_iUnion₂.mpr ⟨L p, hcore p hp, Metric.mem_closedBall.mpr ?_⟩
  have hdist := Metric.mem_closedBall.mp hyp
  have hupper : dist (L y) (L p) <= (theta : Real)⁻¹ * dist y p / (4 * (R : Real)) := by
    change dist (L.toAffineMap y) (L.toAffineMap p) <= _
    rw [hL, Tube.dist_rescaleMap top hRpos]
    exact div_le_div_of_nonneg_right (Tube.dist_normalization_le ht ht1 top y p) (by positivity)
  calc
    dist (L y) (L p) <= (theta : Real)⁻¹ * dist y p / (4 * (R : Real)) := hupper
    _ <= (theta : Real)⁻¹ * r / (4 * (R : Real)) := by gcongr
    _ <= (theta : Real)⁻¹ * r := by
      apply div_le_self (by positivity)
      have hh : (1 : Real) <= R := hR
      nlinarith
    _ = ((r / theta : NNReal) : Real) := by push_cast; ring

theorem tube_ball_of_center_w103 {r : NNReal} (T : Tube r E) {B : Real}
    (hT : ‖T.center‖ <= B) : T.carrier ⊆ Metric.closedBall 0 (B + 1 / 2 + (r : Real)) := by
  intro z hz
  rw [T.carrier_eq] at hz
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  have hpBall : p ∈ Metric.closedBall T.center (1 / 2 : Real) := by
    apply (convex_closedBall T.center (1 / 2 : Real)).segment_subset ?_ ?_ hp
    · rw [Metric.mem_closedBall, dist_eq_norm, Tube.x_eq_center_sub]
      simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, T.norm_direction]
      norm_num
    · rw [Metric.mem_closedBall, dist_eq_norm, Tube.y_eq_center_add]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, T.norm_direction]
      norm_num
  have hp' := Metric.mem_closedBall.mp hpBall
  have hzp' := Metric.mem_closedBall.mp hzp
  have htri := dist_triangle z p T.center
  have hn := norm_add_le (z - T.center) T.center
  rw [sub_add_cancel, ← dist_eq_norm] at hn
  rw [Metric.mem_closedBall, dist_zero_right]
  linarith

theorem axisFootTube_homothety_w103 {r theta R : NNReal} (hr : 0 < r)
    (hrt : r <= theta) (ht1 : theta <= 1) (hR : 0 < R)
    (top : Tube theta E) (T : Tube r E) (hT : T.toConvexSpaceBody <= top.toConvexSpaceBody)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real))
    (hcenter : ‖L T.center‖ <= 1 / 4) :
    (axisFootTubeW103 (r / theta) L T).carrier ⊆
      (fun z => (48 * (R : Real)) • (z - L T.center) + L T.center) '' (L '' T.carrier) := by
  let W := axisFootTubeW103 (r / theta) L T
  let x := L T.center
  let u := W.direction
  let S : Tube ((r / theta) / 4) E := Tube.ofMidpointDirection ((r / theta) / 4) x u W.norm_direction
  have hSc : S.center = x := (Kakeya.ml1Boot.ofMidpointDirection_center_direction x u W.norm_direction).1
  have hSd : S.direction = u := (Kakeya.ml1Boot.ofMidpointDirection_center_direction x u W.norm_direction).2
  have ht : (0 : Real) < theta := hr.trans_le hrt
  have hRr : (0 : Real) < R := hR
  have hnorm : u = ‖top.normalizationLinear T.direction‖⁻¹ • top.normalizationLinear T.direction := by
    dsimp only [u, W]
    rw [axisFootTube_direction_w103]
    have hlin : L.linear T.direction = (4 * (R : Real))⁻¹ • top.normalizationLinear T.direction := by
      have hd : L.toAffineMap.linear T.direction = L.toAffineMap T.direction - L.toAffineMap 0 := by
        simpa only [vsub_eq_sub, sub_zero] using L.toAffineMap.linearMap_vsub T.direction 0
      change L.toAffineMap.linear T.direction = _
      rw [hd, hL, Kakeya.ml1Boot.rescaleMap_sub, sub_zero]
    rw [hlin]
    exact Kakeya.ml1Boot.normalize_smul (by positivity) _
  have hsmall : ((r / theta : NNReal) : Real) <= 1 := by
    rw [NNReal.coe_div]
    exact (div_le_one ht).mpr hrt
  have hxmap : x = top.rescaleMap (R : Real) T.center :=
    congrArg (fun f : E →ᵃ[Real] E => f T.center) hL
  have hSimage : S.carrier ⊆
      (fun z => (12 * (R : Real)) • (z - x) + x) '' (L '' T.carrier) := by
    change S.carrier ⊆ (fun z => (12 * (R : Real)) • (z - x) + x) '' (L.toAffineMap '' T.carrier)
    rw [hL, hxmap]
    refine Kakeya.ml1Boot.carrier_subset_homothety_rescaleMap_image hRr ht ht1 hrt ?_ ?_
      top T S hT (hSc.trans hxmap) (hSd.trans hnorm)
    · push_cast
      have ht0 : (theta : Real) ≠ 0 := ht.ne'
      have hh : (r : Real) / theta / 4 * theta = (r : Real) / 4 := by field_simp
      rw [hh]
      exact div_le_self r.coe_nonneg (by norm_num)
    · change (((r / theta : NNReal) : Real) / 4) <= 1 / 4
      linarith
  intro z hz
  rw [show (axisFootTubeW103 (r / theta) L T).carrier = W.carrier from rfl, W.carrier_eq] at hz
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t, ht', hpt⟩ := W.exists_param_of_mem_segment hp
  have hmid : W.midpoint = W.center := by
    simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
    norm_num
  rw [hmid] at hpt
  let a : Real := inner Real x u
  have ha : |a| <= 1 / 4 := by
    calc |a| <= ‖x‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ <= 1 / 4 := by rw [show ‖u‖ = 1 from W.norm_direction, mul_one]; exact hcenter
  let y := x + (1 / 4 : Real) • (z - x)
  let q := S.center + ((t - a) / 4) • S.direction
  have hq : q ∈ segment Real S.x S.y := by
    have hs : |(t - a) / 4| <= 1 / 2 := by
      rw [abs_div]
      norm_num only [abs_of_pos (by norm_num : (0 : Real) < 4)]
      have hta := abs_sub t a
      linarith
    have hh := S.midpoint_add_smul_direction_mem_segment (s := (t - a) / 4)
      (abs_le.mp hs).1 (abs_le.mp hs).2
    have hm : S.midpoint = S.center := by
      simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
      norm_num
    rwa [hm] at hh
  have hy : y ∈ S.carrier := by
    rw [S.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨q, hq, Metric.mem_closedBall.mpr ?_⟩
    have hyq : y - q = (1 / 4 : Real) • (z - p) := by
      rw [hpt, show W.center = x - a • u from axisFootTube_center_w103 L T]
      dsimp only [y, q]
      rw [hSc, hSd]
      change _ = (1 / 4 : Real) • (z - (x - a • u + t • u))
      module
    rw [dist_eq_norm, hyq, norm_smul, Real.norm_eq_abs]
    norm_num only [abs_div, abs_one, abs_of_pos (by norm_num : (0 : Real) < 4)]
    have hh := Metric.mem_closedBall.mp hzp
    rw [dist_eq_norm] at hh
    change _ <= ((r / theta : NNReal) : Real) / 4
    linarith
  obtain ⟨w, ⟨v, hv, hw⟩, hwy⟩ := hSimage hy
  refine ⟨L v, ⟨v, hv, rfl⟩, ?_⟩
  subst w
  have hy' : (4 : Real) • (y - x) + x = z := by dsimp [y]; module
  rw [← hy', ← hwy]
  module

theorem rescale_jacobian_w103 (hdim : Module.finrank Real E = 3)
    {theta R : NNReal} (htheta : 0 < theta) (hR : 0 < R) (top : Tube theta E) :
    ∃ J : NNReal, 0 < J ∧
      (J : ENNReal) = (4 * (R : ENNReal)) ^ (-3 : Real) * (theta : ENNReal) ^ (-2 : Real) ∧
      ∀ S : Set E, volume (top.rescaleMap (R : Real) '' S) = (J : ENNReal) * volume S := by
  let J : NNReal := (4 * R)⁻¹ ^ (3 : Nat) * theta⁻¹ ^ (2 : Nat)
  have hJ : (J : ENNReal) = (4 * (R : ENNReal))⁻¹ ^ (3 : Nat) *
      (theta : ENNReal)⁻¹ ^ (2 : Nat) := by
    dsimp only [J]
    rw [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_pow,
      ENNReal.coe_inv (by positivity : (4 * R : NNReal) ≠ 0),
      ENNReal.coe_inv htheta.ne', ENNReal.coe_mul, ENNReal.coe_ofNat]
  refine ⟨J, by dsimp [J]; positivity, ?_, ?_⟩
  · rw [hJ]
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg,
      show (4 * (R : ENNReal)) ^ (3 : Real) = (4 * (R : ENNReal)) ^ (3 : Nat) from
        ENNReal.rpow_natCast _ _,
      show (theta : ENNReal) ^ (2 : Real) = (theta : ENNReal) ^ (2 : Nat) from
        ENNReal.rpow_natCast _ _, ENNReal.inv_pow, ENNReal.inv_pow]
  · intro S
    have h := Tube.volume_image_rescaleMap htheta (show (0 : Real) < R from hR) top S
    rw [hdim] at h
    norm_num only [Nat.reduceSub] at h
    rw [h]
    rw [hJ]
    rw [mul_assoc]
    congr 1
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

theorem affine_inverse_volume_w103 (L : E ≃ᵃ[Real] E) {J : NNReal} (hJ : 0 < J)
    (hvol : ∀ S : Set E, volume (L '' S) = (J : ENNReal) * volume S) (K : Set E) :
    volume (L.symm '' K) = (J : ENNReal)⁻¹ * volume K := by
  have hcancel : L '' (L.symm '' K) = K := by
    rw [← Set.image_comp]
    simp only [Function.comp_def, L.apply_symm_apply, Set.image_id']
  calc
    volume (L.symm '' K) = (J : ENNReal)⁻¹ * ((J : ENNReal) * volume (L.symm '' K)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hJ.ne') ENNReal.coe_ne_top, one_mul]
    _ = (J : ENNReal)⁻¹ * volume K := by rw [← hvol, hcancel]

theorem axisFootTube_volume_w103 (hdim : Module.finrank Real E = 3)
    {r theta R : NNReal} (hr : 0 < r) (hrt : r <= theta) (ht1 : theta <= 1)
    (hR : 1 <= R) (hRn : Tube.normalization.C (Module.finrank Real E) <= R)
    (top : Tube theta E) (T : Tube r E) (hT : T.toConvexSpaceBody <= top.toConvexSpaceBody)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real)) :
    volume (L '' T.carrier) <= volume (axisFootTubeW103 (r / theta) L T).carrier ∧
      volume (axisFootTubeW103 (r / theta) L T).carrier <=
        (((48 * R) ^ (3 : Nat) : NNReal) : ENNReal) * volume (L '' T.carrier) := by
  have himage := (axisFootTube_image_w103 hr hrt ht1 hR hRn top T hT L hL).1
  have ht : 0 < theta := hr.trans_le hrt
  have hRp : (0 : Real) < R := zero_lt_one.trans_le hR
  have hball : L '' top.carrier ⊆ Metric.closedBall 0 (1 / 4 : Real) := by
    change L.toAffineMap '' top.carrier ⊆ _
    rw [hL]
    exact Tube.rescale_image_ambient_subset_closedBall ht ht1 hRp hRn top
  have hmid : T.midpoint = T.center := by
    simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
    norm_num
  have hc : T.center ∈ T.carrier := hmid ▸ Tube.midpoint_mem_carrier hr T
  have hcenter : ‖L T.center‖ <= 1 / 4 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball ⟨T.center, hT hc, rfl⟩
  have hhom := axisFootTube_homothety_w103 hr hrt ht1 (zero_lt_one.trans_le hR) top T hT L hL hcenter
  let B := T.toConvexSpaceBody.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous
  have hsub : (axisFootTubeW103 (r / theta) L T).carrier ⊆
      (B.homothety (L T.center) (48 * (R : Real))).carrier := by
    exact hhom
  refine ⟨measure_mono himage, (measure_mono hsub).trans ?_⟩
  rw [ConvexSpaceBody.volume_homothety, hdim]
  rw [abs_pow, ENNReal.ofReal_pow (abs_nonneg _)]
  change ENNReal.ofReal |48 * (R : Real)| ^ (3 : Nat) * volume (L '' T.carrier) <= _
  rw [abs_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  norm_cast

theorem axisFoot_family_forward_test_w103 (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {r theta R : NNReal} (hr : 0 < r) (hrt : r <= theta)
    (ht1 : theta <= 1) (hR : 1 <= R)
    (hRn : Tube.normalization.C (Module.finrank Real E) <= R)
    (top : Tube theta E) (F : Finset iota) (T : iota -> Tube r E)
    (hT : ∀ i ∈ F, (T i).toConvexSpaceBody <= top.toConvexSpaceBody)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real))
    (K : ConvexSpaceBody E) :
    ∃ D : ConvexSpaceBody E,
      K.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous <= D ∧
      volume D.carrier <= (((192 * R) ^ (3 : Nat) * 6 : NNReal) : ENNReal) * volume (L '' K.carrier) ∧
      (∀ i ∈ F, (T i).toConvexSpaceBody <= K ->
        (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody <= D) := by
  let W := fun i => (T i).toConvexSpaceBody.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous
  let V := fun i => (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody
  have hnonzero : ∀ i ∈ F, volume (W i).carrier ≠ 0 := by
    intro i hi
    rw [ConvexSpaceBody.volume_affineImage]
    apply mul_ne_zero (Kakeya.ofReal_abs_det_affineEquiv_ne_zero L)
    have hc := Tube.le_volume.c_pos (Module.finrank Real E)
    exact (lt_of_lt_of_le (by positivity) (Tube.le_volume (T i))).ne'
  have hhom : ∀ i ∈ F, ∃ p ∈ (W i).carrier,
      (V i).carrier ⊆ (fun x => (48 * (R : Real)) • (x - p) + p) '' (W i).carrier := by
    intro i hi
    have hmid : (T i).midpoint = (T i).center := by
      simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
      norm_num
    have htc : (T i).center ∈ (T i).carrier := hmid ▸ Tube.midpoint_mem_carrier hr (T i)
    have ht : 0 < theta := hr.trans_le hrt
    have hRp : (0 : Real) < R := zero_lt_one.trans_le hR
    have hball : L '' top.carrier ⊆ Metric.closedBall 0 (1 / 4 : Real) := by
      change L.toAffineMap '' top.carrier ⊆ _
      rw [hL]
      exact Tube.rescale_image_ambient_subset_closedBall ht ht1 hRp hRn top
    have hcenter : ‖L (T i).center‖ <= 1 / 4 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball ⟨(T i).center, hT i hi htc, rfl⟩
    exact ⟨L (T i).center, ⟨(T i).center, htc, rfl⟩,
      axisFootTube_homothety_w103 hr hrt ht1 (zero_lt_one.trans_le hR) top (T i) (hT i hi) L hL hcenter⟩
  obtain ⟨D, hKD, hvolD, hVD⟩ := ConvexSpaceBody.exists_enlargement_of_homothety
    (by have hh : (1 : Real) <= R := hR; nlinarith : (1 : Real) <= 48 * R)
    hnonzero hhom (K.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous)
  refine ⟨D, hKD, ?_, ?_⟩
  · rw [hdim] at hvolD
    norm_num only [Nat.factorial] at hvolD
    convert hvolD using 1 <;> norm_num [mul_assoc, ENNReal.ofReal_mul] <;> ring
  · intro i hi hiK
    apply hVD i hi
    exact (ConvexSpaceBody.affineImage_le_affineImage_iff L.toAffineMap
      L.toContinuousAffineEquiv.continuous L.injective).mpr hiK

theorem axisFoot_family_backward_test_w103 {iota : Type uI} {r theta : NNReal}
    (F : Finset iota) (T : iota -> Tube r E) (L : E ≃ᵃ[Real] E)
    (himage : ∀ i ∈ F, L '' (T i).carrier ⊆ (axisFootTubeW103 (r / theta) L (T i)).carrier)
    {J : NNReal} (hJ : 0 < J)
    (hvol : ∀ S : Set E, volume (L '' S) = (J : ENNReal) * volume S)
    (K : ConvexSpaceBody E) :
    ∃ D : ConvexSpaceBody E, volume D.carrier = (J : ENNReal)⁻¹ * volume K.carrier ∧
      (∀ i ∈ F, (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody <= K ->
        (T i).toConvexSpaceBody <= D) := by
  let D := K.affineImage L.symm.toAffineMap L.symm.toContinuousAffineEquiv.continuous
  refine ⟨D, affine_inverse_volume_w103 L hJ hvol K.carrier, ?_⟩
  intro i hi hiK x hx
  exact ⟨L x, hiK (himage i hi ⟨x, hx, rfl⟩), L.symm_apply_apply x⟩

end

end Kakeya.ml1Boot.TrialRestartW94
