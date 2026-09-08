module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationGeometryW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.ConvexBody.Counting

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem axisFoot_line_pullback_w103 {r theta R : NNReal} (hr : 0 < r)
    (hrt : r <= theta) (ht1 : theta <= 1) (hR : 0 < R)
    (top : Tube theta E) (T : Tube r E) (hT : T.toConvexSpaceBody <= top.toConvexSpaceBody)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real))
    (K : Real) (hK : 0 <= K) (x : E)
    (hx : ∃ t : Real, dist (L x) ((axisFootTubeW103 (r / theta) L T).center +
      t • (axisFootTubeW103 (r / theta) L T).direction) <= K * ((r / theta : NNReal) : Real)) :
    x ∈ VeryNotSticky.lineNbhd T.center T.direction ((12 * (R : Real) * K) * r) := by
  let W := axisFootTubeW103 (r / theta) L T
  let v := L.linear T.direction
  let u := W.direction
  have hv : ‖v‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro h
    have hz : T.direction = 0 := L.linear.injective (h.trans (map_zero L.linear).symm)
    have := T.norm_direction
    rw [hz, norm_zero] at this
    norm_num at this
  obtain ⟨t, hdist⟩ := hx
  let a : Real := inner Real (L T.center) u
  let b : Real := (t - a) / ‖v‖
  let z : E := T.center + b • T.direction
  have hLz : L z = W.center + t • u := by
    rw [show W.center = L T.center - a • u from axisFootTube_center_w103 L T]
    have hz : L z = L T.center + b • v := by
      dsimp only [z, v]
      rw [add_comm T.center, show L (b • T.direction + T.center) =
        L.linear (b • T.direction) + L T.center from L.map_vadd T.center (b • T.direction),
        map_smul, add_comm]
    rw [hz, show u = ‖v‖⁻¹ • v from axisFootTube_direction_w103 L T]
    dsimp [b]
    module
  have huv : top.rescaleMap (R : Real) (z + (x - z)) =
      top.rescaleMap (R : Real) z + (L x - L z) := by
    have hxeq : L x = top.rescaleMap (R : Real) x := congrArg (fun f : E →ᵃ[Real] E => f x) hL
    have hzeq : L z = top.rescaleMap (R : Real) z := congrArg (fun f : E →ᵃ[Real] E => f z) hL
    rw [add_sub_cancel, hxeq, hzeq]
    abel
  have hnear : ‖L x - L z‖ <= K * ((r / theta : NNReal) : Real) := by
    rw [hLz, ← dist_eq_norm]
    exact hdist
  have hperp : ‖T.direction - inner Real top.direction T.direction • top.direction‖ <=
      2 * (theta : Real) := Tube.perp_norm_direction_le_of_subset top T hT
  have hbound := (Tube.norm_rescale_symm_vector_le (hr.trans_le hrt) ht1
    (show (0 : Real) < R from hR) top T (by norm_num : (0 : Real) <= 2)
    (by positivity : (0 : Real) <= K * ((r / theta : NNReal) : Real)) hperp huv hnear).2
  apply VeryNotSticky.mem_lineNbhd_of_dist_le (b + inner Real T.direction (x - z))
  have heq : x - (T.center + (b + inner Real T.direction (x - z)) • T.direction) =
      (x - z) - inner Real T.direction (x - z) • T.direction := by
    dsimp [z]
    module
  rw [dist_eq_norm, heq]
  convert hbound using 1
  rw [NNReal.coe_div]
  have htne : (theta : Real) ≠ 0 := (show (0 : Real) < theta from hr.trans_le hrt).ne'
  field_simp [htne]
  ring

theorem line_aperture_card_w103 {iota : Type uI} {r : NNReal} (hr : 0 < r) (hr1 : r <= 1)
    (F : Finset iota) (T : iota -> Tube r E) (C : NNReal)
    (hline : lineEssentiallyDistinctW94 F T C)
    (B K : Real) (hB : 0 <= B) (hK : 1 <= K)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= B) (o v : E) (hv : ‖v‖ = 1) :
    ((nearLineFamilyW95 F T o v K).card : NNReal) <=
      (lineAmplificationBoundW95 (Module.finrank Real E) B K : NNReal) * C := by
  obtain ⟨G, assign, hG, hGcard, hassign, hcover⟩ :=
    exists_radius_five_line_bins_w95 hr hr1 F T B K hB hK hcenter o v hv
  let fibres := fun k => F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T k).center (T k).direction)
  have hfibres : ∀ k, ((fibres k).card : NNReal) <= C := fun k =>
    hline (T k).center (T k).direction (T k).norm_direction
  have hcovered : nearLineFamilyW95 F T o v K ⊆ G.biUnion fibres := by
    intro i hi
    refine Finset.mem_biUnion.mpr ⟨assign i, hassign i hi, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, ?_⟩⟩
    exact (pointwise_line_neighbourhood_iff_w95 (T i) (T (assign i)).center
      (T (assign i)).direction (T (assign i)).norm_direction).mpr (hcover i hi)
  calc
    ((nearLineFamilyW95 F T o v K).card : NNReal) <= ((G.biUnion fibres).card : NNReal) := by
      exact_mod_cast Finset.card_le_card hcovered
    _ <= ∑ k ∈ G, ((fibres k).card : NNReal) := by exact_mod_cast Finset.card_biUnion_le
    _ <= ∑ _k ∈ G, C := Finset.sum_le_sum (fun k hk => hfibres k)
    _ = (G.card : NNReal) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (lineAmplificationBoundW95 (Module.finrank Real E) B K : NNReal) * C := by
      apply mul_le_mul_right'
      exact_mod_cast hGcard

theorem axisFoot_family_lineED_w103 {iota : Type uI} {r theta R : NNReal}
    (hr : 0 < r) (hrt : r <= theta) (ht1 : theta <= 1) (hR : 1 <= R)
    (hRn : Tube.normalization.C (Module.finrank Real E) <= R)
    (top : Tube theta E) (F : Finset iota) (T : iota -> Tube r E)
    (hT : ∀ i ∈ F, (T i).toConvexSpaceBody <= top.toConvexSpaceBody)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= 2)
    (C : NNReal) (hline : lineEssentiallyDistinctW94 F T C)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real)) :
    lineEssentiallyDistinctW94 F (fun i => axisFootTubeW103 (r / theta) L (T i))
      ((lineAmplificationBoundW95 (Module.finrank Real E) 1 5 : NNReal) *
        (lineAmplificationBoundW95 (Module.finrank Real E) 2 (60 * (R : Real)) : NNReal) * C) := by
  let W := fun i => axisFootTubeW103 (r / theta) L (T i)
  let Cold : NNReal := (lineAmplificationBoundW95 (Module.finrank Real E) 2 (60 * (R : Real)) : NNReal) * C
  have hd : 0 < r / theta := div_pos hr (hr.trans_le hrt)
  have hd1 : r / theta <= 1 := (div_le_one (hr.trans_le hrt)).mpr hrt
  have hWcenter : ∀ i ∈ F, ‖(W i).center‖ <= 1 := by
    intro i hi
    exact (axisFootTube_image_w103 hr hrt ht1 hR hRn top (T i) (hT i hi) L hL).2.trans (by norm_num)
  intro o v hv
  let H := F.filter (fun i => liesInFiveDeltaLineTubeW94 (W i) o v)
  have hHnear : H = nearLineFamilyW95 F W o v 5 := by
    apply Finset.filter_congr
    intro i hi
    exact pointwise_line_neighbourhood_iff_w95 (W i) o v hv
  obtain ⟨G, assign, hG, hGcard, hassign, hcover⟩ :=
    exists_radius_five_line_bins_w95 hd hd1 F W 1 5 (by norm_num) (by norm_num) hWcenter o v hv
  let fibres := fun j => nearLineFamilyW95 F T (T j).center (T j).direction (60 * (R : Real))
  have hK : (1 : Real) <= 60 * R := by have hh : (1 : Real) <= R := hR; nlinarith
  have hfibres : ∀ j, ((fibres j).card : NNReal) <= Cold := fun j =>
    line_aperture_card_w103 hr (hrt.trans ht1) F T C hline 2 (60 * (R : Real))
      (by norm_num) hK hcenter (T j).center (T j).direction (T j).norm_direction
  have hcovered : H ⊆ G.biUnion fibres := by
    intro i hi
    have hni : i ∈ nearLineFamilyW95 F W o v 5 := hHnear ▸ hi
    have hiF : i ∈ F := (Finset.mem_filter.mp hi).1
    let j := assign i
    have hjG : j ∈ G := hassign i hni
    have hjF : j ∈ F := (Finset.mem_filter.mp (hG hjG)).1
    refine Finset.mem_biUnion.mpr ⟨j, hjG, Finset.mem_filter.mpr ⟨hiF, ?_⟩⟩
    intro x hx
    have hWi := (axisFootTube_image_w103 hr hrt ht1 hR hRn top (T i) (hT i hiF) L hL).1
      ⟨x, hx, rfl⟩
    have hlineij := (pointwise_line_neighbourhood_iff_w95 (W i) (W j).center (W j).direction
      (W j).norm_direction).mpr (hcover i hni)
    have hh := axisFoot_line_pullback_w103 hr hrt ht1 (zero_lt_one.trans_le hR)
      top (T j) (hT j hjF) L hL 5 (by norm_num) x (hlineij (L x) hWi)
    convert hh using 1 <;> ring
  calc
    (H.card : NNReal) <= ((G.biUnion fibres).card : NNReal) := by exact_mod_cast Finset.card_le_card hcovered
    _ <= ∑ j ∈ G, ((fibres j).card : NNReal) := by exact_mod_cast Finset.card_biUnion_le
    _ <= ∑ _j ∈ G, Cold := Finset.sum_le_sum (fun j hj => hfibres j)
    _ = (G.card : NNReal) * Cold := by rw [Finset.sum_const, nsmul_eq_mul]
    _ <= (lineAmplificationBoundW95 (Module.finrank Real E) 1 5 : NNReal) * Cold := by
      apply mul_le_mul_right'
      exact_mod_cast hGcard
    _ = _ := by dsimp [Cold]; ring

end

end Kakeya.ml1Boot.TrialRestartW94
