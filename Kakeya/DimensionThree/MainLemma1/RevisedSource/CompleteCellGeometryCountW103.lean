module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceQuotientGridW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationCountingW103
public import Kakeya.DimensionThree.IsometryTransport

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

open RevisedLiteralProfileInterfaceFormalizerW87

theorem exists_complete_cell_geometry_count_w103
    (hdim : Module.finrank Real E = 3)
    (Ctw Cext : NNReal) (hCtw : 1 <= Ctw) (hCext : 1 <= Cext) :
    ∃ Cnear Cden : NNReal, 1 <= Cnear ∧ 1 <= Cden ∧
      ∀ {iota : Type uI} [DecidableEq iota] {d rho : NNReal},
        0 < d -> d <= rho -> rho <= 1 ->
      ∀ (F J : Finset iota) (T : iota -> Tube d E)
        (P : iota -> Tube rho E) (assign : iota -> iota),
        F.image assign = J ->
        (∀ i ∈ F, (T i).toConvexSpaceBody <= (P (assign i)).toConvexSpaceBody) ->
        (∀ i ∈ F, ‖(T i).center‖ <= 1) ->
        (∀ j ∈ J, ‖(P j).center‖ <= 2) ->
        lineEssentiallyDistinctW94 J P Ctw ->
        (∀ j ∈ J, ∀ k ∈ J,
          ((completeFibreW94 F assign k).card : NNReal) <=
            2 * ((completeFibreW94 F assign j).card : NNReal)) ->
        (∀ j ∈ J, ∃ nearby : Finset iota, nearby ⊆ J ∧
          (nearby.card : NNReal) <= Cnear ∧
          exactTubeCellW87 F T (P j) ⊆ nearby.biUnion (completeFibreW94 F assign)) ∧
        (∀ j ∈ J, ∀ D : ConvexSpaceBody E,
          (P j).toConvexSpaceBody <= D ->
          volume D.carrier <= (Cext : ENNReal) * volume (P j).carrier ->
          ((familyIn F (fun i => (T i).toConvexSpaceBody) D).card : NNReal) <=
            Cden * ((completeFibreW94 F assign j).card : NNReal)) := by
  have hmid : ∀ {w : NNReal} (U : Tube w E), U.midpoint = U.center := by
    intro w U
    simp only [Tube.center, midpoint_eq_smul_add, Tube.midpoint]
    norm_num
  have own_axis : ∀ {w : NNReal} (U : Tube w E) {z : E}, z ∈ U.carrier ->
      Tube.lineDist U.center U.direction z <= (w : Real) := by
    intro w U z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (U.carrier_eq ▸ hz)
    obtain ⟨t, ht, hxt⟩ := U.exists_param_of_mem_segment hx
    rw [hmid] at hxt
    apply (Tube.lineDist_le_norm_sub U.center U.direction z U.norm_direction t).trans
    rw [← hxt, ← dist_eq_norm]
    exact Metric.mem_closedBall.mp hzx

  -- Projection argument extracted from the common-fine containment donor.
  have hparentNear {d rho : NNReal} (T : Tube d E) (A B : Tube rho E)
      (hTA : T.toConvexSpaceBody <= A.toConvexSpaceBody)
      (hTcenter : ‖T.center‖ <= 1) (hAcenter : ‖A.center‖ <= 2)
      (s : Real) (hs : 0 <= s)
      (hcoreB : ∀ z ∈ segment Real T.x T.y, Tube.lineDist B.center B.direction z <= s) :
      A.carrier ⊆ VeryNotSticky.lineNbhd B.center B.direction (16 * ((rho : Real) + s)) := by
    have hcoreA : ∀ z ∈ segment Real T.x T.y,
        Tube.lineDist A.center A.direction z <= (rho : Real) :=
      fun z hz => own_axis A (hTA (T.mem_carrier_of_mem_segment hz))
    let proj := fun x : E => x - inner Real x B.direction • B.direction
    have proj_sub : ∀ x y : E, proj (x - y) = proj x - proj y := by
      intro x y
      dsimp [proj]
      rw [inner_sub_left]
      module
    have proj_add : ∀ x y : E, proj (x + y) = proj x + proj y := by
      intro x y
      dsimp [proj]
      rw [inner_add_left]
      module
    have proj_smul : ∀ (a : Real) (x : E), proj (a • x) = a • proj x := by
      intro a x
      dsimp [proj]
      rw [real_inner_smul_left]
      module
    have proj_norm : ∀ x : E, ‖proj x‖ <= ‖x‖ := by
      intro x
      simpa only [Tube.lineDist, sub_zero, zero_smul, add_zero] using
        Tube.lineDist_le_norm_sub 0 B.direction x B.norm_direction 0
    have hTdir : ‖proj T.direction‖ <= 2 * s := by
      have hid := Tube.perp_sub_perp B.center B.direction T.y T.x
      change proj (T.y - B.center) - proj (T.x - B.center) = proj T.direction at hid
      rw [← hid]
      calc
        _ <= ‖proj (T.y - B.center)‖ + ‖proj (T.x - B.center)‖ := norm_sub_le _ _
        _ <= s + s := add_le_add (hcoreB T.y (right_mem_segment _ _ _))
          (hcoreB T.x (left_mem_segment _ _ _))
        _ = _ := by ring
    obtain ⟨sign, hsign, hdir⟩ := Tube.exists_sign_norm_direction_sub_le T A.norm_direction
      (hcoreA T.x (left_mem_segment _ _ _)) (hcoreA T.y (right_mem_segment _ _ _))
    have hsignAbs : |sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
    have hAdir : ‖proj A.direction‖ <= 4 * ((rho : Real) + s) := by
      calc
        ‖proj A.direction‖ = ‖proj (sign • A.direction)‖ := by
          rw [proj_smul, norm_smul, Real.norm_eq_abs, hsignAbs, one_mul]
        _ <= ‖proj (sign • A.direction - T.direction)‖ + ‖proj T.direction‖ := by
          rw [proj_sub]
          exact norm_le_norm_sub_add _ _
        _ <= ‖sign • A.direction - T.direction‖ + 2 * s :=
          add_le_add (proj_norm _) hTdir
        _ <= 4 * (rho : Real) + 2 * s := by
          rw [norm_sub_rev]
          exact add_le_add hdir le_rfl
        _ <= 4 * ((rho : Real) + s) := by nlinarith [hs]
    let c := inner Real (T.center - A.center) A.direction
    let e := (T.center - A.center) - c • A.direction
    have he : ‖e‖ <= (rho : Real) := hcoreA T.center (midpoint_mem_segment (𝕜 := Real) _ _)
    have hc : |c| <= 3 := by
      calc
        |c| <= ‖T.center - A.center‖ * ‖A.direction‖ := abs_real_inner_le_norm _ _
        _ = ‖T.center - A.center‖ := by rw [A.norm_direction, mul_one]
        _ <= ‖T.center‖ + ‖A.center‖ := norm_sub_le _ _
        _ <= 3 := by linarith
    have hTcenterB : ‖proj (T.center - B.center)‖ <= s :=
      hcoreB T.center (midpoint_mem_segment (𝕜 := Real) _ _)
    have hcenterId : proj (A.center - B.center) =
        proj (T.center - B.center) - c • proj A.direction - proj e := by
      dsimp [proj, e, c]
      simp only [inner_sub_left, real_inner_smul_left]
      module
    have hcenter : ‖proj (A.center - B.center)‖ <= 13 * ((rho : Real) + s) := by
      rw [hcenterId]
      calc
        _ <= (‖proj (T.center - B.center)‖ + ‖c • proj A.direction‖) + ‖proj e‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ = (‖proj (T.center - B.center)‖ + |c| * ‖proj A.direction‖) + ‖proj e‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ <= s + 3 * (4 * ((rho : Real) + s)) + rho := by
          gcongr
          exact (proj_norm e).trans he
        _ = _ := by ring
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (A.carrier_eq ▸ hx)
    obtain ⟨t, ht, hzt⟩ := A.exists_param_of_mem_segment hz
    rw [hmid] at hzt
    have hzId : proj (z - B.center) = proj (A.center - B.center) + t • proj A.direction := by
      rw [hzt]
      have heq : A.center + t • A.direction - B.center =
          (A.center - B.center) + t • A.direction := by abel
      rw [heq, proj_add, proj_smul]
    have hzBound : ‖proj (z - B.center)‖ <= 15 * ((rho : Real) + s) := by
      rw [hzId]
      calc
        _ <= ‖proj (A.center - B.center)‖ + ‖t • proj A.direction‖ := norm_add_le _ _
        _ = ‖proj (A.center - B.center)‖ + |t| * ‖proj A.direction‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ <= 13 * ((rho : Real) + s) + (1 / 2 : Real) *
            (4 * ((rho : Real) + s)) := by gcongr
        _ = _ := by ring
    rw [VeryNotSticky.lineNbhd_eq_cthickening_range]
    apply (Tube.mem_cthickening_line_iff B.norm_direction (by positivity)).mpr
    change ‖proj (x - B.center)‖ <= _
    have hxId : x - B.center = (x - z) + (z - B.center) := by abel
    rw [hxId, proj_add]
    calc
      _ <= ‖proj (x - z)‖ + ‖proj (z - B.center)‖ := norm_add_le _ _
      _ <= ‖x - z‖ + 15 * ((rho : Real) + s) := add_le_add (proj_norm _) hzBound
      _ <= (rho : Real) + 15 * ((rho : Real) + s) := by
        apply add_le_add _ le_rfl
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hxz
      _ <= 16 * ((rho : Real) + s) := by nlinarith [hs]
  have hCextR : (0 : Real) < Cext := by
    exact_mod_cast zero_lt_one.trans_le hCext
  have htheta : (0 : Real) < (Cext : Real)⁻¹ := inv_pos.mpr hCextR
  have htheta1 : (Cext : Real)⁻¹ <= 1 := by
    have hmul := mul_inv_cancel₀ hCextR.ne'
    have hCext1 : (1 : Real) <= Cext := hCext
    nlinarith [htheta]
  obtain ⟨C, hC, hdilate⟩ := Kakeya.exists_essOverlapDilate_constant 3 htheta htheta1
  have hC0 : 0 <= C := zero_le_one.trans hC
  let K : Real := 16 * (1 + 2 * C)
  have hK : 1 <= K := by dsimp [K]; linarith
  let Cnear : NNReal := max 1 ((lineAmplificationBoundW95 3 2 K : NNReal) * Ctw)
  have hCnear : 1 <= Cnear := le_max_left _ _
  refine ⟨Cnear, 2 * Cnear, hCnear, ?_, ?_⟩
  · nlinarith
  intro iota inst d rho hd hdr hr1 F J T P assign hsurj hassign hTcenter hPcenter hline hfibres
  have hr : 0 < rho := hd.trans_le hdr
  have hrR : (0 : Real) < rho := by exact_mod_cast hr
  let f := Kakeya.dimThreeLinearIsometryEquiv E hdim
  have hDline (B : Tube rho E) (D : ConvexSpaceBody E)
      (hBD : B.toConvexSpaceBody <= D)
      (hvol : volume D.carrier <= (Cext : ENNReal) * volume B.carrier) :
      ∀ x ∈ D.carrier, Tube.lineDist B.center B.direction x <= 2 * C * (rho : Real) := by
    let M := B.toConvexSpaceBody.mapLinearIsometryEquiv f
    let Q := D.mapLinearIsometryEquiv f
    have hMvol : volume M.carrier = volume B.carrier :=
      Kakeya.volume_image_linearIsometryEquiv f B.carrier
    have hQvol : volume Q.carrier = volume D.carrier :=
      Kakeya.volume_image_linearIsometryEquiv f D.carrier
    have hBvol : 0 < volume B.carrier := by
      apply lt_of_lt_of_le _ B.le_volume
      have hcpos := ENNReal.coe_pos.mpr (Tube.le_volume.c_pos (Module.finrank Real E))
      have hrpos := ENNReal.coe_pos.mpr hr
      positivity
    obtain ⟨z, hzM, hz⟩ := hdilate M (by rwa [hMvol])
    have hMQ : M.carrier ⊆ Q.carrier := Set.image_mono hBD
    have hvolratio : ENNReal.ofReal (Cext : Real)⁻¹ * volume Q.carrier <= volume M.carrier := by
      rw [hQvol, hMvol, ENNReal.ofReal_inv_of_pos hCextR, ENNReal.ofReal_coe_nnreal]
      calc
        _ <= (Cext : ENNReal)⁻¹ * ((Cext : ENNReal) * volume B.carrier) :=
          mul_le_mul_left' hvol _
        _ = _ := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel
            (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCext)).ne' ENNReal.coe_ne_top, one_mul]
    obtain ⟨z0, hz0, rfl⟩ := hzM
    intro x hx
    obtain ⟨y, hyM, hy⟩ := hz Q hMQ hvolratio (Set.mem_image_of_mem f hx)
    obtain ⟨y0, hy0, rfl⟩ := hyM
    have hxy : x = z0 + C • (y0 - z0) := by
      apply f.injective
      calc
        f x = AffineMap.homothety (f z0) C (f y0) := hy.symm
        _ = f (z0 + C • (y0 - z0)) := by
          simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
            map_add, map_smul, map_sub]
          abel
    let proj := fun w : E => w - inner Real w B.direction • B.direction
    have hperp : proj (x - B.center) =
        (1 - C) • proj (z0 - B.center) + C • proj (y0 - B.center) := by
      rw [hxy]
      dsimp [proj]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
      module
    have hzbound : ‖proj (z0 - B.center)‖ <= (rho : Real) := own_axis B hz0
    have hybound : ‖proj (y0 - B.center)‖ <= (rho : Real) := own_axis B hy0
    change ‖proj (x - B.center)‖ <= _
    rw [hperp]
    calc
      _ <= ‖(1 - C) • proj (z0 - B.center)‖ + ‖C • proj (y0 - B.center)‖ := norm_add_le _ _
      _ = (C - 1) * ‖proj (z0 - B.center)‖ + C * ‖proj (y0 - B.center)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonpos (by linarith : 1 - C <= 0), abs_of_nonneg hC0]
        ring
      _ <= (C - 1) * (rho : Real) + C * (rho : Real) := by gcongr
      _ <= 2 * C * (rho : Real) := by nlinarith [rho.coe_nonneg]
  let nearby := fun j => nearLineFamilyW95 J P (P j).center (P j).direction K
  have hnearbySub (j : iota) : nearby j ⊆ J := Finset.filter_subset _ _
  have hnearbyCard (j : iota) : ((nearby j).card : NNReal) <= Cnear := by
    have h := line_aperture_card_w103 hr hr1 J P Ctw hline 2 K
      (by norm_num) hK hPcenter (P j).center (P j).direction (P j).norm_direction
    calc
      _ <= (lineAmplificationBoundW95 3 2 K : NNReal) * Ctw := by
        simpa only [hdim] using h
      _ <= Cnear := le_max_right _ _
  have hcover (j : iota) (D : ConvexSpaceBody E)
      (hPD : (P j).toConvexSpaceBody <= D)
      (hDvol : volume D.carrier <= (Cext : ENNReal) * volume (P j).carrier) :
      familyIn F (fun i => (T i).toConvexSpaceBody) D ⊆
        (nearby j).biUnion (completeFibreW94 F assign) := by
    intro i hi
    obtain ⟨hiF, hiD⟩ := Finset.mem_filter.mp hi
    have hparentJ : assign i ∈ J := hsurj ▸ Finset.mem_image.mpr ⟨i, hiF, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨assign i, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hparentJ, ?_⟩
      have hparent := hparentNear (T i) (P (assign i)) (P j) (hassign i hiF)
        (hTcenter i hiF) (hPcenter _ hparentJ) (2 * C * (rho : Real))
        (by positivity) (fun z hz => hDline (P j) D hPD hDvol z
          (hiD ((T i).mem_carrier_of_mem_segment hz)))
      have heq : 16 * ((rho : Real) + 2 * C * (rho : Real)) = K * (rho : Real) := by
        dsimp [K]
        ring
      rw [heq] at hparent
      exact hparent
    · exact Finset.mem_filter.mpr ⟨hiF, rfl⟩
  constructor
  · intro j hj
    refine ⟨nearby j, hnearbySub j, hnearbyCard j, ?_⟩
    have hvol : volume (P j).carrier <= (Cext : ENNReal) * volume (P j).carrier := by
      simpa only [one_mul] using mul_le_mul_right' (show (1 : ENNReal) <= Cext by exact_mod_cast hCext)
        (volume (P j).carrier)
    exact hcover j (P j).toConvexSpaceBody le_rfl hvol
  · intro j hj D hPD hDvol
    calc
      ((familyIn F (fun i => (T i).toConvexSpaceBody) D).card : NNReal) <=
          (((nearby j).biUnion (completeFibreW94 F assign)).card : NNReal) := by
        exact_mod_cast Finset.card_le_card (hcover j D hPD hDvol)
      _ <= ∑ k ∈ nearby j, ((completeFibreW94 F assign k).card : NNReal) := by
        exact_mod_cast Finset.card_biUnion_le
      _ <= ∑ _k ∈ nearby j, 2 * ((completeFibreW94 F assign j).card : NNReal) :=
        Finset.sum_le_sum (fun k hk => hfibres j hj k (hnearbySub j hk))
      _ = ((nearby j).card : NNReal) * (2 * ((completeFibreW94 F assign j).card : NNReal)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= Cnear * (2 * ((completeFibreW94 F assign j).card : NNReal)) :=
        mul_le_mul_right' (hnearbyCard j) _
      _ = _ := by ring

end

end Kakeya.ml1Boot.TrialRestartW94
