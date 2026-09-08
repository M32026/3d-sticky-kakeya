module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI uP

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def trialEDPreparationCostW96 (n : Nat) (Ctw : NNReal) : Nat :=
  lineSelectionMultiplicityW95 n 1 (Nat.ceil (Ctw : Real)) *
    lineSelectionMultiplicityW95 n 2 (Nat.ceil (Ctw : Real))

def trialOneSidedUniformConstantW96 (n : Nat) : NNReal :=
  max 1 (Tube.overlapConstBOTight n : NNReal)

/-- G0: construct fine ED and then parent ED using the actual fine shaded
weights. The retained parent fibres belong to the same selected fine E0.
The one-sided SSF uniformity costs no further subfamily selection. -/
theorem exists_actual_fine_and_parent_ED_preparation_w96
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d rho : NNReal} (hd : 0 < d) (hdrho : d <= rho)
    (hdquarter : d <= 1 / 4) (hrho : rho <= 1)
    (F : Finset iota) (Y : iota -> ShadedTube d E)
    (J : Finset pi) (P : pi -> Tube rho E) (parent : iota -> pi)
    (Ctw : NNReal) (hCtw : 1 <= Ctw)
    (hF : F.Nonempty) (hmass : 0 < ∑ i ∈ F, volume (Y i).shade)
    (hfine_ball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (hparent_ball : ∀ S ∈ J, (P S).carrier ⊆ Metric.closedBall 0 2)
    (hfine_ed : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Ctw)
    (hparent_ed : lineEssentiallyDistinctW94 J P Ctw)
    (hparent_image : F.image parent ⊆ J)
    (hcontain : ∀ i ∈ F, (Y i).toConvexSpaceBody <= (P (parent i)).toConvexSpaceBody) :
    let Mfine := lineSelectionMultiplicityW95 (Module.finrank Real E) 1 (Nat.ceil (Ctw : Real))
    let Mpaid := trialEDPreparationCostW96 (Module.finrank Real E) Ctw
    ∃ (E0 E1 : Finset iota) (J1 : Finset pi),
      E0.Nonempty ∧ E0 ⊆ F ∧ E1.Nonempty ∧ E1 ⊆ E0 ∧
      J1.Nonempty ∧ J1 ⊆ E0.image parent ∧ E1 = E0.filter (fun i => parent i ∈ J1) ∧
      E1.image parent = J1 ∧
      (∀ S ∈ J1, completeFibreW94 E1 parent S = completeFibreW94 E0 parent S) ∧
      (E0 : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
      F.card <= Mfine * E0.card ∧
      (∑ i ∈ F, volume (Y i).shade) <= (Mfine : ENNReal) * ∑ i ∈ E0, volume (Y i).shade ∧
      (E1 : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
      (J1 : Set pi).Pairwise (fun S T => IsEssentiallyDistinct (P S).carrier (P T).carrier) ∧
      FlatPrismParentPresentation (D := 1) E1 Y J1 P parent ∧
      Nonempty (IsFlatPrismUniform E1 Y (Tube.ssfGridLen d)
        (trialOneSidedUniformConstantW96 (Module.finrank Real E))) ∧
      (∑ i ∈ F, volume (Y i).shade) <= (Mpaid : ENNReal) * ∑ i ∈ E1, volume (Y i).shade ∧
      fullness' F (fun i => (Y i).toShadedBody) <=
        (Mpaid : ENNReal) * fullness' E1 (fun i => (Y i).toShadedBody) ∧
      frostmanConstIn E1 (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
        (Mpaid : ENNReal) * (fullness' F (fun i => (Y i).toShadedBody))⁻¹ *
          frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
        (Mpaid : ENNReal) * ShadedBody.multiplicity E1 (fun i => (Y i).toShadedBody) := by
  classical
  let A := Nat.ceil (Ctw : Real)
  let Mf := lineSelectionMultiplicityW95 (Module.finrank Real E) 1 A
  let Mp := lineSelectionMultiplicityW95 (Module.finrank Real E) 2 A
  let M := Mf * Mp
  have hA : 1 <= A := (Nat.one_le_floor_iff _).mpr (by exact_mod_cast hCtw) |>.trans
    (Nat.floor_le_ceil (Ctw : Real))
  have hd1 : d <= 1 := hdquarter.trans (by
    rw [div_le_one (by norm_num : (0 : NNReal) < 4)]
    norm_num)
  have hrho0 : 0 < rho := hd.trans_le hdrho
  have hlineA : VeryNotSticky.IsLineEssDistinct A F (fun i => (Y i).toTube) := by
    intro o v hv
    exact ((pointwise_lineED_iff_library_floor_w95 F (fun i => (Y i).toTube) Ctw).mp
      hfine_ed o v hv).trans (Nat.floor_le_ceil (Ctw : Real))
  have hcenter : ∀ i ∈ F, ‖(Y i).center‖ <= (1 : Real) := by
    intro i hi
    have hmem := (Y i).toTube.mem_carrier_of_mem_segment
      (midpoint_mem_segment (𝕜 := Real) (Y i).x (Y i).y)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hfine_ball i hi hmem
  obtain ⟨E0, hE0F, hE0, hE0ED, hE0mass, hE0card, hE0full, hE0CF, hE0max, hE0mult⟩ :=
    exists_pairwise_lineED_paid_w95 hd hd1 F Y hF 1 (by norm_num) hcenter A hA
      hlineA ConvexSpaceBody.closedUnitBall hfine_ball hmass
  change (∑ i ∈ F, volume (Y i).shade) <=
    (Mf : ENNReal) * (∑ i ∈ E0, volume (Y i).shade) at hE0mass
  change F.card <= Mf * E0.card at hE0card
  let occupied := E0.image parent
  have hoccupied : occupied ⊆ J := (Finset.image_subset_image hE0F).trans hparent_image
  have hpcenter : ∀ S ∈ occupied, ‖(P S).center‖ <= (2 : Real) := by
    intro S hS
    have hmem := (P S).mem_carrier_of_mem_segment
      (midpoint_mem_segment (𝕜 := Real) (P S).x (P S).y)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hparent_ball S (hoccupied hS) hmem
  have hparentLineA : VeryNotSticky.IsLineEssDistinct A occupied P := by
    intro o v hv
    have hsub : (occupied.filter fun S => (P S).carrier ⊆ VeryNotSticky.lineNbhd o v
        (5 * (rho : Real))) ⊆ J.filter (fun S => (P S).carrier ⊆
          VeryNotSticky.lineNbhd o v (5 * (rho : Real))) :=
      Finset.filter_subset_filter _ hoccupied
    exact (Finset.card_le_card hsub).trans
      (((pointwise_lineED_iff_library_floor_w95 J P Ctw).mp hparent_ed o v hv).trans
        (Nat.floor_le_ceil (Ctw : Real)))
  have hparentBig := lineED_five_implies_lineEDAt_w95 hrho0 hrho occupied P A hparentLineA 2
    (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E)) (by norm_num)
    (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _).le hpcenter
  have hMul : ∀ R : Real, 0 <= R ->
      1 <= lineSelectionMultiplicityW95 (Module.finrank Real E) R A := by
    intro R hR
    apply Nat.mul_pos _ (by omega)
    apply Nat.ceil_pos.mpr
    have hK : 0 <= Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E) - 1 :=
      sub_nonneg.mpr (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _).le
    positivity
  have hMf : 1 <= Mf := hMul 1 (by norm_num)
  have hMp : 1 <= Mp := hMul 2 (by norm_num)
  have hM : 1 <= M := Nat.mul_pos (by omega) (by omega)
  let weight := fun S => ∑ i ∈ E0.filter (fun i => parent i = S), volume (Y i).shade
  obtain ⟨J1, hJ1, hJ1ED, hJ1mass, hJ1card⟩ :=
    VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hrho0 hrho hparentBig weight
  change (∑ S ∈ occupied, weight S) <=
    ((Mp - 1 + 1 : Nat) : ENNReal) * (∑ S ∈ J1, weight S) at hJ1mass
  rw [Nat.sub_add_cancel hMp] at hJ1mass
  have hmaps : ∀ i ∈ E0, parent i ∈ occupied := fun i hi => Finset.mem_image_of_mem _ hi
  have hmassFibres : (∑ S ∈ occupied, weight S) =
      ∑ i ∈ E0, volume (Y i).shade := Finset.sum_fiberwise_of_maps_to hmaps _
  let E1 := E0.filter (fun i => parent i ∈ J1)
  have hmassSelected : (∑ S ∈ J1, weight S) =
      ∑ i ∈ E1, volume (Y i).shade := Finset.sum_fiberwise_eq_sum_filter E0 J1 _ _
  rw [hmassFibres, hmassSelected] at hJ1mass
  have hE1sub : E1 ⊆ E0 := Finset.filter_subset _ _
  have hE1F : E1 ⊆ F := hE1sub.trans hE0F
  have htotal : (∑ i ∈ F, volume (Y i).shade) <=
      (M : ENNReal) * (∑ i ∈ E1, volume (Y i).shade) := by
    apply hE0mass.trans
    simpa only [M, Nat.cast_mul, mul_assoc] using mul_le_mul' le_rfl hJ1mass
  have hE1 : E1.Nonempty := by
    by_contra hn
    have hzero : E1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hbad : (∑ i ∈ F, volume (Y i).shade) <= 0 := by simpa [hzero] using htotal
    exact (not_lt_of_ge hbad) hmass
  have himage : E1.image parent = J1 := by
    apply Finset.Subset.antisymm
    · intro S hS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
      exact (Finset.mem_filter.mp hi).2
    · intro S hS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hJ1 hS)
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hi, hS⟩)
  have hE1ED : (E1 : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) :=
    hE0ED.mono (by exact_mod_cast hE1sub)
  have hfull : fullness' F (fun i => (Y i).toShadedBody) <=
      (M : ENNReal) * fullness' E1 (fun i => (Y i).toShadedBody) := by
    unfold fullness'
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div htotal (Finset.sum_le_sum_of_subset hE1F)
  have hCF : frostmanConstIn E1 (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      (M : ENNReal) * (fullness' F (fun i => (Y i).toShadedBody))⁻¹ *
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    obtain ⟨i0, hi0⟩ := hF
    let v := volume (Y i0).carrier
    have hv : 0 < v := (Tube.volume_pos_and_lt_top hd hd1 (Y i0).toTube).1
    have hvtop : v ≠ ⊤ := (Tube.volume_pos_and_lt_top hd hd1 (Y i0).toTube).2.ne
    have hvol : ∀ i ∈ F, volume (Y i).carrier = v :=
      fun i _ => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
    have hsumF : (∑ i ∈ F, volume (Y i).carrier) = (F.card : ENNReal) * v := by
      rw [Finset.sum_congr rfl hvol]
      simp
    have hsumE1 : (∑ i ∈ E1, volume (Y i).carrier) = (E1.card : ENNReal) * v := by
      rw [Finset.sum_congr rfl (fun i hi => hvol i (hE1F hi))]
      simp
    have hF0 : (F.card : ENNReal) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨i0, hi0⟩)
    have hsum0 : (F.card : ENNReal) * v ≠ 0 := mul_ne_zero hF0 hv.ne'
    have hsumTop : (F.card : ENNReal) * v ≠ ⊤ := ENNReal.mul_ne_top (by simp) hvtop
    let lam := fullness' F (fun i => (Y i).toShadedBody)
    have hlam : 0 < lam := by
      unfold lam fullness'
      rw [hsumF]
      exact ENNReal.div_pos hmass.ne' hsumTop
    have hbase : lam * ((F.card : ENNReal) * v) = ∑ i ∈ F, volume (Y i).shade := by
      dsimp [lam, fullness']
      rw [hsumF, ENNReal.div_mul_cancel hsum0 hsumTop]
    have hcard : lam * (F.card : ENNReal) <= (M : ENNReal) * E1.card := by
      apply (ENNReal.mul_le_mul_iff_left hv.ne' hvtop).mp
      calc
        _ = ∑ i ∈ F, volume (Y i).shade := by simpa only [mul_assoc] using hbase
        _ <= (M : ENNReal) * (∑ i ∈ E1, volume (Y i).shade) := htotal
        _ <= (M : ENNReal) * (∑ i ∈ E1, volume (Y i).carrier) := by
          gcongr with i hi
          exact (Y i).shade_subset
        _ = _ := by rw [hsumE1, mul_assoc]
    have hM0 : (M : ENNReal) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hMtop : (M : ENNReal) ≠ ⊤ := by simp
    have hretain : ((M : ENNReal)⁻¹ * lam) * (F.card : ENNReal) <= E1.card := by
      rw [mul_assoc]
      exact (ENNReal.inv_mul_le_iff hM0 hMtop).mpr hcard
    have hk0 : (M : ENNReal)⁻¹ * lam ≠ 0 :=
      mul_ne_zero (ENNReal.inv_ne_zero.mpr hMtop) hlam.ne'
    have hbound := frostmanConstIn_subfamily_le (K := ConvexSpaceBody.closedUnitBall)
      ⟨i0, hi0⟩ hvol hfine_ball hE1F hk0 hretain
    rwa [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hMtop))
      (Or.inl (ENNReal.inv_ne_top.mpr hM0)), inv_inv] at hbound
  refine ⟨E0, E1, J1, hE0, hE0F, hE1, hE1sub, ?_, hJ1, rfl, himage, ?_,
    hE0ED, hE0card, hE0mass, hE1ED, hJ1ED, ?_, ?_, htotal, hfull, hCF, ?_⟩
  · rw [← himage]
    exact hE1.image _
  · intro S hS
    ext i
    simp only [completeFibreW94, E1, Finset.mem_filter]
    constructor
    · exact fun hi => ⟨hi.1.1, hi.2⟩
    · intro hi
      exact ⟨⟨hi.1, hi.2 ▸ hS⟩, hi.2⟩
  · exact
      { one_le := le_rfl
        mapsTo := fun i hi => (Finset.mem_filter.mp hi).2
        le_parent_dilate := fun i hi => (hcontain i (hE1F hi)).trans
          (Tube.subset_dilate (P (parent i)) (le_refl (1 : Real)))
        pairwise := hJ1ED }
  · exact nonempty_isFlatPrismUniform_ssf hd hdquarter E1 Y
      (fun i hi => hfine_ball i (hE1F hi)) hE1ED (le_max_left _ _) (le_max_right _ _)
  · apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset F
      (fun i => (Y i).toShadedBody) E1 (fun i => (Y i).toShadedBody) M _ htotal
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hE1F hi, hxi⟩

/-- G3a: common actual fine containment, not intersection of the parents. -/
theorem carrier_in_line_neighborhood_of_common_fine_tube_w96
    {d r s : NNReal} (hd : 0 < d) (hdr : d <= r) (hds : d <= s)
    (T : Tube d E) (A : Tube r E) (B : Tube s E)
    (hTA : T.toConvexSpaceBody <= A.toConvexSpaceBody)
    (hTB : T.toConvexSpaceBody <= B.toConvexSpaceBody)
    (hTcenter : ‖T.center‖ <= 1) (hAcenter : ‖A.center‖ <= 2) :
    A.carrier ⊆ VeryNotSticky.lineNbhd B.center B.direction (16 * ((r : Real) + (s : Real))) := by
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
  have hcoreA : ∀ z ∈ segment Real T.x T.y,
      Tube.lineDist A.center A.direction z <= (r : Real) :=
    fun z hz => own_axis A (hTA (T.mem_carrier_of_mem_segment hz))
  have hcoreB : ∀ z ∈ segment Real T.x T.y,
      Tube.lineDist B.center B.direction z <= (s : Real) :=
    fun z hz => own_axis B (hTB (T.mem_carrier_of_mem_segment hz))
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
  have hTdir : ‖proj T.direction‖ <= 2 * (s : Real) := by
    have hid := Tube.perp_sub_perp B.center B.direction T.y T.x
    change proj (T.y - B.center) - proj (T.x - B.center) = proj T.direction at hid
    rw [← hid]
    calc
      _ <= ‖proj (T.y - B.center)‖ + ‖proj (T.x - B.center)‖ := norm_sub_le _ _
      _ <= (s : Real) + s := add_le_add (hcoreB T.y (right_mem_segment _ _ _))
        (hcoreB T.x (left_mem_segment _ _ _))
      _ = _ := by ring
  obtain ⟨sign, hsign, hdir⟩ := Tube.exists_sign_norm_direction_sub_le T A.norm_direction
    (hcoreA T.x (left_mem_segment _ _ _)) (hcoreA T.y (right_mem_segment _ _ _))
  have hsignAbs : |sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hAdir : ‖proj A.direction‖ <= 4 * ((r : Real) + (s : Real)) := by
    calc
      ‖proj A.direction‖ = ‖proj (sign • A.direction)‖ := by
        rw [proj_smul, norm_smul, Real.norm_eq_abs, hsignAbs, one_mul]
      _ <= ‖proj (sign • A.direction - T.direction)‖ + ‖proj T.direction‖ := by
        rw [proj_sub]
        exact norm_le_norm_sub_add _ _
      _ <= ‖sign • A.direction - T.direction‖ + 2 * (s : Real) :=
        add_le_add (proj_norm _) hTdir
      _ <= 4 * (r : Real) + 2 * (s : Real) := by
        rw [norm_sub_rev]
        exact add_le_add hdir le_rfl
      _ <= 4 * ((r : Real) + (s : Real)) := by nlinarith [s.coe_nonneg]
  let c := inner Real (T.center - A.center) A.direction
  let e := (T.center - A.center) - c • A.direction
  have he : ‖e‖ <= (r : Real) := hcoreA T.center (midpoint_mem_segment (𝕜 := Real) _ _)
  have hc : |c| <= 3 := by
    calc
      |c| <= ‖T.center - A.center‖ * ‖A.direction‖ := abs_real_inner_le_norm _ _
      _ = ‖T.center - A.center‖ := by rw [A.norm_direction, mul_one]
      _ <= ‖T.center‖ + ‖A.center‖ := norm_sub_le _ _
      _ <= 3 := by linarith
  have hTcenterB : ‖proj (T.center - B.center)‖ <= (s : Real) :=
    hcoreB T.center (midpoint_mem_segment (𝕜 := Real) _ _)
  have hcenterId : proj (A.center - B.center) =
      proj (T.center - B.center) - c • proj A.direction - proj e := by
    dsimp [proj, e, c]
    simp only [inner_sub_left, real_inner_smul_left]
    module
  have hcenter : ‖proj (A.center - B.center)‖ <= 13 * ((r : Real) + (s : Real)) := by
    rw [hcenterId]
    calc
      _ <= (‖proj (T.center - B.center)‖ + ‖c • proj A.direction‖) + ‖proj e‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = (‖proj (T.center - B.center)‖ + |c| * ‖proj A.direction‖) + ‖proj e‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= (s : Real) + 3 * (4 * ((r : Real) + (s : Real))) + r := by
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
  have hzBound : ‖proj (z - B.center)‖ <= 15 * ((r : Real) + (s : Real)) := by
    rw [hzId]
    calc
      _ <= ‖proj (A.center - B.center)‖ + ‖t • proj A.direction‖ := norm_add_le _ _
      _ = ‖proj (A.center - B.center)‖ + |t| * ‖proj A.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= 13 * ((r : Real) + (s : Real)) + (1 / 2 : Real) *
          (4 * ((r : Real) + (s : Real))) := by gcongr
      _ = _ := by ring
  rw [VeryNotSticky.lineNbhd_eq_cthickening_range]
  apply (Tube.mem_cthickening_line_iff B.norm_direction (by positivity)).mpr
  change ‖proj (x - B.center)‖ <= _
  have hxId : x - B.center = (x - z) + (z - B.center) := by abel
  rw [hxId, proj_add]
  calc
    _ <= ‖proj (x - z)‖ + ‖proj (z - B.center)‖ := norm_add_le _ _
    _ <= ‖x - z‖ + 15 * ((r : Real) + (s : Real)) := add_le_add (proj_norm _) hzBound
    _ <= (r : Real) + 15 * ((r : Real) + (s : Real)) := by
      apply add_le_add _ le_rfl
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hxz
    _ <= 16 * ((r : Real) + (s : Real)) := by nlinarith [s.coe_nonneg]

def commonFineMeetingParentsW96
    {iota : Type uI} {pi : Type uP} {d r s : NNReal}
    (H : Finset iota) (T : iota -> Tube d E)
    (J : Finset pi) (P : pi -> Tube r E) (R : Tube s E) : Finset pi :=
  J.filter (fun S => ∃ i ∈ H,
    (T i).toConvexSpaceBody <= (P S).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody <= R.toConvexSpaceBody)

def trialNearbyParentCountW96 (Ctw : NNReal) : Nat :=
  2 * Nat.ceil (Ctw : Real) * lineAmplificationBoundW95 3 2 32

/-- The explicit radius amplification has degree six in dimension three. -/
theorem lineAmplification_bound_scale_six_w96 (q : Real) (hq : 1 <= q) :
    (lineAmplificationBoundW95 3 2 (32 * q) : Real) <=
      2 * (lineAmplificationBoundW95 3 2 32 : Real) * q ^ (6 : Nat) := by
  have hq0 : 0 <= q := zero_le_one.trans hq
  let x : Real := 4 * (2 + 1) * (32 * q - 1) * (1 + 8 * 2) + 1
  let y : Real := 16 * (2 + 1) * (32 * q - 1) + 1
  have hx0 : 0 <= x := by dsimp [x]; nlinarith
  have hy0 : 0 <= y := by dsimp [y]; nlinarith
  have hx : x <= 6528 * q := by dsimp [x]; linarith
  have hy : y <= 1536 * q := by dsimp [y]; linarith
  have hconst : 2 * (6528 : Real) ^ 3 * 1536 ^ 3 + 1 <=
      2 * (lineAmplificationBoundW95 3 2 32 : Real) := by
    norm_num [lineAmplificationBoundW95]
  change (Nat.ceil (2 * x ^ 3 * y ^ 3) : Real) <= _
  apply (Nat.ceil_lt_add_one (show 0 <= 2 * x ^ 3 * y ^ 3 by positivity)).le.trans
  calc
    2 * x ^ 3 * y ^ 3 + 1 <= 2 * (6528 * q) ^ 3 * (1536 * q) ^ 3 + 1 := by
      gcongr
    _ = (2 * (6528 : Real) ^ 3 * 1536 ^ 3) * q ^ 6 + 1 := by ring
    _ <= (2 * (6528 : Real) ^ 3 * 1536 ^ 3 + 1) * q ^ 6 := by
      nlinarith [show 1 <= q ^ (6 : Nat) from one_le_pow₀ hq]
    _ <= 2 * (lineAmplificationBoundW95 3 2 32 : Real) * q ^ 6 :=
      mul_le_mul_of_nonneg_right hconst (by positivity)

/-- G3b: arbitrary exact test tubes are allowed; every counted parent has
an actual common B1 fine tube with the test. Only the parents are in B2. -/
theorem card_assigned_parents_meeting_exact_cell_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} {d r s : NNReal}
    (hd : 0 < d) (hdr : d <= r) (hds : d <= s) (hr : r <= 1)
    (H : Finset iota) (T : iota -> Tube d E)
    (J : Finset pi) (P : pi -> Tube r E) (R : Tube s E)
    (Ctw : NNReal) (hCtw : 1 <= Ctw)
    (hfine_ball : ∀ i ∈ H, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent_ball : ∀ S ∈ J, (P S).carrier ⊆ Metric.closedBall 0 2)
    (hline : lineEssentiallyDistinctW94 J P Ctw) :
    ((commonFineMeetingParentsW96 H T J P R).card : Real) <=
      (trialNearbyParentCountW96 Ctw : Real) *
        (max 1 ((s : Real) / (r : Real))) ^ (6 : Nat) := by
  classical
  let q : Real := max 1 ((s : Real) / (r : Real))
  let A := Nat.ceil (Ctw : Real)
  have hq : 1 <= q := le_max_left _ _
  have hr0 : (0 : Real) < r := by exact_mod_cast hd.trans_le hdr
  have hsr : (s : Real) <= q * r :=
    (div_le_iff₀ hr0).mp (le_max_right _ _)
  have hrr : (r : Real) <= q * r := by nlinarith
  have hscale : 16 * ((r : Real) + (s : Real)) <= (32 * q) * r := by linarith
  have hlineA : VeryNotSticky.IsLineEssDistinct A J P := by
    intro o v hv
    exact ((pointwise_lineED_iff_library_floor_w95 J P Ctw).mp hline o v hv).trans
      (Nat.floor_le_ceil (Ctw : Real))
  have hPcenter : ∀ S ∈ J, ‖(P S).center‖ <= (2 : Real) := by
    intro S hS
    have hmem := (P S).mem_carrier_of_mem_segment
      (midpoint_mem_segment (𝕜 := Real) (P S).x (P S).y)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hparent_ball S hS hmem
  have hlineBig := lineED_five_implies_lineEDAt_w95 (hd.trans_le hdr) hr J P A hlineA 2
    (32 * q) (by norm_num) (by linarith) hPcenter
  rw [hdim] at hlineBig
  have hsub : commonFineMeetingParentsW96 H T J P R ⊆
      J.filter (fun S => (P S).carrier ⊆ VeryNotSticky.lineNbhd R.center R.direction
        ((32 * q) * (r : Real))) := by
    intro S hS
    obtain ⟨hSJ, i, hi, hiP, hiR⟩ := Finset.mem_filter.mp hS
    have hTcenter : ‖(T i).center‖ <= (1 : Real) := by
      have hmem := (T i).mem_carrier_of_mem_segment
        (midpoint_mem_segment (𝕜 := Real) (T i).x (T i).y)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hfine_ball i hi hmem
    have hcontain := carrier_in_line_neighborhood_of_common_fine_tube_w96
      hd hdr hds (T i) (P S) R hiP hiR hTcenter (hPcenter S hSJ)
    refine Finset.mem_filter.mpr ⟨hSJ, ?_⟩
    intro x hx
    have hsmall := hcontain hx
    rw [VeryNotSticky.lineNbhd_eq_cthickening_range] at hsmall ⊢
    exact Metric.cthickening_mono hscale _ hsmall
  have hcount : (commonFineMeetingParentsW96 H T J P R).card <=
      lineAmplificationBoundW95 3 2 (32 * q) * A :=
    (Finset.card_le_card hsub).trans (hlineBig R.center R.direction R.norm_direction)
  calc
    ((commonFineMeetingParentsW96 H T J P R).card : Real) <=
        (lineAmplificationBoundW95 3 2 (32 * q) : Real) * A := by exact_mod_cast hcount
    _ <= (2 * (lineAmplificationBoundW95 3 2 32 : Real) * q ^ 6) * A :=
      mul_le_mul_of_nonneg_right (lineAmplification_bound_scale_six_w96 q hq) (by positivity)
    _ = (trialNearbyParentCountW96 Ctw : Real) * q ^ 6 := by
      dsimp only [trialNearbyParentCountW96, A]
      push_cast
      ring

end

end Kakeya.ml1Boot.TrialRestartW94
