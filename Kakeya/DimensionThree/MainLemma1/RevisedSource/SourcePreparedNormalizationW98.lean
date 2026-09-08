module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.PreparedAxisFootCoreW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootQuotientGeometryW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CompleteCellGeometryCountW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.NormalizationActualFibresW103

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- Corrected INTERNAL C4 constructor. Its old-data margin is constructed
by the preceding raw/prepared/P2 theorems. Every original output field is kept. -/
theorem exists_prepared_centred_unit_normalization_w98
    (hdim : Module.finrank Real E = 3) (M : Nat) (hM : 1 <= M)
    (Ctw Ccell : NNReal) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell) :
    ∃ Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal,
      1 <= Rnorm ∧ 1 <= Cext ∧ 1 <= Cnorm ∧ 1 <= CtwNorm ∧ 1 <= CcellNorm ∧
      Ctw <= CtwNorm ∧ Ccell <= CcellNorm ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < 1 ->
        16 * Tube.gridScale delta (M * M) 1 <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty -> VisibleExtendedRestrictionW97 U Uext ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
        ActualTreeParameterMarginW98 Uext.cover normalizationParameterMarginW98 ->
      ∀ (a b : Nat), a < b -> b <= M ->
      ∀ (R : iota), R ∈ U.cover.indexSet a ->
      ∀ Z : iota -> ShadedTube (Tube.gridScale delta M b) E,
        (∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R, (Z Q).toTube = U.cover.tube b Q) ->
        ∃ normalization : ActualAssignedUnitNormalizationW97 U Uext a b R Z
          Rnorm Cext Cnorm CtwNorm CcellNorm,
          (∀ l, l <= M -> ∀ S ∈ normalization.cells.parentSet l,
            (normalization.cells.parentTube l S).direction =
              ‖((U.cover.tube a R).rescaleMap (Rnorm : Real)).linear
                (Uext.cover.tube (quotientGridIndexW97 M a b l) S).direction‖⁻¹ •
              ((U.cover.tube a R).rescaleMap (Rnorm : Real)).linear
                (Uext.cover.tube (quotientGridIndexW97 M a b l) S).direction) ∧
          (∀ l, l <= M -> ∀ S ∈ normalization.cells.parentSet l,
            let x := (U.cover.tube a R).rescaleMap (Rnorm : Real)
              (Uext.cover.tube (quotientGridIndexW97 M a b l) S).center
            let v := (normalization.cells.parentTube l S).direction
            (normalization.cells.parentTube l S).center = x - inner Real x v • v) := by
  obtain ⟨Rmin, hRmin, hquotient⟩ := exists_axisFoot_quotient_geometry_w103 hdim M hM
  let Rnorm := max Rmin (Tube.normalization.C (Module.finrank Real E))
  have hRminR : Rmin <= Rnorm := le_max_left _ _
  have hR : 1 <= Rnorm := hRmin.trans hRminR
  have hRn : Tube.normalization.C (Module.finrank Real E) <= Rnorm := le_max_right _ _
  have hRpos : 0 < Rnorm := zero_lt_one.trans_le hR
  let Cext : NNReal := max ((192 * Rnorm) ^ (3 : Nat) * 6) ((4 * Rnorm) ^ (6 : Nat))
  have hCgeo : (192 * Rnorm) ^ (3 : Nat) * 6 <= Cext := le_max_left _ _
  have hCamb : (4 * Rnorm) ^ (6 : Nat) <= Cext := le_max_right _ _
  have hCext : 1 <= Cext := by
    apply le_trans _ hCamb
    apply one_le_pow₀
    nlinarith
  have hCvol : (48 * Rnorm) ^ (3 : Nat) <= Cext := by
    have h48 : (48 * Rnorm : NNReal) <= 192 * Rnorm := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity) h48 (3 : Nat)
    nlinarith
  let Cline : NNReal := (lineAmplificationBoundW95 (Module.finrank Real E) 1 5 : NNReal) *
    (lineAmplificationBoundW95 (Module.finrank Real E) 2 (60 * (Rnorm : Real)) : NNReal) * Ctw
  let CtwNorm := max Ctw Cline
  have hCtwNorm : 1 <= CtwNorm := hCtw.trans (le_max_left _ _)
  obtain ⟨Cnear, Cden, hCnear, hCden, hcounting⟩ :=
    exists_complete_cell_geometry_count_w103 hdim CtwNorm Cext hCtwNorm hCext
  let Cnorm := max (Cext ^ (2 : Nat)) (max Cnear Cden)
  let CcellNorm := max Ccell Cden
  have hCnorm : 1 <= Cnorm := hCnear.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hCcellNorm : 1 <= CcellNorm := hCcell.trans (le_max_left _ _)
  have hCcf : Cext ^ (2 : Nat) <= Cnorm := le_max_left _ _
  have hCnnear : Cnear <= Cnorm := (le_max_left _ _).trans (le_max_right _ _)
  have hCnden : Cden <= Cnorm := (le_max_right _ _).trans (le_max_right _ _)
  have hCcellden : Cden <= CcellNorm := le_max_right _ _
  refine ⟨Rnorm, Cext, Cnorm, CtwNorm, CcellNorm, hR, hCext, hCnorm, hCtwNorm,
    hCcellNorm, le_max_left _ _, le_max_left _ _, ?_⟩
  intro delta hd hd1 hgap iota _ A Y Ccan U Uext hA restriction reg regext margin a b hab hb R hRmem Z hZ
  let F := actualDescendantsW95 A U.cover.assign a b R
  let theta := Tube.gridScale delta M a
  let tau := Tube.gridScale delta M b
  let d := tau / theta
  let c := quotientGridIndexW97 M a b
  let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
  let Jparents := fun l => F.image (parent l)
  let top := U.cover.tube a R
  have ha : a <= M := hab.le.trans hb
  have ht : 0 < theta := Tube.gridScale_pos hd M a
  have ht1 : theta <= 1 := Tube.gridScale_le_one hd1.le M a
  have htau : 0 < tau := Tube.gridScale_pos hd M b
  have htaut : tau <= theta := Tube.gridScale_antitone hd hd1.le M hab.le
  have hdpos : 0 < d := div_pos htau ht
  have hdle : d <= 1 := (div_le_one ht).mpr htaut
  have hdsmall : d <= 1 / 16 := grid_block_ratio_small_w103 hd hd1.le hM hab hgap
  obtain ⟨L, hL⟩ := Tube.exists_rescaleEquiv ht (show (0 : Real) < Rnorm from hRpos) top
  obtain ⟨hfTop, hpTop, hrho, hcontain⟩ :=
    hquotient Rnorm hRminR hd hd1 hgap U Uext hA restriction reg regext margin a b hab hb R hRmem L hL
  obtain ⟨hFne, hFext, hparents, hfibres, hcfibres, hbands, hbottom⟩ :=
    extended_middle_fibres_w97 U Uext restriction regext hM a b hab hb R hRmem
  obtain ⟨hFindex, hDpos, hDband, holdContained⟩ :=
    actual_fibre_data_w103 U Uext restriction regext hM a b hab hb R hRmem
  obtain ⟨hc0, hcM, hcbounds, hcstrict, hcradius⟩ :=
    quotient_grid_index_w97 M a b hM hab hb delta hd hd1
  let W := fun Q => axisFootTubeW103 d L (U.cover.tube b Q)
  let P : (l : Nat) -> iota -> Tube (Tube.gridScale d M l) E :=
    fun l S => axisFootTubeW103 (Tube.gridScale d M l) L (Uext.cover.tube (c l) S)
  have hparentRadius : ∀ l, l <= M -> Tube.gridScale delta (M * M) (c l) <= theta := by
    intro l hl
    dsimp only [theta]
    rw [restriction.radius a ha]
    exact Tube.gridScale_antitone hd hd1.le (M * M) (hcbounds l hl).1
  have hWimage : ∀ Q ∈ F, L '' (U.cover.tube b Q).carrier ⊆ (W Q).carrier := by
    intro Q hQ
    exact (axisFootTube_image_w103 htau htaut ht1 hR hRn top _ (hfTop Q hQ) L hL).1
  have hWcenter : ∀ Q ∈ F, ‖(W Q).center‖ <= 1 / 4 := by
    intro Q hQ
    exact (axisFootTube_image_w103 htau htaut ht1 hR hRn top _ (hfTop Q hQ) L hL).2
  have hWball : ∀ Q ∈ F, (W Q).carrier ⊆ Metric.closedBall 0 1 := by
    intro Q hQ
    refine (tube_ball_of_center_w103 (W Q) (hWcenter Q hQ)).trans ?_
    apply Metric.closedBall_subset_closedBall
    have hsmall : (d : Real) <= 1 / 16 := by exact_mod_cast hdsmall
    linarith
  have hWvolume : ∀ Q ∈ F, volume (W Q).carrier <= (Cext : ENNReal) * volume (L '' (U.cover.tube b Q).carrier) := by
    intro Q hQ
    exact (axisFootTube_volume_w103 hdim htau htaut ht1 hR hRn top _ (hfTop Q hQ) L hL).2.trans
      (mul_le_mul_right' (by exact_mod_cast hCvol) _)
  obtain ⟨V, hVtube, hVshade, hfullness, hmultiplicity⟩ :=
    exists_axisFoot_shading_transport_w103 F (U.cover.tube b) Z hZ L hWimage Cext hCext hWvolume
  have hVbody : ∀ Q, (V Q).toConvexSpaceBody = (W Q).toConvexSpaceBody :=
    fun Q => congrArg Tube.toConvexSpaceBody (hVtube Q)
  have hVcarrier : ∀ Q, (V Q).carrier = (W Q).carrier := fun Q => congrArg (fun T : Tube d E => T.carrier) (hVtube Q)
  have hVcontained : ∀ l, l <= M -> ∀ Q ∈ F,
      (V Q).toConvexSpaceBody <= (P l (parent l Q)).toConvexSpaceBody := by
    intro l hl Q hQ
    rw [hVbody]
    exact hcontain l hl Q hQ
  have hPimage : ∀ l, l <= M -> ∀ S ∈ Jparents l,
      L '' (Uext.cover.tube (c l) S).carrier ⊆ (P l S).carrier := by
    intro l hl S hS
    dsimp only [P]
    rw [hrho l hl]
    exact (axisFootTube_image_w103 (Tube.gridScale_pos hd _ _) (hparentRadius l hl) ht1 hR hRn top _
      (hpTop l hl S hS).2 L hL).1
  have hPcenter : ∀ l, l <= M -> ∀ S ∈ Jparents l, ‖(P l S).center‖ <= 1 / 4 := by
    intro l hl S hS
    dsimp only [P]
    rw [hrho l hl]
    exact (axisFootTube_image_w103 (Tube.gridScale_pos hd _ _) (hparentRadius l hl) ht1 hR hRn top _
      (hpTop l hl S hS).2 L hL).2
  have hPball : ∀ l, l <= M -> ∀ S ∈ Jparents l, (P l S).carrier ⊆ Metric.closedBall 0 2 := by
    intro l hl S hS
    refine (tube_ball_of_center_w103 (P l S) (hPcenter l hl S hS)).trans ?_
    apply Metric.closedBall_subset_closedBall
    have hscale : (Tube.gridScale d M l : Real) <= 1 := Tube.gridScale_le_one hdle M l
    linarith
  have hPvolume : ∀ l, l <= M -> ∀ S ∈ Jparents l,
      volume (P l S).carrier <= (Cext : ENNReal) * volume (L '' (Uext.cover.tube (c l) S).carrier) := by
    intro l hl S hS
    dsimp only [P]
    rw [hrho l hl]
    exact (axisFootTube_volume_w103 hdim (Tube.gridScale_pos hd _ _) (hparentRadius l hl) ht1 hR hRn top _
      (hpTop l hl S hS).2 L hL).2.trans (mul_le_mul_right' (by exact_mod_cast hCvol) _)
  have hPline : ∀ l, l <= M -> lineEssentiallyDistinctW94 (Jparents l) (P l) CtwNorm := by
    intro l hl
    have hJsub : Jparents l ⊆ Uext.cover.indexSet (c l) := fun S hS => (hpTop l hl S hS).1
    have hline := lineED_subset_w103 hJsub (Uext.cover.tube (c l))
      (regext.parent_line_ed (c l) (hcbounds l hl).2.2) le_rfl
    have hcOld : ∀ S ∈ Jparents l, ‖(Uext.cover.tube (c l) S).center‖ <= 2 := fun S hS =>
      tube_center_norm_of_ball_w103 (Tube.gridScale_pos hd _ _) _ 2
        (regext.parent_ball (c l) (hcbounds l hl).2.2 S (hJsub hS))
    have hh := axisFoot_family_lineED_w103 (Tube.gridScale_pos hd _ _) (hparentRadius l hl) ht1 hR hRn top
      (Jparents l) (Uext.cover.tube (c l)) (fun S hS => (hpTop l hl S hS).2) hcOld Ctw hline L hL
    have hhh : lineEssentiallyDistinctW94 (Jparents l) (P l) Cline := by
      dsimp only [P]
      rw [hrho l hl]
      exact hh
    exact lineED_subset_w103 (Finset.Subset.refl _) _ hhh (le_max_right _ _)
  have hVline : lineEssentiallyDistinctW94 F (fun Q => (V Q).toTube) CtwNorm := by
    have hline := lineED_subset_w103 hFindex (U.cover.tube b) (reg.parent_line_ed b hb) le_rfl
    have hcOld : ∀ Q ∈ F, ‖(U.cover.tube b Q).center‖ <= 2 := fun Q hQ =>
      tube_center_norm_of_ball_w103 htau _ 2 (reg.parent_ball b hb Q (hFindex hQ))
    have hh := axisFoot_family_lineED_w103 htau htaut ht1 hR hRn top F (U.cover.tube b) hfTop hcOld Ctw hline L hL
    have htubes : (fun Q => (V Q).toTube) = W := funext hVtube
    rw [htubes]
    exact lineED_subset_w103 (Finset.Subset.refl _) _ hh (le_max_right _ _)
  let Dband := fun l => if l < M then regext.countBand (c l) (b * M) else 1
  have hcountData : ∀ l, l <= M ->
      (∀ S ∈ Jparents l, ∃ nearby : Finset iota, nearby ⊆ Jparents l ∧
        (nearby.card : NNReal) <= Cnear ∧
        exactTubeCellW87 F (fun Q => (V Q).toTube) (P l S) ⊆ nearby.biUnion (completeFibreW94 F (parent l))) ∧
      (∀ S ∈ Jparents l, ∀ D : ConvexSpaceBody E,
        (P l S).toConvexSpaceBody <= D -> volume D.carrier <= (Cext : ENNReal) * volume (P l S).carrier ->
        ((familyIn F (fun Q => (V Q).toConvexSpaceBody) D).card : NNReal) <=
          Cden * ((completeFibreW94 F (parent l) S).card : NNReal)) := by
    intro l hl
    have hdl : d <= Tube.gridScale d M l := by
      have hh := Tube.gridScale_antitone hdpos hdle M hl
      rwa [Tube.gridScale_self d (show 0 < M by omega)] at hh
    apply hcounting hdpos hdl (Tube.gridScale_le_one hdle M l) F (Jparents l)
      (fun Q => (V Q).toTube) (P l) (parent l) rfl (hVcontained l hl)
    · intro Q hQ
      rw [hVtube]
      exact (hWcenter Q hQ).trans (by norm_num)
    · intro S hS
      exact (hPcenter l hl S hS).trans (by norm_num)
    · exact hPline l hl
    · intro S hS T hT
      exact (hDband l hl T hT).2.le.trans (mul_le_mul_left' (hDband l hl S hS).1 2)
  have hgeoUpper : ∀ l, l <= M -> ∀ S ∈ Jparents l,
      ((exactTubeCellW87 F (fun Q => (V Q).toTube) (P l S)).card : NNReal) < 2 * CcellNorm * Dband l := by
    intro l hl S hS
    have hden := (hcountData l hl).2 S hS (P l S).toConvexSpaceBody le_rfl
      (le_mul_of_one_le_left' (by exact_mod_cast hCext))
    apply hden.trans_lt
    have hlt := mul_lt_mul_of_pos_left (hDband l hl S hS).2 (zero_lt_one.trans_le hCden)
    calc
      Cden * ((completeFibreW94 F (parent l) S).card : NNReal) < Cden * (2 * Dband l) := hlt
      _ <= CcellNorm * (2 * Dband l) := mul_le_mul_right' hCcellden _
      _ = _ := by ring
  let cells := detailed_grid_cells_w103 hdpos hdle F V M hM CtwNorm CcellNorm P parent
    hVcontained hPball hPline Dband hDpos (fun l hl S hS => (hDband l hl S hS).1) hgeoUpper
  obtain ⟨Jac, hJac, hJacEq, hJacVol⟩ := rescale_jacobian_w103 hdim ht hRpos top
  have hLvol : ∀ K : Set E, volume (L '' K) = (Jac : ENNReal) * volume K := by
    intro K
    change volume (L.toAffineMap '' K) = _
    rw [hL]
    exact hJacVol K
  have hTopImage : top.toConvexSpaceBody.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous <=
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    have hball := Tube.rescale_image_ambient_subset_closedBall ht ht1
      (show (0 : Real) < Rnorm from hRpos) hRn top
    change L.toAffineMap '' top.carrier ⊆ Metric.closedBall 0 1
    rw [hL]
    exact hball.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hTopVol : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier <=
      (Cext : ENNReal) * volume (L '' top.carrier) := by
    have hh := Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient hdim ht
      (show (1 : Real) <= Rnorm from hR) top
    change volume (Metric.closedBall (0 : E) 1) <= _
    change volume (Metric.closedBall (0 : E) 1) <= (Cext : ENNReal) * volume (L.toAffineMap '' top.carrier)
    rw [hL]
    refine hh.trans (mul_le_mul_right' ?_ _)
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    simpa only [ENNReal.coe_pow, ENNReal.coe_mul, ENNReal.coe_ofNat] using ENNReal.coe_le_coe.mpr hCamb
  have hWholeCF := axisFoot_family_frostman_w103 hdim htau htaut ht1 hR hRn top F (U.cover.tube b)
    top.toConvexSpaceBody (tube_volume_ne_zero_w103 ht top) le_rfl hfTop L hL Cext hCgeo
    ConvexSpaceBody.closedUnitBall hTopImage hWball hTopVol
  have hWholeCF' := ennreal_comparison_w103 (zero_lt_one.trans_le hCnorm) hCcf hWholeCF.1 hWholeCF.2
  have hAssignedCF : ∀ l, l <= M -> ∀ S ∈ Jparents l,
      (Cnorm : ENNReal)⁻¹ * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube (c l) (b * M) S <=
        frostmanConstIn (completeFibreW94 F (parent l) S) (fun Q => (V Q).toConvexSpaceBody) (P l S).toConvexSpaceBody ∧
      frostmanConstIn (completeFibreW94 F (parent l) S) (fun Q => (V Q).toConvexSpaceBody) (P l S).toConvexSpaceBody <=
        (Cnorm : ENNReal) * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube (c l) (b * M) S := by
    intro l hl S hS
    have hWcontained : ∀ Q ∈ completeFibreW94 F (parent l) S,
        (W Q).toConvexSpaceBody <= (P l S).toConvexSpaceBody := by
      intro Q hQ
      obtain ⟨hQF, hQS⟩ := Finset.mem_filter.mp hQ
      rw [← hQS]
      exact hcontain l hl Q hQF
    have hh := axisFoot_family_frostman_w103 hdim htau htaut ht1 hR hRn top
      (completeFibreW94 F (parent l) S) (U.cover.tube b) (Uext.cover.tube (c l) S).toConvexSpaceBody
      (tube_volume_ne_zero_w103 (Tube.gridScale_pos hd _ _) _) (hpTop l hl S hS).2
      (holdContained l hl S hS) L hL Cext hCgeo (P l S).toConvexSpaceBody
      (hPimage l hl S hS) hWcontained (hPvolume l hl S hS)
    have hh' := ennreal_comparison_w103 (zero_lt_one.trans_le hCnorm) hCcf hh.1 hh.2
    rw [hcfibres l hl S hS] at hh'
    have hbodyEq : (fun Q => (V Q).toConvexSpaceBody) = (fun Q => (W Q).toConvexSpaceBody) := funext hVbody
    rwa [hbodyEq]
  let nearby : Nat -> iota -> Finset iota := fun l S =>
    if hl : l <= M then if hS : S ∈ Jparents l then Classical.choose ((hcountData l hl).1 S hS) else ∅ else ∅
  have hnearby : ∀ l, l <= M -> ∀ S ∈ Jparents l,
      nearby l S ⊆ Jparents l ∧ ((nearby l S).card : NNReal) <= Cnear ∧
      exactTubeCellW87 F (fun Q => (V Q).toTube) (P l S) ⊆ (nearby l S).biUnion (completeFibreW94 F (parent l)) := by
    intro l hl S hS
    simpa only [nearby, dif_pos hl, dif_pos hS] using Classical.choose_spec ((hcountData l hl).1 S hS)
  let normalization : ActualAssignedUnitNormalizationW97 U Uext a b R Z Rnorm Cext Cnorm CtwNorm CcellNorm :=
    { normalized := V
      cells := cells
      assign_eq := fun _ _ => rfl
      parents_eq := hparents
      assigned_eq := hfibres
      ball := by
        intro Q hQ
        rw [hVcarrier]
        exact hWball Q hQ
      centred := by
        intro Q hQ
        rw [hVtube]
        exact axisFootTube_centred_w103 L _
      line_ed := hVline
      fine_direction := by
        intro Q hQ
        rw [hVtube, axisFootTube_direction_w103]
        rw [← hL]
        rfl
      fine_centre := by
        intro Q hQ
        rw [hVtube, axisFootTube_center_w103]
        rw [← hL]
        rfl
      image_carrier := by
        intro Q hQ
        rw [hVcarrier, ← hL]
        exact hWimage Q hQ
      image_shade := by
        intro Q hQ
        rw [hVshade Q hQ, ← hL]
        rfl
      jacobian := Jac
      jacobian_pos := hJac
      jacobian_eq := hJacEq
      volume_image := fun K _ => hJacVol K
      carrier_volume := by
        intro Q hQ
        rw [hVcarrier, ← hLvol]
        refine ⟨measure_mono (hWimage Q hQ), ?_⟩
        simpa only [hLvol, mul_assoc] using hWvolume Q hQ
      parent_image := by
        intro l hl S hS
        change top.rescaleMap (Rnorm : Real) '' (Uext.cover.tube (c l) S).carrier ⊆ (P l S).carrier
        rw [← hL]
        exact hPimage l hl S hS
      parent_volume := by
        intro l hl S hS
        change (Jac : ENNReal) * volume (Uext.cover.tube (c l) S).carrier <= volume (P l S).carrier ∧
          volume (P l S).carrier <= (Cext : ENNReal) * (Jac : ENNReal) * volume (Uext.cover.tube (c l) S).carrier
        rw [← hLvol]
        refine ⟨measure_mono (hPimage l hl S hS), ?_⟩
        simpa only [hLvol, mul_assoc] using hPvolume l hl S hS
      forward_test := by
        intro K
        obtain ⟨D, hKD, hDvol, hD⟩ := axisFoot_family_forward_test_w103 hdim htau htaut ht1 hR hRn top
          F (U.cover.tube b) hfTop L hL K
        refine ⟨D, ?_, ?_⟩
        · have hh := hDvol.trans (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hCgeo) _)
          simpa only [hLvol, mul_assoc] using hh
        · intro Q hQ hQK
          rw [hVbody]
          exact hD Q hQ hQK
      backward_test := by
        intro K
        obtain ⟨D, hDvol, hD⟩ := axisFoot_family_backward_test_w103 F (U.cover.tube b) L hWimage hJac hLvol K
        refine ⟨D, ?_, ?_⟩
        · rw [hDvol, mul_assoc]
          exact le_mul_of_one_le_left' (by exact_mod_cast hCext)
        · intro Q hQ hQK
          apply hD Q hQ
          rwa [hVbody] at hQK
      whole_cf := by
        change (Cnorm : ENNReal)⁻¹ * frostmanConstIn F (fun Q => (U.cover.tube b Q).toConvexSpaceBody) top.toConvexSpaceBody <=
            frostmanConstIn F (fun Q => (V Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
          frostmanConstIn F (fun Q => (V Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
            (Cnorm : ENNReal) * frostmanConstIn F (fun Q => (U.cover.tube b Q).toConvexSpaceBody) top.toConvexSpaceBody
        have hbodyEq : (fun Q => (V Q).toConvexSpaceBody) = (fun Q => (W Q).toConvexSpaceBody) := funext hVbody
        rwa [hbodyEq]
      assigned_cf := hAssignedCF
      nearby := nearby
      nearby_subset := fun l hl S hS => (hnearby l hl S hS).1
      nearby_card := fun l hl S hS => (hnearby l hl S hS).2.1.trans hCnnear
      complete_cell_cover := fun l hl S hS => (hnearby l hl S hS).2.2
      enlarged_denominator := by
        intro l hl S hS D hSD hDvol
        exact ((hcountData l hl).2 S hS D hSD hDvol).trans (mul_le_mul_right' hCnden _)
      fullness := hfullness
      multiplicity := hmultiplicity }
  refine ⟨normalization, ?_, ?_⟩
  · intro l hl S hS
    change (P l S).direction = _
    dsimp only [P]
    rw [axisFootTube_direction_w103, ← hL]
    rfl
  · intro l hl S hS
    change (P l S).center = _
    dsimp only [P]
    rw [axisFootTube_center_w103, ← hL]
    rfl

end

end Kakeya.ml1Boot.TrialRestartW94
