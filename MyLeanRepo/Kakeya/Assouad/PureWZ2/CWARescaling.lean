import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedCover
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledEssentialDistinctness

/-!
# Rescale pure Definition 2.12 CWA from source to ordinary public family

Given pure CWA on a source family and an anchor tube, transport nearby-scale
CWA to the ordinary rescaled public family.  Source witnesses below the
anchor use nested-cover transport; witnesses jumping above the anchor are
replaced by a bounded witness below it.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2PaperOrdinaryRescaled_essentiallyDistinct_of_locality
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdelta : 0 < delta)
    (hdeltaRho : 100 * delta ≤ rho)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : ∀ i, WZ1PaperTubeCovers (sourceFamily.tube i) anchor)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (sourceFamily.tube first)
            (sourceFamily.tube second))
    (htargetLocal :
      ∀ index,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily anchor hrho).tube index)‖ ≤ 3) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFamily anchor hrho) := by
  let target :=
    wz2PaperLiteralOrdinaryRescaledFamily sourceFamily anchor hrho
  have htargetLine : WZ1PaperIsLineClass target :=
    wz2PaperLiteralOrdinaryRescaledFamily_lineClass
      hrho hrhoOne sourceFamily anchor hline hanchor
      (fun index => by
        have hstrict := hcover index
        unfold WZ1PaperTubeCovers at hstrict
        unfold WZ2PaperDilatedTubeCovers
        linarith)
  have htargetSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              (delta / rho) <
          wz1PaperLineDistance
            (target.tube first) (target.tube second) := by
    intro first second hne
    have hstrong :
        1600 * (delta / rho) <
          wz1PaperLineDistance
            (target.tube first) (target.tube second) := by
      exact
        wz2_paper_literal_dilated_strong_separation
          hdelta (by linarith) hrho hrhoOne
          (sourceFamily.tube first) (sourceFamily.tube second) anchor
          (hline first) (hline second) hanchor
          (by
            have hstrict := hcover first
            unfold WZ1PaperTubeCovers at hstrict
            unfold WZ2PaperDilatedTubeCovers
            linarith)
          (by
            have hstrict := hcover second
            unfold WZ1PaperTubeCovers at hstrict
            unfold WZ2PaperDilatedTubeCovers
            linarith)
          (hseparated first second hne)
          (target.tube first) (target.tube second)
          (htargetLine first) (htargetLine second)
          (wz2PaperLiteralOrdinaryRescaledTube_axis
            (sourceFamily.tube first) anchor hrho)
          (wz2PaperLiteralOrdinaryRescaledTube_axis
            (sourceFamily.tube second) anchor hrho)
    have hscale : 0 < delta / rho := div_pos hdelta hrho
    dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
    linarith
  exact
    wz2_paper_localized_ordinary_isEssentiallyDistinct
      (div_pos hdelta hrho) htargetLine htargetLocal htargetSeparated

theorem wz2PaperOrdinaryRescaled_essentiallyDistinct
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdelta : 0 < delta)
    (hdeltaRho : 100 * delta ≤ rho)
    (hsourceUnit : sourceFamily.IsInUnitBall)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : ∀ i, WZ1PaperTubeCovers (sourceFamily.tube i) anchor)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (sourceFamily.tube first)
            (sourceFamily.tube second)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFamily anchor hrho) :=
  wz2PaperLiteralOrdinaryRescaledFamily_essentiallyDistinct
    hdelta hrho (by linarith) hrhoOne sourceFamily anchor
    hsourceUnit hline hanchor hcover hseparated

noncomputable def wz2PaperPureScaleCoverData_rescale
    {delta rho t : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {C : ENNReal}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (_hdelta : 0 < delta)
    (hdeltaT : 100 * delta ≤ t)
    (htRho : t ≤ rho)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : ∀ i, WZ1PaperTubeCovers (sourceFamily.tube i) anchor)
    (scaleData : WZ2PaperPureScaleCoverData sourceFamily t C)
    (hcoarseLine : WZ1PaperIsLineClass scaleData.coarse)
    (hFineMiddle :
      ∀ source,
        WZ1PaperTubeCovers
          (sourceFamily.tube source)
          (scaleData.coarse.tube
            (scaleData.cover.parent source)))
    (hMiddleAnchor :
      ∀ parent,
        WZ2PaperDilatedTubeCovers 2
          (scaleData.coarse.tube parent) anchor)
    (hMiddleSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * t <
          wz1PaperLineDistance
            (scaleData.coarse.tube first)
            (scaleData.coarse.tube second))
    (localization :
      WZ2PaperOrdinaryNestedTargetLocalization
        sourceFamily scaleData.coarse anchor hrho) :
    WZ2PaperPureScaleCoverData
      (wz2PaperLiteralOrdinaryRescaledFamily sourceFamily anchor hrho)
      (t / rho)
      (max C ((81000000 : ENNReal) * C)) :=
  wz2PaperPureScaleCoverData.ordinaryNestedScale
    scaleData
    hrho hdeltaT htRho hrhoOne anchor
    hline hcoarseLine hanchor
    hFineMiddle hcover hMiddleAnchor hMiddleSeparated localization

lemma wz2PaperPureScaleCoverData_max_eq
    {C : ENNReal} (hC_one : 1 ≤ C) :
    max C ((81000000 : ENNReal) * C) =
      (81000000 : ENNReal) * C := by
  rw [max_eq_right]
  calc
    C = (1 : ENNReal) * C := by simp
    _ ≤ (81000000 : ENNReal) * C := by gcongr <;> norm_num

lemma ennreal_mul_lt_mul_right_cancel
    {x y c : ENNReal} (hc : c ≠ 0) (h : x * c < y * c) :
    x < y := by
  by_contra hnot
  have hle : y ≤ x := le_of_not_gt hnot
  exact (not_lt_of_ge (mul_le_mul_right' hle c)) h

theorem wz2PaperPureCWAAtNearbyScales_rescale_of_locality
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {C : ENNReal}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (_hdelta : 0 < delta)
    (hdeltaRho : 100 * delta ≤ rho)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : ∀ i, WZ1PaperTubeCovers (sourceFamily.tube i) anchor)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (sourceFamily.tube first)
            (sourceFamily.tube second))
    (htargetLocal :
      ∀ index,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily anchor hrho).tube index)‖ ≤ 3)
    (cwa : WZ2PaperPureCWAAtNearbyScales sourceFamily C)
    (hC_finite : C ≠ ⊤)
    (hC_one : 1 ≤ C)
    (h_assumptions_for_every_scale :
      ∀ (t : ℝ) (ht : delta ≤ t) (ht' : t ≤ rho)
        (scaleData : WZ2PaperPureScaleCoverData sourceFamily t C),
        WZ1PaperIsLineClass scaleData.coarse ∧
          (∀ source,
            WZ1PaperTubeCovers
              (sourceFamily.tube source)
              (scaleData.coarse.tube (scaleData.cover.parent source))) ∧
          (∀ parent, WZ2PaperDilatedTubeCovers 2
            (scaleData.coarse.tube parent) anchor) ∧
          (∀ first second, first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * t <
              wz1PaperLineDistance
                (scaleData.coarse.tube first)
                (scaleData.coarse.tube second)) ∧
          WZ2PaperOrdinaryNestedTargetLocalization
            sourceFamily scaleData.coarse anchor hrho)
    (h_covers_bounded :
      ∀ (s : ℝ), delta ≤ s → s ≤ rho →
        ∃ (t : ℝ) (scaleData : WZ2PaperPureScaleCoverData sourceFamily t C),
          s ≤ t ∧ t ≤ rho) :
    WZ2PaperPureCWAAtNearbyScales
      (wz2PaperLiteralOrdinaryRescaledFamily sourceFamily anchor hrho)
      ((81000000 : ENNReal) * C) := by
  let rescaledFamily :=
    wz2PaperLiteralOrdinaryRescaledFamily sourceFamily anchor hrho
  let K : ENNReal := (81000000 : ENNReal) * C
  have hdelta' : 0 < delta / rho := div_pos _hdelta hrho
  have hK_one : (1 : ENNReal) ≤ K := by
    calc
      (1 : ENNReal) ≤ (81000000 : ENNReal) := by norm_num
      _ ≤ (81000000 : ENNReal) * C := by
        exact le_mul_of_one_le_right (by norm_num) hC_one
  have hK_finite : K ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hC_finite
  have hdistinct : WZ2PaperOrdinaryIsEssentiallyDistinct rescaledFamily :=
    wz2PaperOrdinaryRescaled_essentiallyDistinct_of_locality
      hrho hrhoOne _hdelta hdeltaRho
      hline hanchor hcover hseparated htargetLocal
  have hmax : max C K = K :=
    wz2PaperPureScaleCoverData_max_eq hC_one
  have h_C_le_K : C ≤ K := by
    calc
      C = (1 : ENNReal) * C := by simp
      _ ≤ (81000000 : ENNReal) * C := by gcongr <;> norm_num
  refine ⟨hdelta', ⟨hK_one, hK_finite⟩, hdistinct, fun requested => ?_⟩
  let s : ℝ := requested.1
  have hs1 : delta / rho ≤ s := requested.2.1
  have hs2 : s ≤ 1 := requested.2.2
  have hs_pos : 0 < s := by linarith [_hdelta, hrho]
  let source_s : ℝ := max (s * rho) (100 * delta)
  have hsource_s1 : delta ≤ source_s := by
    apply le_max_of_le_left
    calc
      delta = (delta / rho) * rho := by
        field_simp [hrho.ne'] <;> ring
      _ ≤ s * rho := by
        exact mul_le_mul_of_nonneg_right hs1 (by linarith)
  have hsource_s2 : source_s ≤ rho := by
    apply max_le
    · exact mul_le_of_le_one_left (by linarith) hs2
    · exact hdeltaRho
  have hsource_s3 : source_s ≤ 1 := hsource_s2.trans hrhoOne
  let source_req : WZ2PaperRequestedScale delta :=
    ⟨source_s, hsource_s1, hsource_s3⟩
  rcases cwa.2.2.2 source_req with ⟨nearbyData⟩
  let t : ℝ := nearbyData.rho
  let scaleData := nearbyData.scaleData
  have h_t1 : source_s ≤ t := nearbyData.requested_le
  have h_t2 :
      ENNReal.ofReal t < C * ENNReal.ofReal source_s :=
    nearbyData.within_factor
  have h_t_pos : 0 < t := scaleData.rho_pos
  have h_rho_pos' : 0 < ENNReal.ofReal rho :=
    ENNReal.ofReal_pos.mpr hrho
  have h_rho_ne_zero : ENNReal.ofReal rho ≠ 0 := h_rho_pos'.ne'
  by_cases h_t3 : t ≤ rho
  · have h_100 : 100 * delta ≤ t :=
      (le_max_right _ _).trans h_t1
    rcases
        h_assumptions_for_every_scale t (by linarith) h_t3 scaleData
      with
      ⟨hmiddle, hFineMiddle, hMiddleAnchor,
        hMiddleSeparated, hlocalization⟩
    let rescaledCover :=
      wz2PaperPureScaleCoverData.ordinaryNestedScale
        scaleData hrho h_100 h_t3 hrhoOne anchor
        hline hmiddle hanchor
        hFineMiddle hcover hMiddleAnchor hMiddleSeparated hlocalization
    let rescaledCover' :
        WZ2PaperPureScaleCoverData rescaledFamily (t / rho) K :=
      hmax ▸ rescaledCover
    have h_requested_le : s ≤ t / rho := by
      have h : s * rho ≤ t :=
        (le_max_left _ _).trans h_t1
      calc
        s = (s * rho) / rho := by
          field_simp [hrho.ne'] <;> ring
        _ ≤ t / rho := by gcongr
    have h_goal :
        ENNReal.ofReal t < K * ENNReal.ofReal (s * rho) := by
      by_cases hcase : s * rho ≥ 100 * delta
      · have hsrc : source_s = s * rho := max_eq_left hcase
        rw [hsrc] at h_t2
        exact h_t2.trans_le <|
          mul_le_mul_right' h_C_le_K _
      · have hsrc : source_s = 100 * delta :=
          max_eq_right (by linarith)
        rw [hsrc] at h_t2
        have h_le : 100 * delta ≤ 100 * (s * rho) := by
          gcongr
          calc
            delta = (delta / rho) * rho := by
              field_simp [hrho.ne'] <;> ring
            _ ≤ s * rho := by
              exact mul_le_mul_of_nonneg_right hs1 (by linarith)
        have h7 :
            ENNReal.ofReal (100 * delta) ≤
              ENNReal.ofReal (100 * (s * rho)) :=
          ENNReal.ofReal_mono h_le
        have h8 :=
          mul_le_mul_left' h7 C
        have h9 :
            C * ENNReal.ofReal (100 * (s * rho)) =
              (100 : ENNReal) * C * ENNReal.ofReal (s * rho) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
          norm_num
          ring
        rw [h9] at h8
        have h10 : (100 : ENNReal) * C ≤ K := by
          dsimp only [K]
          gcongr
          norm_num
        calc
          ENNReal.ofReal t <
              C * ENNReal.ofReal (100 * delta) := h_t2
          _ ≤ (100 : ENNReal) * C *
              ENNReal.ofReal (s * rho) := h8
          _ ≤ K * ENNReal.ofReal (s * rho) := by gcongr
    have h_mul1 :
        ENNReal.ofReal (t / rho) * ENNReal.ofReal rho =
          ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [hrho.ne']
    have h_mul2 :
        K * ENNReal.ofReal s * ENNReal.ofReal rho =
          K * ENNReal.ofReal (s * rho) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      ring
    have h11 :
        ENNReal.ofReal (t / rho) * ENNReal.ofReal rho <
          K * ENNReal.ofReal s * ENNReal.ofReal rho := by
      rw [h_mul1, h_mul2]
      exact h_goal
    have h_within_factor :
        ENNReal.ofReal (t / rho) < K * ENNReal.ofReal s :=
      ennreal_mul_lt_mul_right_cancel h_rho_ne_zero h11
    exact ⟨t / rho, h_requested_le, h_within_factor, rescaledCover'⟩
  · have h_t_gt_rho : rho < t := by linarith
    have h_rho_lt_t :
        ENNReal.ofReal rho < ENNReal.ofReal t :=
      (ENNReal.ofReal_lt_ofReal_iff h_t_pos).mpr h_t_gt_rho
    have h_t_rho :
        ENNReal.ofReal rho < C * ENNReal.ofReal source_s :=
      h_rho_lt_t.trans h_t2
    have hK_s_gt_one : (1 : ENNReal) < K * ENNReal.ofReal s := by
      by_cases hcase : s * rho ≥ 100 * delta
      · have hsrc : source_s = s * rho := max_eq_left hcase
        rw [hsrc] at h_t_rho
        have h' :
            C * ENNReal.ofReal (s * rho) =
              C * ENNReal.ofReal s * ENNReal.ofReal rho := by
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
        rw [h'] at h_t_rho
        have h_cancel : (1 : ENNReal) < C * ENNReal.ofReal s :=
          ennreal_mul_lt_mul_right_cancel h_rho_ne_zero <| by
            simpa using h_t_rho
        exact h_cancel.trans_le <| mul_le_mul_right' h_C_le_K _
      · have hsrc : source_s = 100 * delta :=
          max_eq_right (by linarith)
        rw [hsrc] at h_t_rho
        have h_le : 100 * delta ≤ 100 * (s * rho) := by
          gcongr
          calc
            delta = (delta / rho) * rho := by
              field_simp [hrho.ne'] <;> ring
            _ ≤ s * rho := by
              exact mul_le_mul_of_nonneg_right hs1 (by linarith)
        have h7 :
            ENNReal.ofReal (100 * delta) ≤
              ENNReal.ofReal (100 * (s * rho)) :=
          ENNReal.ofReal_mono h_le
        have h8 := mul_le_mul_left' h7 C
        have h9 :
            C * ENNReal.ofReal (100 * (s * rho)) =
              (100 : ENNReal) * C *
                ENNReal.ofReal s * ENNReal.ofReal rho := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
          rw [ENNReal.ofReal_mul (by positivity)]
          norm_num
          ring
        rw [h9] at h8
        have h10 :
            (1 : ENNReal) * ENNReal.ofReal rho <
              (100 : ENNReal) * C *
                ENNReal.ofReal s * ENNReal.ofReal rho := by
          calc
            (1 : ENNReal) * ENNReal.ofReal rho =
                ENNReal.ofReal rho := by simp
            _ < C * ENNReal.ofReal (100 * delta) := h_t_rho
            _ ≤ _ := h8
        have h_cancel :
            (1 : ENNReal) <
              (100 : ENNReal) * C * ENNReal.ofReal s :=
          ennreal_mul_lt_mul_right_cancel h_rho_ne_zero h10
        have h100 : (100 : ENNReal) * C ≤ K := by
          dsimp only [K]
          gcongr
          norm_num
        exact h_cancel.trans_le <| mul_le_mul_right' h100 _
    rcases h_covers_bounded source_s hsource_s1 hsource_s2 with
      ⟨t', scaleData', h_t'1, h_t'2⟩
    have h_100' : 100 * delta ≤ t' :=
      (le_max_right _ _).trans h_t'1
    rcases
        h_assumptions_for_every_scale
          t' (by linarith) h_t'2 scaleData'
      with
      ⟨hmiddle, hFineMiddle, hMiddleAnchor,
        hMiddleSeparated, hlocalization⟩
    let rescaledCover :=
      wz2PaperPureScaleCoverData.ordinaryNestedScale
        scaleData' hrho h_100' h_t'2 hrhoOne anchor
        hline hmiddle hanchor
        hFineMiddle hcover hMiddleAnchor hMiddleSeparated hlocalization
    let rescaledCover' :
        WZ2PaperPureScaleCoverData rescaledFamily (t' / rho) K :=
      hmax ▸ rescaledCover
    have h_requested_le' : s ≤ t' / rho := by
      have h : s * rho ≤ t' :=
        (le_max_left _ _).trans h_t'1
      calc
        s = (s * rho) / rho := by
          field_simp [hrho.ne'] <;> ring
        _ ≤ t' / rho := by
          apply div_le_div_of_nonneg_right h hrho.le
    have h_within_factor' :
        ENNReal.ofReal (t' / rho) < K * ENNReal.ofReal s := by
      have h1 : t' / rho ≤ 1 := (div_le_one hrho).mpr h_t'2
      have h2 : ENNReal.ofReal (t' / rho) ≤ 1 := by
        simpa using ENNReal.ofReal_le_one.mpr h1
      exact h2.trans_lt hK_s_gt_one
    exact ⟨t' / rho, h_requested_le', h_within_factor', rescaledCover'⟩

/--
Rescale pure nearby CWA using geometry only for the canonical nearby witnesses
selected by the source CWA.

Unlike `wz2PaperPureCWAAtNearbyScales_rescale_of_locality`, the nested-geometry
premise is never applied to an arbitrary manually assembled exact-scale cover.
The bounded fallback is likewise required to be an actual nearby witness of
the same source CWA.
-/
theorem wz2PaperPureCWAAtNearbyScales_rescale_canonical_of_locality
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {C : ENNReal}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdelta : 0 < delta)
    (hdeltaRho : 100 * delta ≤ rho)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : ∀ index, WZ1PaperTubeCovers (sourceFamily.tube index) anchor)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (sourceFamily.tube first)
            (sourceFamily.tube second))
    (htargetLocal :
      ∀ index,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily anchor hrho).tube index)‖ ≤ 3)
    (cwa : WZ2PaperPureCWAAtNearbyScales sourceFamily C)
    (nearby :
      ∀ requested : WZ2PaperRequestedScale delta,
        WZ2PaperPureNearbyScaleCoverData
          sourceFamily requested C)
    (actualNestedGeometry :
      ∀ requested : WZ2PaperRequestedScale delta,
        (nearby requested).rho ≤ rho →
          WZ1PaperIsLineClass (nearby requested).scaleData.coarse ∧
            (∀ source,
              WZ1PaperTubeCovers
                (sourceFamily.tube source)
                ((nearby requested).scaleData.coarse.tube
                  ((nearby requested).scaleData.cover.parent source))) ∧
            (∀ middle,
              WZ2PaperDilatedTubeCovers 2
                ((nearby requested).scaleData.coarse.tube middle) anchor) ∧
            (∀ first second, first ≠ second →
              wz2PaperLiteralSourceSeparationFactor *
                    (nearby requested).rho <
                wz1PaperLineDistance
                  ((nearby requested).scaleData.coarse.tube first)
                  ((nearby requested).scaleData.coarse.tube second)) ∧
            WZ2PaperOrdinaryNestedTargetLocalization
              sourceFamily (nearby requested).scaleData.coarse
              anchor hrho)
    (fallback :
      (∀ (scale : ℝ), delta ≤ scale → scale ≤ rho →
        ∃ requested : WZ2PaperRequestedScale delta,
          scale ≤ (nearby requested).rho ∧
            (nearby requested).rho ≤ rho) ∨
      Nonempty
        (WZ2PaperPureScaleCoverData
          (wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily anchor hrho)
          4 ((81000000 : ENNReal) * C))) :
    WZ2PaperPureCWAAtNearbyScales
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFamily anchor hrho)
      ((81000000 : ENNReal) * C) := by
  let rescaledFamily :=
    wz2PaperLiteralOrdinaryRescaledFamily sourceFamily anchor hrho
  let targetConstant : ENNReal := (81000000 : ENNReal) * C
  have targetOne : (1 : ENNReal) ≤ targetConstant := by
    calc
      (1 : ENNReal) ≤ (81000000 : ENNReal) := by norm_num
      _ ≤ (81000000 : ENNReal) * C := by
        exact le_mul_of_one_le_right (by norm_num) cwa.2.1.1
  have targetFinite : targetConstant ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) cwa.2.1.2
  have targetDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct rescaledFamily :=
    wz2PaperOrdinaryRescaled_essentiallyDistinct_of_locality
      hrho hrhoOne hdelta hdeltaRho hline hanchor hcover
      hseparated htargetLocal
  have constantEq :
      max C targetConstant = targetConstant :=
    wz2PaperPureScaleCoverData_max_eq cwa.2.1.1
  have sourceConstantLe : C ≤ targetConstant := by
    calc
      C = (1 : ENNReal) * C := by simp
      _ ≤ (81000000 : ENNReal) * C := by
        gcongr
        norm_num
  refine
    ⟨div_pos hdelta hrho, ⟨targetOne, targetFinite⟩,
      targetDistinct, ?_⟩
  intro requested
  let requestedScale : ℝ := requested.1
  have requestedLower : delta / rho ≤ requestedScale :=
    requested.2.1
  have requestedUpper : requestedScale ≤ 1 :=
    requested.2.2
  have requestedPos : 0 < requestedScale :=
    (div_pos hdelta hrho).trans_le requestedLower
  let sourceRequestedScale : ℝ :=
    max (requestedScale * rho) (100 * delta)
  have sourceRequestedLower : delta ≤ sourceRequestedScale := by
    apply le_max_of_le_left
    calc
      delta = (delta / rho) * rho := by
        field_simp [hrho.ne']
      _ ≤ requestedScale * rho := by
        exact mul_le_mul_of_nonneg_right requestedLower hrho.le
  have sourceRequestedUpper : sourceRequestedScale ≤ rho := by
    apply max_le
    · exact mul_le_of_le_one_left hrho.le requestedUpper
    · exact hdeltaRho
  have sourceRequestedUnit : sourceRequestedScale ≤ 1 :=
    sourceRequestedUpper.trans hrhoOne
  let sourceRequest : WZ2PaperRequestedScale delta :=
    ⟨sourceRequestedScale, sourceRequestedLower, sourceRequestedUnit⟩
  let actual := nearby sourceRequest
  let actualScale : ℝ := actual.rho
  let actualScaleData := actual.scaleData
  have actualRequestedLower : sourceRequestedScale ≤ actualScale :=
    actual.requested_le
  have actualWithin :
      ENNReal.ofReal actualScale <
        C * ENNReal.ofReal sourceRequestedScale :=
    actual.within_factor
  have actualPos : 0 < actualScale :=
    actualScaleData.rho_pos
  have rhoOfRealPos : 0 < ENNReal.ofReal rho :=
    ENNReal.ofReal_pos.mpr hrho
  have rhoOfRealNe : ENNReal.ofReal rho ≠ 0 :=
    rhoOfRealPos.ne'
  by_cases actualBounded : actualScale ≤ rho
  · have treeSafe : 100 * delta ≤ actualScale :=
      (le_max_right _ _).trans actualRequestedLower
    rcases actualNestedGeometry sourceRequest actualBounded with
      ⟨middleLine, fineMiddle, middleAnchor,
        middleSeparated, localization⟩
    let rescaledCover :=
      wz2PaperPureScaleCoverData.ordinaryNestedScale
        actualScaleData hrho treeSafe actualBounded hrhoOne anchor
        hline middleLine hanchor fineMiddle hcover
        middleAnchor middleSeparated localization
    let rescaledCover' :
        WZ2PaperPureScaleCoverData
          rescaledFamily (actualScale / rho) targetConstant :=
      constantEq ▸ rescaledCover
    have requestedLeActual :
        requestedScale ≤ actualScale / rho := by
      have productLe : requestedScale * rho ≤ actualScale :=
        (le_max_left _ _).trans actualRequestedLower
      calc
        requestedScale =
            (requestedScale * rho) / rho := by
          field_simp [hrho.ne']
        _ ≤ actualScale / rho := by
          gcongr
    have actualWithinTarget :
        ENNReal.ofReal actualScale <
          targetConstant *
            ENNReal.ofReal (requestedScale * rho) := by
      by_cases productTreeSafe :
          requestedScale * rho ≥ 100 * delta
      · have sourceEq :
            sourceRequestedScale = requestedScale * rho :=
          max_eq_left productTreeSafe
        rw [sourceEq] at actualWithin
        exact
          actualWithin.trans_le <|
            mul_le_mul_right' sourceConstantLe _
      · have sourceEq :
            sourceRequestedScale = 100 * delta :=
          max_eq_right (by linarith)
        rw [sourceEq] at actualWithin
        have scaledLower :
            100 * delta ≤ 100 * (requestedScale * rho) := by
          gcongr
          calc
            delta = (delta / rho) * rho := by
              field_simp [hrho.ne']
            _ ≤ requestedScale * rho := by
              exact
                mul_le_mul_of_nonneg_right requestedLower hrho.le
        have ofRealLower :
            ENNReal.ofReal (100 * delta) ≤
              ENNReal.ofReal
                (100 * (requestedScale * rho)) :=
          ENNReal.ofReal_mono scaledLower
        have multipliedLower :=
          mul_le_mul_left' ofRealLower C
        have multipliedEq :
            C *
                ENNReal.ofReal
                  (100 * (requestedScale * rho)) =
              (100 : ENNReal) * C *
                ENNReal.ofReal (requestedScale * rho) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
          norm_num
          ring
        rw [multipliedEq] at multipliedLower
        have hundredLe :
            (100 : ENNReal) * C ≤ targetConstant := by
          dsimp only [targetConstant]
          gcongr
          norm_num
        calc
          ENNReal.ofReal actualScale <
              C * ENNReal.ofReal (100 * delta) :=
            actualWithin
          _ ≤
              (100 : ENNReal) * C *
                ENNReal.ofReal (requestedScale * rho) :=
            multipliedLower
          _ ≤
              targetConstant *
                ENNReal.ofReal (requestedScale * rho) := by
            gcongr
    have quotientMul :
        ENNReal.ofReal (actualScale / rho) *
            ENNReal.ofReal rho =
          ENNReal.ofReal actualScale := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [hrho.ne']
    have targetMul :
        targetConstant * ENNReal.ofReal requestedScale *
            ENNReal.ofReal rho =
          targetConstant *
            ENNReal.ofReal (requestedScale * rho) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      ring
    have multipliedWithin :
        ENNReal.ofReal (actualScale / rho) *
              ENNReal.ofReal rho <
            targetConstant * ENNReal.ofReal requestedScale *
              ENNReal.ofReal rho := by
      rw [quotientMul, targetMul]
      exact actualWithinTarget
    have withinTarget :
        ENNReal.ofReal (actualScale / rho) <
          targetConstant * ENNReal.ofReal requestedScale :=
      ennreal_mul_lt_mul_right_cancel rhoOfRealNe multipliedWithin
    exact
      ⟨actualScale / rho, requestedLeActual,
        withinTarget, rescaledCover'⟩
  · have rhoLtActual : rho < actualScale := by
      linarith
    have rhoLtActualOfReal :
        ENNReal.ofReal rho < ENNReal.ofReal actualScale :=
      (ENNReal.ofReal_lt_ofReal_iff actualPos).mpr rhoLtActual
    have rhoWithinSource :
        ENNReal.ofReal rho <
          C * ENNReal.ofReal sourceRequestedScale :=
      rhoLtActualOfReal.trans actualWithin
    have targetRequestedGtFour :
        (4 : ENNReal) <
          targetConstant * ENNReal.ofReal requestedScale := by
      by_cases productTreeSafe :
          requestedScale * rho ≥ 100 * delta
      · have sourceEq :
            sourceRequestedScale = requestedScale * rho :=
          max_eq_left productTreeSafe
        rw [sourceEq] at rhoWithinSource
        have productEq :
            C * ENNReal.ofReal (requestedScale * rho) =
              C * ENNReal.ofReal requestedScale *
                ENNReal.ofReal rho := by
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
        rw [productEq] at rhoWithinSource
        have cancelled :
            (1 : ENNReal) <
              C * ENNReal.ofReal requestedScale :=
          ennreal_mul_lt_mul_right_cancel rhoOfRealNe <| by
            simpa using rhoWithinSource
        calc
          (4 : ENNReal) < 81000000 := by norm_num
          _ = 1 * 81000000 := by simp
          _ < (C * ENNReal.ofReal requestedScale) * 81000000 :=
            ENNReal.mul_lt_mul_left
              (by norm_num : (81000000 : ENNReal) ≠ 0)
              (by norm_num : (81000000 : ENNReal) ≠ ⊤)
              cancelled
          _ =
              targetConstant * ENNReal.ofReal requestedScale := by
            dsimp only [targetConstant]
            ring
      · have sourceEq :
            sourceRequestedScale = 100 * delta :=
          max_eq_right (by linarith)
        rw [sourceEq] at rhoWithinSource
        have scaledLower :
            100 * delta ≤ 100 * (requestedScale * rho) := by
          gcongr
          calc
            delta = (delta / rho) * rho := by
              field_simp [hrho.ne']
            _ ≤ requestedScale * rho := by
              exact
                mul_le_mul_of_nonneg_right requestedLower hrho.le
        have ofRealLower :
            ENNReal.ofReal (100 * delta) ≤
              ENNReal.ofReal
                (100 * (requestedScale * rho)) :=
          ENNReal.ofReal_mono scaledLower
        have multipliedLower :=
          mul_le_mul_left' ofRealLower C
        have multipliedEq :
            C *
                ENNReal.ofReal
                  (100 * (requestedScale * rho)) =
              (100 : ENNReal) * C *
                ENNReal.ofReal requestedScale *
                ENNReal.ofReal rho := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)]
          rw [ENNReal.ofReal_mul (by positivity)]
          norm_num
          ring
        rw [multipliedEq] at multipliedLower
        have multipliedStrict :
            (1 : ENNReal) * ENNReal.ofReal rho <
              (100 : ENNReal) * C *
                ENNReal.ofReal requestedScale *
                ENNReal.ofReal rho := by
          calc
            (1 : ENNReal) * ENNReal.ofReal rho =
                ENNReal.ofReal rho := by simp
            _ <
                C * ENNReal.ofReal (100 * delta) :=
              rhoWithinSource
            _ ≤ _ := multipliedLower
        have cancelled :
            (1 : ENNReal) <
              (100 : ENNReal) * C *
                ENNReal.ofReal requestedScale :=
          ennreal_mul_lt_mul_right_cancel
            rhoOfRealNe multipliedStrict
        have hundredLe :
            (100 : ENNReal) * C ≤ targetConstant := by
          dsimp only [targetConstant]
          gcongr
          norm_num
        calc
          (4 : ENNReal) = 4 * 1 := by simp
          _ = 1 * 4 := by simp
          _ < ((100 : ENNReal) * C *
                ENNReal.ofReal requestedScale) * 4 :=
            ENNReal.mul_lt_mul_left
              (by norm_num : (4 : ENNReal) ≠ 0)
              (by norm_num : (4 : ENNReal) ≠ ⊤)
              cancelled
          _ ≤
              targetConstant * ENNReal.ofReal requestedScale := by
            calc
              ((100 : ENNReal) * C *
                    ENNReal.ofReal requestedScale) * 4 =
                  400 * (C * ENNReal.ofReal requestedScale) := by
                ring
              _ ≤ 81000000 *
                    (C * ENNReal.ofReal requestedScale) :=
                mul_le_mul_right'
                  (by norm_num : (400 : ENNReal) ≤ 81000000) _
              _ =
                  targetConstant * ENNReal.ofReal requestedScale := by
                dsimp only [targetConstant]
                ring
    rcases fallback with boundedActualWitness | topScale
    · rcases
          boundedActualWitness
            sourceRequestedScale sourceRequestedLower sourceRequestedUpper
        with ⟨fallbackRequest, fallbackLower, fallbackBounded⟩
      let fallbackWitness := nearby fallbackRequest
      let fallbackScale : ℝ := fallbackWitness.rho
      let fallbackScaleData := fallbackWitness.scaleData
      have fallbackTreeSafe : 100 * delta ≤ fallbackScale :=
        (le_max_right _ _).trans fallbackLower
      rcases
          actualNestedGeometry fallbackRequest fallbackBounded
        with
        ⟨middleLine, fineMiddle, middleAnchor,
          middleSeparated, localization⟩
      let rescaledCover :=
        wz2PaperPureScaleCoverData.ordinaryNestedScale
          fallbackScaleData hrho fallbackTreeSafe fallbackBounded
          hrhoOne anchor hline middleLine hanchor
          fineMiddle hcover middleAnchor middleSeparated localization
      let rescaledCover' :
          WZ2PaperPureScaleCoverData
            rescaledFamily (fallbackScale / rho) targetConstant :=
        constantEq ▸ rescaledCover
      have requestedLeFallback :
          requestedScale ≤ fallbackScale / rho := by
        have productLe : requestedScale * rho ≤ fallbackScale :=
          (le_max_left _ _).trans fallbackLower
        calc
          requestedScale =
              (requestedScale * rho) / rho := by
            field_simp [hrho.ne']
          _ ≤ fallbackScale / rho := by
            exact div_le_div_of_nonneg_right productLe hrho.le
      have fallbackAtMostOne :
          ENNReal.ofReal (fallbackScale / rho) ≤ 1 := by
        apply ENNReal.ofReal_le_one.mpr
        exact (div_le_one hrho).mpr fallbackBounded
      have fallbackWithin :
          ENNReal.ofReal (fallbackScale / rho) <
            targetConstant * ENNReal.ofReal requestedScale :=
        fallbackAtMostOne.trans_lt <|
          (by norm_num : (1 : ENNReal) ≤ 4).trans_lt targetRequestedGtFour
      exact
        ⟨fallbackScale / rho, requestedLeFallback,
          fallbackWithin, rescaledCover'⟩
    · rcases topScale with ⟨topScaleData⟩
      have requestedLeTop : requestedScale ≤ 4 :=
        requestedUpper.trans (by norm_num)
      have topWithin :
          ENNReal.ofReal (4 : ℝ) <
            targetConstant * ENNReal.ofReal requestedScale := by
        norm_num
        exact targetRequestedGtFour
      exact ⟨4, requestedLeTop, topWithin, topScaleData⟩

theorem wz2PaperPureCWAAtNearbyScales_rescale
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {C : ENNReal}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdelta : 0 < delta)
    (hdeltaRho : 100 * delta ≤ rho)
    (hsourceUnit : sourceFamily.IsInUnitBall)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hanchor : WZ1PaperTubeInLineClass anchor)
    (hcover : ∀ i, WZ1PaperTubeCovers (sourceFamily.tube i) anchor)
    (hseparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * delta <
          wz1PaperLineDistance
            (sourceFamily.tube first)
            (sourceFamily.tube second))
    (cwa : WZ2PaperPureCWAAtNearbyScales sourceFamily C)
    (hC_finite : C ≠ ⊤)
    (hC_one : 1 ≤ C)
    (h_assumptions_for_every_scale :
      ∀ (t : ℝ) (ht : delta ≤ t) (ht' : t ≤ rho)
        (scaleData : WZ2PaperPureScaleCoverData sourceFamily t C),
        WZ1PaperIsLineClass scaleData.coarse ∧
          (∀ source,
            WZ1PaperTubeCovers
              (sourceFamily.tube source)
              (scaleData.coarse.tube (scaleData.cover.parent source))) ∧
          (∀ parent, WZ2PaperDilatedTubeCovers 2
            (scaleData.coarse.tube parent) anchor) ∧
          (∀ first second, first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * t <
              wz1PaperLineDistance
                (scaleData.coarse.tube first)
                (scaleData.coarse.tube second)) ∧
          WZ2PaperOrdinaryNestedTargetLocalization
            sourceFamily scaleData.coarse anchor hrho)
    (h_covers_bounded :
      ∀ (s : ℝ), delta ≤ s → s ≤ rho →
        ∃ (t : ℝ) (scaleData : WZ2PaperPureScaleCoverData sourceFamily t C),
          s ≤ t ∧ t ≤ rho) :
    WZ2PaperPureCWAAtNearbyScales
      (wz2PaperLiteralOrdinaryRescaledFamily sourceFamily anchor hrho)
      ((81000000 : ENNReal) * C) := by
  apply
    wz2PaperPureCWAAtNearbyScales_rescale_of_locality
      hrho hrhoOne hdelta hdeltaRho hline hanchor hcover hseparated
  · intro index
    exact
      wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three
        hdelta hrho hrhoOne
        (sourceFamily.tube index) anchor
        (hsourceUnit index) (hline index) (hcover index)
  · exact cwa
  · exact hC_finite
  · exact hC_one
  · exact h_assumptions_for_every_scale
  · exact h_covers_bounded

end Kakeya.Assouad

end
