module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.NaturalCutoff
public import Kakeya.DimensionThree.MainLemma2.WangZahl.AssertionDToKatzTaoCurrency

@[expose] public section

open MeasureTheory Filter Topology

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The single remaining analytic producer after the family, slab, ED,
currency, and exponent bridges: either the requested Katz--Tao estimate is
already true, or the input family has the unit-ball Frostman control needed by
the Assertion D reduction. -/
def FrostmanOrDone (gamma : Real) : Prop :=
  ∀ epsilon > (0 : Real), ∃ eta0 > (0 : Real), ∀ eta > (0 : Real), eta ≤ eta0 →
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {iota : Type u} (s : Finset iota) (T : iota -> ShadedTube delta Space3),
        s.Nonempty ->
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ->
        ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody)
          ((delta : ENNReal) ^ (-eta)) ->
        ShadedBody.fullness s (fun i => (T i).toShadedBody) >= delta ^ eta ->
        (∑ i ∈ s, volume (T i).shade <=
            (delta : ENNReal) ^ (-epsilon) * (s.card : ENNReal) ^ gamma *
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)) ∨
          ConvexSpaceBody.IsFrostmanIn s
            (fun i => (T i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall (E := Space3))
            ((delta : ENNReal) ^ (-eta))

/-- Once the single `FrostmanOrDone` analytic dichotomy is supplied,
`AssertionD(gamma,gamma)` implies the exact project Katz--Tao estimate. -/
theorem katzTaoEstimate_of_assertionD_of_frostmanOrDone
    {gamma : Real} (hgamma : 0 <= gamma)
    (hD : AssertionD.{u} gamma gamma)
    (hreduce : FrostmanOrDone.{u} gamma) :
    KatzTaoEstimate.{u} Space3 gamma := by
  intro epsilon hepsilon
  obtain ⟨kappa, etaD, hkappa, hetaD, hDall⟩ := hD (epsilon / 4) (by linarith)
  obtain ⟨eta0, heta0, hreduce'⟩ := hreduce epsilon hepsilon
  let etaW : Real := min (min etaD eta0) (epsilon / 4)
  let eta : Real := etaW / 4
  have hetaW : 0 < etaW := lt_min (lt_min hetaD heta0) (by linarith)
  have hetaW_D : etaW <= etaD := (min_le_left _ _).trans (min_le_left _ _)
  have hetaW_0 : etaW <= eta0 := (min_le_left _ _).trans (min_le_right _ _)
  have hetaW_eps : etaW <= epsilon / 4 := min_le_right _ _
  have heta : 0 < eta := div_pos hetaW (by norm_num)
  have heta_le_eta0 : eta <= eta0 := by
    have : eta <= etaW := by dsimp [eta]; linarith
    exact this.trans hetaW_0
  have heta_le_eps : eta <= epsilon := by
    dsimp [eta]; linarith
  refine ⟨eta, heta, ?_⟩
  let C : ENNReal := (Tube.volume_le.C 3 : ENNReal) ^ (gamma / 2)
  let c : ENNReal := C * (kappa : ENNReal)⁻¹
  have hCtop : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top hCtop (by simp [hkappa.ne'])
  have hscaleC : ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      C <= (kappa : ENNReal) * (delta : ENNReal) ^ (-(epsilon / 2) / 2) := by
    filter_upwards [eventually_finite_le_rpow_neg_wz hctop (by linarith : 0 < epsilon / 4),
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with delta habs hdelta
    have hz : (kappa : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hkappa.ne'
    calc
      C = (kappa : ENNReal) * c := by
        dsimp [c]
        calc
          C = C * ((kappa : ENNReal) * (kappa : ENNReal)⁻¹) := by
            rw [ENNReal.mul_inv_cancel hz ENNReal.coe_ne_top, mul_one]
          _ = (kappa : ENNReal) * (C * (kappa : ENNReal)⁻¹) := by ring
      _ <= (kappa : ENNReal) * (delta : ENNReal) ^ (-(epsilon / 2) / 2) := by
        gcongr
        convert habs using 1 <;> congr 1 <;> ring
  have hCtop : Tube.refineToEssDistinctLeaves.C 3 ≠ ⊤ := by
    rw [Tube.refineToEssDistinctLeaves.C]
    refine ENNReal.div_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ?_
    · rw [Tube.overlapContainment.C]
      exact ENNReal.ofReal_ne_top
    · exact_mod_cast (Tube.le_volume.c_pos 3).ne'
  filter_upwards [hreduce' eta heta heta_le_eta0,
      eventually_exists_nat_degree_cutoff hCtop heta,
      hscaleC,
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hred hMcut hscale ⟨hdelta0, hdelta1⟩
  intro iota s T hball hKT hfull
  by_cases hs : s.Nonempty
  · rcases hred s T hs hball hKT hfull with hdone | hF
    · exact hdone
    · obtain ⟨M, hMdegree, hMloss⟩ := hMcut
      have hmax : maxDensity s (fun i => (T i).toConvexSpaceBody) <=
          (delta : ENNReal) ^ (-eta) := hKT
      have hdense : (delta : ENNReal) ^ eta *
          (∑ i ∈ s, volume (T i).carrier) <=
          ∑ i ∈ s, volume (T i).shade := by
        have hfull' : (delta : ENNReal) ^ eta <=
            ShadedBody.fullness s (fun i => (T i).toShadedBody) := by
          simpa [ENNReal.coe_rpow_of_nonneg _ heta.le] using
            (ENNReal.coe_le_coe.mpr hfull)
        calc
          (delta : ENNReal) ^ eta * (∑ i ∈ s, volume (T i).carrier) <=
              (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) *
                (∑ i ∈ s, volume (T i).carrier) := by gcongr
          _ = ∑ i ∈ s, volume (T i).shade :=
            (ShadedBody.sum_volumeReal_shade_eq_fullness_mul s
              (fun i => (T i).toShadedBody)).symm
      obtain ⟨t, ht, hfamily, hshade, hdenseT, hconvexT, hslabT⟩ :=
        exists_assertionD_input_subfamily_four_eta hdelta0 hdelta1.le heta
          s T hs hMdegree hMloss hmax hKT hball hF hdense
      have heta4 : 4 * eta = etaW := by dsimp [eta]; ring
      have hdeltaE1 : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1.le
      have hdenseD : IsDense t T
          ⟨(delta : Real) ^ etaD, Real.rpow_nonneg delta.coe_nonneg _⟩ := by
        rw [IsDense] at hdenseT ⊢
        have hpow : (delta : ENNReal) ^ etaD <=
            (delta : ENNReal) ^ (4 * eta) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by
            rw [heta4]
            exact hetaW_D)
        have hdenseT' : (delta : ENNReal) ^ (4 * eta) *
            (∑ i ∈ t, volume (T i).carrier) <=
            ∑ i ∈ t, volume (T i).shade := by
          let q : NNReal := ⟨(delta : Real) ^ (4 * eta), Real.rpow_nonneg delta.coe_nonneg _⟩
          have hc : (q : ENNReal) =
              (delta : ENNReal) ^ (4 * eta) := by
            dsimp [q]
            rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity)]
            congr 1
          rw [← hc]
          simpa [q] using hdenseT
        let qD : NNReal := ⟨(delta : Real) ^ etaD, Real.rpow_nonneg delta.coe_nonneg _⟩
        have hcD : (qD : ENNReal) =
            (delta : ENNReal) ^ etaD := by
          dsimp [qD]
          rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity)]
          congr 1
        calc
          (qD : ENNReal) *
              (∑ i ∈ t, volume (T i).carrier) <=
              (delta : ENNReal) ^ etaD * (∑ i ∈ t, volume (T i).carrier) := by rw [hcD]
          _ <= _ := (mul_le_mul_right' hpow _).trans hdenseT'
      have hconvexD : katzTaoConvexWolffConstant t T <=
          (delta : ENNReal) ^ (-etaD) :=
        hconvexT.trans (ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by
          rw [heta4]
          linarith [hetaW_D]))
      have hslabD : frostmanSlabWolffConstant t T <=
          (delta : ENNReal) ^ (-etaD) :=
        hslabT.trans (ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by
          rw [heta4]
          linarith [hetaW_D]))
      have hDbound := hDall delta hdelta0 t T hfamily hdenseD hconvexD hslabD
      have htne : t.Nonempty := by
        by_contra ht0
        have htzero : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht0
        rw [htzero] at hshade
        have hsumcar : 0 < ∑ i ∈ s, volume (T i).carrier := by
          obtain ⟨i, hi⟩ := hs
          have hiV : 0 < volume (T i).carrier := by
            rw [volume_carrier_eq_tubeVolume T i]
            exact (tubeVolume_pos_and_ne_top hdelta0).1
          exact hiV.trans_le (Finset.single_le_sum (s := s)
            (f := fun j => volume (T j).carrier) (fun _ _ => bot_le) hi)
        have hsumshade : 0 < ∑ i ∈ s, volume (T i).shade :=
          (pos_iff_ne_zero.mpr (mul_ne_zero
            (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta0) ENNReal.coe_ne_top).ne'
            hsumcar.ne')).trans_le hdense
        exact (not_le_of_gt hsumshade) (by simpa using hshade)
      have hmass := assertionD_bound_implies_katzTao_mass (epsilon := epsilon / 2) t T hgamma hdelta0
        hdelta1.le htne hkappa (by simpa [C] using hscale) (by
            convert hDbound using 1 <;> ring)
      have hpull := katzTao_mass_pullback_of_shade_selection T ht hgamma hshade hmass
      have hL : ((M : ENNReal) + 1) <= (delta : ENNReal) ^ (-(2 * eta)) := hMloss
      calc
        (∑ i ∈ s, volume (T i).shade) <=
            ((M : ENNReal) + 1) * (delta : ENNReal) ^ (-(epsilon / 2)) *
              (s.card : ENNReal) ^ gamma *
                volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := hpull
        _ <= (delta : ENNReal) ^ (-epsilon) * (s.card : ENNReal) ^ gamma *
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
          have hexp : ((M : ENNReal) + 1) *
              (delta : ENNReal) ^ (-(epsilon / 2)) <=
              (delta : ENNReal) ^ (-epsilon) := by
            calc
              ((M : ENNReal) + 1) * (delta : ENNReal) ^ (-(epsilon / 2)) <=
                  (delta : ENNReal) ^ (-(2 * eta)) *
                    (delta : ENNReal) ^ (-(epsilon / 2)) := by gcongr
              _ = (delta : ENNReal) ^ (-(2 * eta) + -(epsilon / 2)) := by
                rw [ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hdelta0.ne')
                  ENNReal.coe_ne_top]
              _ <= (delta : ENNReal) ^ (-epsilon) :=
                ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by
                  have : eta = etaW / 4 := rfl
                  have h4 := hetaW_eps
                  rw [this]
                  linarith)
          gcongr
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.FrostmanOrDone
#print axioms Kakeya.WangZahl.katzTaoEstimate_of_assertionD_of_frostmanOrDone
