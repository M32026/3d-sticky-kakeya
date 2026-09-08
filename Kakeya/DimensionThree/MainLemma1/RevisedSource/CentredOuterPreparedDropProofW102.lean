module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceDropPreparationW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalAssignedGeometryW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CanonicalDropConstructorsW100
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.WindowSourceParentSelectionW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.RawPaidDropProfileW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceActualGoodW100
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualWindowSourceAssemblyW101
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.DropUniformPaymentsW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentredExactNsProofW102

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

private theorem drop_all_exact_ns_mono_radius_w102
    {iota : Type uI} [DecidableEq iota] {d r s : NNReal}
    (F : Finset iota) (Y : iota -> Tube d E) (hrs : r <= s) :
    allExactTubeNsW87 F Y r <= allExactTubeNsW87 F Y s := by
  apply allExactTubeNs_le_w87
  intro T hT
  have hsub : exactTubeCellW87 F Y T ⊆ exactTubeCellW87 F Y (T.rescale s) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
      (Finset.mem_filter.mp hi).2.trans (Tube.le_rescale T hrs)⟩
  exact (Kakeya.maxDensity_mono _ hsub).trans
    (maxDensity_exactTubeCell_le_allExactTubeNs_w87 (T.rescale s) (hT.mono hsub))

/-- The same source-centred entry for the same-selection outer-fullness route.
the estimate old-coarse fullness input and all outputs are retained verbatim. -/
theorem exists_centred_actual_outer_prepared_dividing_canonical_pass_w101
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (gamma : Real) (hgammaZero : gammaZero <= gamma) (hgamma : gamma <= 1)
    (Ccan CbaseTw CbaseCell Cwork Ctw Ccell BF Cprep Cselect : NNReal)
    (hCcan : 1 <= Ccan) (hCbaseTw : 1 <= CbaseTw) (hCbaseCell : 1 <= CbaseCell)
    (hCwork : 1 <= Cwork) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (hBF : 1 <= BF) (hCprep : 1 <= Cprep) (hCselect : 1 <= Cselect)
    (Kprep Kselect : Nat) (hKprep : 1 <= Kprep) (hKselect : 1 <= Kselect)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (Rnorm Cext Cnorm CtwNorm CcellNorm Ctransport Cgood Cpass : NNReal)
      (full : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
      (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
      (CM Kout : Nat) (eFull eCF : Real) (delta0 : NNReal),
      1 <= Rnorm ∧ 1 <= Cext ∧ 1 <= Cnorm ∧ 1 <= CtwNorm ∧ 1 <= CcellNorm ∧
      Ctw <= CtwNorm ∧ Ccell <= CcellNorm ∧
      1 <= Ctransport ∧ 1 <= Cgood ∧ 1 <= Cpass ∧ 1 <= CM ∧ 1 <= Kout ∧
      0 < eFull ∧ 0 < eCF ∧ 0 < delta0 ∧ delta0 < 1 ∧
      (∀ m : Fin (p.N + 1), m.val < p.N ->
        eFull < p.ε * min (full.inner m) (aux.inner m) / 100 ∧
        eCF < p.ε * xi m / 16000 ∧ full.Ktr m <= Kout ∧ aux.Ktr m <= Kout) ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        (B : Finset iota) (V : iota -> ShadedTube delta E)
        (base : FixedBaseReserveW94 B V)
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan),
        SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
        (∀ i ∈ B, centredTubeW94 (V i).toTube) ->
        (B.card : Real) <= (delta : Real) ^ (-7 : Real) ->
      ∀ (current : RetainedStateW94 B V) (A : Finset iota)
        (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork)
        (Uext : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) (M * M) Cwork),
        A.Nonempty -> A ⊆ current.active ->
        VisibleExtendedRestrictionW97 U Uext ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
        ActualTreeParameterMarginW98 Uext.cover normalizationParameterMarginW98 ->
        towerPreparationRetainedW95 delta Cprep Kprep *
          (∑ i ∈ current.active, volume (current.shading i).shade) <=
            ∑ i ∈ A, volume (current.shading i).shade ->
        (delta : ENNReal) ^ eFull <= fullness' A (fun i => (current.shading i).toShadedBody) ->
        frostmanConstIn A (fun i => (current.shading i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-eCF) ->
      ∀ (block : ActualSourceDividingBlockW95 U p BF) (loss : NNReal)
        (selections : ActualSameMassSelectionsW95 block loss),
        (loss : ENNReal) <= (towerPreparationRetainedW95 delta Cselect Kselect)⁻¹ ->
        (delta : ENNReal) ^ eFull <= fullness' (U.cover.indexSet block.b.val)
          (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) ->
        ((loss : ENNReal) ^ (14 : Nat))⁻¹ *
            (fullness' A (fun i => (current.shading i).toShadedBody)) ^ (4 : Nat) <=
          fullness' (U.cover.indexSet block.a.val)
            (fun R => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
              selections.coarseShading R).toShadedBody) ->
        let d := Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val
        ∃ calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
          Rnorm Cext Cnorm CtwNorm CcellNorm aux,
          (ShadedBody.multiplicity A (fun i => (current.shading i).toShadedBody) <=
            (Cgood : ENNReal) * (delta : ENNReal) ^ (18 * xiMin) *
              (delta : ENNReal) ^ (-2 * gamma) *
                ((delta : ENNReal) ^ (2 : Nat) * (A.card : ENNReal)) ^ (1 - gamma / 2)) ∨
          ∃ (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
              WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
                (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))
            (working : NNReal) (trialLevel ellPred : Fin (M + 1))
            (nodeFamily middlePlus Fdagger : Finset iota)
            (nodeTube : iota -> Tube working E)
            (part : iota -> Finset (CanonicalQNodeW87 U0 current.active block.b))
            (W : CanonicalQNodeW87 U0 current.active block.b ->
              ShadedTube (Tube.gridScale delta M block.b.val) E)
            (raw : LiteralInnerDropOutputW87 U0 block.b W nodeFamily nodeTube part d p.ε
              (p.η (block.label.val + 1) / 2) Kout)
            (Zplus : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E)
            (Ydagger : iota -> ShadedTube delta E) (c : NNReal),
            0 < working ∧ working <= 1 ∧
            ellPred.val < M ∧
            Tube.gridScale delta M (ellPred.val + 1) <= working ∧
            working < Tube.gridScale delta M ellPred.val ∧
            Tube.gridScale delta M block.a.val * Tube.gridScale d M trialLevel.val <= working ∧
            working <= Ctransport * Tube.gridScale delta M block.a.val * Tube.gridScale d M trialLevel.val ∧
            Fdagger.Nonempty ∧ Fdagger ⊆ selections.fineFamily ∧
            (∀ i ∈ Fdagger, (Ydagger i).toTube = (current.shading i).toTube ∧
              (Ydagger i).shade ⊆ (selections.fineShading i).shade) ∧
            middlePlus = Fdagger.image (U.cover.assign block.b.val) ∧
            middlePlus ⊆ selections.secondFamily ∧
            (∀ Q ∈ middlePlus, (Zplus Q).toTube = U.cover.tube block.b.val Q ∧
              (Zplus Q).shade ⊆ (selections.secondShading Q).shade ∧
              ∃ R, ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
                Q ∈ (drops R hR).Fplus ∧ (drops R hR).level = trialLevel ∧
                (Zplus Q).shade ⊆ ((U.cover.tube block.a.val R).rescaleMap (Rnorm : Real)) ⁻¹'
                  ((drops R hR).Yplus Q).shade) ∧
            (∀ Q ∈ middlePlus,
              (∑ i ∈ completeFibreW94 Fdagger (U.cover.assign block.b.val) Q, volume (Ydagger i).shade) =
                (selections.commonMass : ENNReal)⁻¹ * volume (Zplus Q).shade) ∧
            Fdagger.image (U0.cover.assign block.b.val) = raw.FPlus.image Subtype.val ∧
            (∀ w ∈ raw.FPlus, ∃ i ∈ Fdagger, U0.cover.assign block.b.val i = w.val ∧
              0 < volume (Ydagger i).shade) ∧
            0 < c ∧
            (∀ w, volume (W w).shade = (c : ENNReal) *
              ∑ i ∈ completeFibreW94 selections.fineFamily (U0.cover.assign block.b.val) w.val,
                volume (selections.fineShading i).shade) ∧
            (∀ w ∈ raw.FPlus, volume (raw.YPlus w).shade = (c : ENNReal) *
              ∑ i ∈ completeFibreW94 Fdagger (U0.cover.assign block.b.val) w.val,
                volume (Ydagger i).shade) ∧
            (∀ w, (W w).shade ⊆
              ⋃ i ∈ completeFibreW94 selections.fineFamily (U0.cover.assign block.b.val) w.val,
                (selections.fineShading i).shade) ∧
            (∀ w ∈ raw.FPlus, (raw.YPlus w).shade ⊆
              ⋃ i ∈ completeFibreW94 Fdagger (U0.cover.assign block.b.val) w.val, (Ydagger i).shade) ∧
            trialRetainedFractionW94 d Kout *
              (∑ i ∈ current.active, volume (current.shading i).shade) <=
                ∑ i ∈ Fdagger, volume (Ydagger i).shade ∧
            (∃ (next : RetainedStateW94 B V)
              (step : PaidDropTransitionW94 U0 current next CM Cpass (sourceFlatDropW95 p)),
              step.trialScale = d ∧ step.Ktr = Kout ∧
              step.daggerFamily = Fdagger ∧ step.Ydagger = Ydagger ∧
              step.drop_q = block.b ∧ step.drop_ell = ellPred ∧
              current.retained / uniformPaidPassCostW95 delta M CM Kout Cpass <= next.retained) := by
  obtain ⟨Rnorm, Cext, Cnorm, CtwNorm, CcellNorm, full, aux, eCall, deltaCall, Kmax,
    hRnorm, hCext, hCnorm, hCtwNorm, hCcellNorm, htw, hcell, heCall, hdeltaCall,
    hdeltaCall1, hKmax, hschedules, hcalls⟩ :=
    exists_prepared_eligible_window_trial_calls_w98 hdim hp gamma hgammaZero hgamma
      Ctw Ccell hCtw hCcell hKT hKF
  obtain ⟨Cgood, eGoodFull, eGoodCF, deltaGood, hCgood, heGoodFull, heGoodFullSmall,
    heGoodCF, heGoodCFSmall, hdeltaGood, hdeltaGood1, hgood⟩ :=
    actual_polylog_eligible_good_implies_source_good_w98 hdim hp gamma hgammaZero hgamma
      Ctw Ccell BF Rnorm Cext Cnorm CtwNorm CcellNorm hCtw hCcell hBF
      Cselect Kselect hCselect hKselect hKT hKF
  obtain ⟨Cden1, hCden1, hdensity⟩ :=
    exists_actual_window_assigned_density_transfer_w102 hdim CbaseTw Ctw Ccell
      Rnorm Cext Cnorm CtwNorm CcellNorm hCbaseTw hCtw hCcell hRnorm hCext hCnorm
  obtain ⟨Cden2, Lns, hCden2, hLns, hNs⟩ :=
    exists_centred_actual_canonical_exact_ns_comparison_w101 hdim CbaseTw Ctw Ccell
      Rnorm Cext Cnorm CtwNorm CcellNorm hCbaseTw hCtw hCcell hRnorm hCext hCnorm
  let Lgeom := max 5 Lns
  have hLgeom5 : (5 : NNReal) <= Lgeom := le_max_left _ _
  have hLgeom2 : (2 : NNReal) <= Lgeom := (by norm_num : (2 : NNReal) <= 5).trans hLgeom5
  have hLgeom1 : (1 : NNReal) <= Lgeom := (by norm_num : (1 : NNReal) <= 5).trans hLgeom5
  obtain ⟨Cdegree, Dgeom, hCdegree, hDgeom, hgeometry⟩ :=
    exists_actual_window_assigned_fine_geometry_w102 hdim Ccan CbaseTw CbaseCell
      Cwork Ctw Ccell Lgeom hCbaseTw hCtw hLgeom1 M
  let Cgeom : NNReal := 2 * (M + 1) * (Dgeom + 1) *
    (trialNearbyParentCountW96 CtwNorm : Nat) * Cdegree
  obtain ⟨Kout, deltaMass, hKoutMax, hKout, hdeltaMass, hdeltaMass1, hmassPayment⟩ :=
    exists_drop_uniform_polylog_payment_w102 p.ε hp.epsilon_pos Cgeom Cprep Cselect Kmax Kprep Kselect
  obtain ⟨deltaWork, hdeltaWork, hdeltaWork1, hworking⟩ :=
    exists_drop_working_scale_funding_w101 hp Lgeom hLgeom2
  obtain ⟨deltaSep, hdeltaSep, hdeltaSep1, hseparation⟩ :=
    exists_drop_window_scale_separation_w102 p.ε hp.epsilon_pos
  obtain ⟨deltaDensity, hdeltaDensity, hdeltaDensity1, hpayDensity⟩ :=
    exists_drop_fixed_density_payment_w101 hp (Cden1 * Cden2)
  obtain ⟨deltaProfile, hdeltaProfile, hdeltaProfile1, hprofile⟩ :=
    exists_paid_drop_transition_of_raw_w101 hdim hp Ccan hCcan 1 Kout hKout 1 (by norm_num)
  let eFull := min (eCall / 10) (eGoodFull / 2)
  let eCF := min (eGoodCF / 2) (p.ε * xiMin / 32000)
  let delta0 := min deltaCall (min deltaGood (min deltaWork
    (min deltaSep (min deltaDensity (min deltaMass deltaProfile)))))
  have heFull : 0 < eFull := lt_min (by positivity) (by positivity)
  have heCF : 0 < eCF := lt_min (by positivity)
    (div_pos (mul_pos hp.epsilon_pos hp.xiMin_pos) (by norm_num))
  have hdelta0 : 0 < delta0 := by dsimp [delta0]; positivity
  have hdelta01 : delta0 < 1 := (min_le_left _ _).trans_lt hdeltaCall1
  have heFullCall : eFull <= eCall := (min_le_left _ _).trans (by linarith)
  have heFullGood : eFull <= eGoodFull := (min_le_right _ _).trans (by linarith)
  have heCFGood : eCF <= eGoodCF := (min_le_left _ _).trans (by linarith)
  refine ⟨Rnorm, Cext, Cnorm, CtwNorm, CcellNorm, Lgeom, Cgood, 1, full, aux, 1, Kout,
    eFull, eCF, delta0, hRnorm, hCext, hCnorm, hCtwNorm, hCcellNorm, htw, hcell,
    hLgeom1, hCgood, by norm_num, by norm_num, hKout, heFull, heCF, hdelta0, hdelta01, ?_, ?_⟩
  · intro m hm
    obtain ⟨hmFull, hmKfull, hmKaux, _⟩ := hschedules m hm
    refine ⟨?_, ?_, hmKfull.trans hKoutMax, hmKaux.trans hKoutMax⟩
    · have he := min_le_left (eCall / 10) (eGoodFull / 2)
      change eFull <= eCall / 10 at he
      linarith
    · have he := min_le_right (eGoodCF / 2) (p.ε * xiMin / 32000)
      change eCF <= p.ε * xiMin / 32000 at he
      have hx := hp.xiMin_lower m hm
      have hxp := hp.xiMin_pos
      nlinarith [mul_le_mul_of_nonneg_left hx hp.epsilon_pos.le]
  · intro delta hd hdcut iota inst B V base U0 reg0 hcentred hcard current A U Uext
      hAne hA restriction reg regext margin hprep hfull hCF block loss selections
      hloss hsecondFull hcoarseFull
    change delta < min deltaCall (min deltaGood (min deltaWork
      (min deltaSep (min deltaDensity (min deltaMass deltaProfile))))) at hdcut
    obtain ⟨hdCall, hdrest⟩ := lt_min_iff.mp hdcut
    obtain ⟨hdGood, hdrest⟩ := lt_min_iff.mp hdrest
    obtain ⟨hdWork, hdrest⟩ := lt_min_iff.mp hdrest
    obtain ⟨hdSep, hdrest⟩ := lt_min_iff.mp hdrest
    obtain ⟨hdDensity, hdrest⟩ := lt_min_iff.mp hdrest
    obtain ⟨hdMass, hdProfile⟩ := lt_min_iff.mp hdrest
    have hd1 : delta < 1 := hdCall.trans hdeltaCall1
    have hballA : ∀ i ∈ A, (current.shading i).carrier ⊆ Metric.closedBall 0 1 := by
      intro i hi
      rw [show (current.shading i).carrier = (V i).carrier from
        congrArg (fun T : Tube delta E => T.carrier) (current.same_tube i (hA hi))]
      exact base.ball i (current.active_subset (hA hi))
    have hfullCall : (delta : ENNReal) ^ eCall <= fullness' (U.cover.indexSet block.b.val)
        (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) :=
      (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le) heFullCall).trans hsecondFull
    obtain ⟨calls, houtcome⟩ := hcalls hd hdCall U Uext hAne hballA restriction reg regext margin
      block selections hfullCall
    refine ⟨calls, ?_⟩
    by_cases hGood : ∃ R, ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
        detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
          (calls.normalization R hR).normalized gamma p.ε (xi block.label)
    · obtain ⟨R, hR, hGood⟩ := hGood
      left
      exact hgood hd hdGood U Uext hAne hballA reg
        ((ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le) heFullGood).trans hfull)
        (hCF.trans (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le) (by linarith)))
        block selections aux calls hloss hcoarseFull R hR hGood
    · right
      have hDrops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
          Nonempty (WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
            (p.η (block.label.val + 1) / 2) (aux.Ktr block.label)) := by
        intro R hR
        exact (houtcome R hR).resolve_left (fun h => hGood ⟨R, hR, h⟩)
      let drops := fun R hR => Classical.choice (hDrops R hR)
      let theta := Tube.gridScale delta M block.a.val
      let tau := Tube.gridScale delta M block.b.val
      let d := tau / theta
      have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
      have htheta : 0 < theta := Tube.gridScale_pos hd M _
      have htheta1 : theta <= 1 := Tube.gridScale_le_one hd1.le M _
      have hdtau : delta <= tau := by
        simpa only [Tube.gridScale_self delta hp.M_pos] using Tube.gridScale_antitone hd hd1.le M hb
      have htautheta : tau <= theta := Tube.gridScale_antitone hd hd1.le M block.a_lt_b.le
      have hdp : 0 < d := div_pos (Tube.gridScale_pos hd M _) htheta
      have hdsmall : d < 1 := block.block_long.trans_lt (by
        simpa only [NNReal.one_rpow] using NNReal.rpow_lt_rpow hd1 hp.epsilon_pos)
      have hdd : delta <= d := (le_div_iff₀ htheta).mpr (by
        have h := mul_le_mul_of_nonneg_left htheta1 delta.coe_nonneg
        have h' : delta * theta <= delta := by simpa only [mul_one] using h
        exact h'.trans hdtau)
      have hbaseMass : 0 < ∑ i ∈ B, volume (V i).shade := by
        by_contra h
        have hz : (∑ i ∈ B, volume (V i).shade) = 0 := le_antisymm (le_of_not_gt h) bot_le
        have hpos := base.lambda0_pos.trans_le base.fullness
        change 0 < (∑ i ∈ B, volume (V i).shade) / _ at hpos
        rw [hz, ENNReal.zero_div] at hpos
        exact lt_irrefl _ hpos
      have hcurrentMass : 0 < ∑ i ∈ current.active, volume (current.shading i).shade :=
        (ENNReal.mul_pos current.retained_pos.ne' hbaseMass.ne').trans_le current.mass_retention
      have hAMass : 0 < ∑ i ∈ A, volume (current.shading i).shade := by
        apply lt_of_lt_of_le _ hprep
        apply ENNReal.mul_pos _ hcurrentMass.ne'
        exact ENNReal.inv_ne_zero.mpr (by finiteness)
      have hfineMass : 0 < ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade :=
        (ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (by finiteness)) hAMass.ne').trans_le selections.fine_retention
      obtain ⟨trialLevel, middle0, F0, Z0, Ydagger, hF0ne, hF0fine, hYdagger, hmiddle0,
        hmiddle0Sub, hZ0, hmiddleMass, hsyncRet⟩ :=
        exists_synchronized_window_fine_lift_w101 hp gamma Cwork Ctw Ccell BF hd hd1
          U Uext hAne reg block loss selections Rnorm Cext Cnorm CtwNorm CcellNorm aux calls drops hfineMass
      have hfineA : selections.fineFamily ⊆ A := selections.fine_subset.trans selections.first.child_subset
      have hF0A : F0 ⊆ A := hF0fine.trans hfineA
      have hOrigin : ∀ i ∈ F0, ∃ R : {R // R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)},
          U.cover.assign block.b.val i ∈ (drops R.val R.property).Fplus ∧ (drops R.val R.property).level = trialLevel := by
        intro i hi
        have hQ : U.cover.assign block.b.val i ∈ middle0 := hmiddle0 ▸ Finset.mem_image_of_mem _ hi
        obtain ⟨_, _, R, hR, hQi, hlevel, _⟩ := hZ0 _ hQ
        exact ⟨⟨R, hR⟩, hQi, hlevel⟩
      choose chosen chosenSpec using hOrigin
      obtain ⟨Rdefault, hRdefault⟩ := calls.eligible_nonempty
      let origin := fun i => if hi : i ∈ F0 then chosen i hi else ⟨Rdefault, hRdefault⟩
      have horigin : ∀ i ∈ F0,
          U.cover.assign block.b.val i ∈ (drops (origin i).val (origin i).property).Fplus ∧
            (drops (origin i).val (origin i).property).level = trialLevel := by
        intro i hi
        have heq : origin i = chosen i hi := dif_pos hi
        exact heq.symm ▸ chosenSpec i hi
      let r := Tube.gridScale d M trialLevel.val
      let cindex := quotientGridIndexW97 M block.a.val block.b.val trialLevel.val
      let sigma := Tube.gridScale delta (M * M) cindex
      let working := Lgeom * sigma
      have hl : trialLevel.val <= M := Nat.le_of_lt_succ trialLevel.isLt
      have hsigma : sigma = theta * r :=
        (quotient_grid_index_w97 M block.a.val block.b.val hp.M_pos block.a_lt_b hb delta hd hd1).2.2.2.2 trialLevel.val hl
      obtain ⟨i0, hi0⟩ := hF0ne
      have hlevel0 : (drops (origin i0).val (origin i0).property).level.val = trialLevel.val :=
        congrArg Fin.val (horigin i0 hi0).2
      have hlow : (d : ENNReal) ^ (1 - 3 * p.ε / 2) <= (r : ENNReal) := by
        simpa only [hlevel0] using (drops (origin i0).val (origin i0).property).window_lower
      have hupp : (r : ENNReal) <= (d : ENNReal) ^ (3 * p.ε / 2) := by
        simpa only [hlevel0] using (drops (origin i0).val (origin i0).property).window_upper
      obtain ⟨hwpos, hwsmall, htwice, hwlower, ellPred, hellM, hroundLower, hroundUpper⟩ :=
        hworking hd hdWork htheta htheta1 hdtau htautheta block.block_long hlow hupp
      have hworkingEq : working = Lgeom * theta * r := by dsimp only [working]; rw [hsigma]; ring
      rw [← hworkingEq] at hwpos hwsmall htwice hwlower hroundLower hroundUpper
      have hF0Mass : 0 < ∑ i ∈ F0, volume (Ydagger i).shade :=
        (hYdagger i0 hi0).2.2.trans_le (Finset.single_le_sum (f := fun i => volume (Ydagger i).shade)
          (fun _ _ => bot_le) hi0)
      obtain ⟨Fdagger, hFne, hFF0, hgeomRet, hcanonical, hsource, hoverlap⟩ :=
        hgeometry U0 current A U Uext restriction hA reg0 reg regext block selections aux calls drops
          hd hd1.le hp.epsilon_pos hCtwNorm trialLevel F0 hF0A origin horigin Ydagger hF0Mass hwsmall.le
      have hFfine : Fdagger ⊆ selections.fineFamily := hFF0.trans hF0fine
      have hFA : Fdagger ⊆ A := hFF0.trans hF0A
      have hFcurrent : Fdagger ⊆ current.active := hFA.trans hA
      have hfineCurrent : selections.fineFamily ⊆ current.active := hfineA.trans hA
      have hfineShade : ∀ i ∈ selections.fineFamily,
          (selections.fineShading i).shade ⊆ (current.shading i).shade := by
        intro i hi
        exact (selections.fine_subshade i hi).trans
          (selections.first.child_shade i (selections.fine_subset hi)).2
      have hfineMassLe : (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) <=
          ∑ i ∈ current.active, volume (current.shading i).shade :=
        (Finset.sum_le_sum (fun i hi => measure_mono (hfineShade i hi))).trans
          (Finset.sum_le_sum_of_subset hfineCurrent)
      have hselectPay : (towerPreparationRetainedW95 delta Cselect Kselect) ^ (3 : Nat) <=
          ((loss : ENNReal) ^ (3 : Nat))⁻¹ := by
        have h := ENNReal.inv_le_inv.mpr hloss
        simp only [inv_inv] at h
        simpa only [ENNReal.inv_pow] using pow_le_pow_left' h 3
      have hfinePay : (towerPreparationRetainedW95 delta Cprep Kprep *
          (towerPreparationRetainedW95 delta Cselect Kselect) ^ (3 : Nat)) *
            (∑ i ∈ current.active, volume (current.shading i).shade) <=
              ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade := by
        calc
          _ = (towerPreparationRetainedW95 delta Cselect Kselect) ^ (3 : Nat) *
              (towerPreparationRetainedW95 delta Cprep Kprep *
                ∑ i ∈ current.active, volume (current.shading i).shade) := by ring
          _ <= ((loss : ENNReal) ^ (3 : Nat))⁻¹ *
              ∑ i ∈ A, volume (current.shading i).shade := mul_le_mul' hselectPay hprep
          _ <= _ := selections.fine_retention
      let gLoss : ENNReal := ((Dgeom + 1 : Nat) : ENNReal)⁻¹ *
        ((trialNearbyParentCountW96 CtwNorm : Nat) : ENNReal)⁻¹ * (Cdegree : ENNReal)⁻¹
      let sLoss : ENNReal := ((M + 1 : Nat) : ENNReal)⁻¹ * (1 / 2 : ENNReal) *
        trialRetainedFractionW94 d (aux.Ktr block.label)
      have hgeomConstant : (Cgeom : ENNReal)⁻¹ * trialRetainedFractionW94 d (aux.Ktr block.label) =
          gLoss * sLoss := by
        have hinv (a b : NNReal) : ((a * b : NNReal) : ENNReal)⁻¹ =
            (a : ENNReal)⁻¹ * (b : ENNReal)⁻¹ := by
          rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]
        dsimp only [Cgeom, gLoss, sLoss]
        simp only [hinv, ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one,
          Nat.cast_add, Nat.cast_one, ENNReal.coe_ofNat, one_div]
        ac_rfl
      have hretCurrent : trialRetainedFractionW94 d Kout *
          (∑ i ∈ current.active, volume (current.shading i).shade) <=
            ∑ i ∈ Fdagger, volume (Ydagger i).shade := by
        have hpaid := hmassPayment hd hdMass hdp hdsmall.le block.block_long
          (aux.Ktr block.label) (hschedules block.label block.label_active).2.2.1
        calc
          _ <= ((Cgeom : ENNReal)⁻¹ * trialRetainedFractionW94 d (aux.Ktr block.label) *
              towerPreparationRetainedW95 delta Cprep Kprep *
                (towerPreparationRetainedW95 delta Cselect Kselect) ^ (3 : Nat)) *
                  (∑ i ∈ current.active, volume (current.shading i).shade) := mul_le_mul_right' hpaid _
          _ = gLoss * (sLoss * ((towerPreparationRetainedW95 delta Cprep Kprep *
              (towerPreparationRetainedW95 delta Cselect Kselect) ^ (3 : Nat)) *
                (∑ i ∈ current.active, volume (current.shading i).shade))) := by
            rw [hgeomConstant]; ring
          _ <= gLoss * (sLoss * (∑ i ∈ selections.fineFamily,
              volume (selections.fineShading i).shade)) :=
            mul_le_mul_left' (mul_le_mul_left' hfinePay sLoss) gLoss
          _ <= gLoss * (∑ i ∈ F0, volume (Ydagger i).shade) := mul_le_mul_left' hsyncRet gLoss
          _ <= _ := hgeomRet
      have hretFine := (mul_le_mul_left' hfineMassLe (trialRetainedFractionW94 d Kout)).trans hretCurrent
      obtain ⟨c, W, Wplus, Fplus, hc, hFplusNe, hFplusSub, himage, hsupport,
        htubes, hWsupport, hWplusSupport, hWmass, hWplusMass, hWplusPos, hrawMass⟩ :=
        exists_canonical_drop_support_and_mass_w100 hd U0 current block.b
          selections.fineFamily Fdagger selections.fineShading Ydagger hfineCurrent hFfine hFne
          selections.fine_same_tube
          (fun i hi => ⟨(hYdagger i (hFF0 hi)).1.trans (selections.fine_same_tube i (hFfine hi)).symm,
            (hYdagger i (hFF0 hi)).2.1⟩)
          (fun i hi => (hYdagger i (hFF0 hi)).2.2) (trialRetainedFractionW94 d Kout) hretFine
      let parent := Uext.cover.assign cindex
      let nodeTube := fun P => (Uext.cover.tube cindex P).rescale working
      obtain ⟨nodeFamily, part, hnodeEq, hnodeNe, hcover, hdisjoint, hpart, hpartWitness⟩ :=
        exists_canonical_drop_partition_w100 U0 current block.b Fdagger hFne Fplus himage parent
          (fun i hi j hj hij => (hcanonical i hi j hj hij).2)
      obtain ⟨Zplus, hZplus, hfinalMiddleMass⟩ :=
        exists_drop_middle_recut_w101 F0 Fdagger hFF0 (U.cover.assign block.b.val) Z0 Ydagger
          selections.commonMass selections.commonMass_pos (by
            intro Q hQ
            exact hmiddleMass Q (hmiddle0 ▸ hQ))
      let middlePlus := Fdagger.image (U.cover.assign block.b.val)
      have hmiddleSub : middlePlus ⊆ middle0 := by
        rw [hmiddle0]
        exact Finset.image_subset_image hFF0
      have hmiddleFinal : ∀ Q ∈ middlePlus,
          (Zplus Q).toTube = U.cover.tube block.b.val Q ∧
          (Zplus Q).shade ⊆ (selections.secondShading Q).shade ∧
          ∃ R, ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
            Q ∈ (drops R hR).Fplus ∧ (drops R hR).level = trialLevel ∧
              (Zplus Q).shade ⊆ ((U.cover.tube block.a.val R).rescaleMap (Rnorm : Real)) ⁻¹'
                ((drops R hR).Yplus Q).shade := by
        intro Q hQ
        obtain ⟨hTube, hShade, R, hR, hmem, hlevel, hSub⟩ := hZ0 Q (hmiddleSub hQ)
        exact ⟨(hZplus Q).1.trans hTube, (hZplus Q).2.trans hShade,
          R, hR, hmem, hlevel, (hZplus Q).2.trans hSub⟩
      have hindex := (quotient_grid_index_w97 M block.a.val block.b.val hp.M_pos
        block.a_lt_b hb delta hd hd1).2.2.1 trialLevel.val hl
      have hscale : tau <= sigma := (restriction.radius block.b.val hb).le.trans
        (Tube.gridScale_antitone hd hd1.le (M * M) hindex.2.1)
      have hphysical : ∀ i ∈ Fdagger,
          (current.shading i).toConvexSpaceBody <= (Uext.cover.tube cindex (parent i)).toConvexSpaceBody := by
        intro i hi
        exact Uext.cover.le_tube_assign cindex hindex.2.2 i (hFA hi)
      have hcontain5 := canonical_drop_part_parent_containment_w100 U0 current block.b
        hd hd1.le hp.M_pos hscale Fdagger nodeFamily hFcurrent parent (Uext.cover.tube cindex)
        hphysical part (fun P hP w hw => (hpartWitness P hP w hw).1)
        Wplus (fun P hP w hw => (htubes w).2.1)
      have hcontain : ∀ P ∈ nodeFamily, ∀ w ∈ part P,
          (Wplus w).toConvexSpaceBody <= (nodeTube P).toConvexSpaceBody := by
        intro P hP w hw
        exact (hcontain5 P hP w hw).trans
          (Tube.rescale_le_rescale_of_radius_le (Uext.cover.tube cindex P)
            (mul_le_mul_of_nonneg_right hLgeom5 sigma.coe_nonneg))
      have hWtube : (fun w => (W w).toTube) = (fun w => U0.cover.tube block.b.val w.val) :=
        funext (fun w => (htubes w).1)
      have hOverlap : Tube.HasBoundedOverlap (canonicalQNodeFinsetW87 U0 current.active block.b)
          (fun w => (W w).toTube) nodeFamily nodeTube Ccan := by
        rw [hWtube, hnodeEq]
        exact fun T => (hoverlap T).trans hCcan
      have h16 : 16 * d <= r := hseparation hd hdSep hdp block.block_long hlow
      have hr1 : r <= 1 := by
        exact_mod_cast hupp.trans (ENNReal.rpow_le_one (by exact_mod_cast hdsmall.le)
          (div_nonneg (mul_nonneg (by norm_num) hp.epsilon_pos.le) (by norm_num)))
      have hNsRadius : Lns * theta * r <= working := by
        rw [hworkingEq]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 5 Lns) theta.coe_nonneg) r.coe_nonneg
      have hDensity : ∀ P ∈ nodeFamily,
          Kakeya.maxDensity (part P) (fun w => (Wplus w).toConvexSpaceBody) <=
            (d : ENNReal) ^ (p.ε * (p.η (block.label.val + 1) / 2) / 4) *
              allExactTubeNsW87 (canonicalQNodeFinsetW87 U0 current.active block.b)
                (fun w => (W w).toTube) working := by
        intro P hP
        obtain ⟨R, hR, hlevel, hcompare⟩ :=
          hdensity U0 current A U Uext hd hd1 hp.M_pos hAne hA base.ball reg0 reg regext restriction margin
            block selections aux calls drops trialLevel Fdagger nodeFamily part hFA origin
            (fun i hi => horigin i (hFF0 hi)) hnodeEq
            (fun P hP w hw => (hpartWitness P hP w hw).1) hsource P hP
        have hns := hNs hd hd1 U0 current A U Uext hp.M_pos hAne hA base.ball hcentred
          reg0 reg regext restriction margin block.a block.b block.a_lt_b R (Finset.mem_filter.mp hR).1
          (actualSecondAmbientW97 selections) (calls.normalization R hR) r h16 hr1
          (hNsRadius.trans hwsmall.le)
        have hmono := drop_all_exact_ns_mono_radius_w102
          (canonicalQNodeFinsetW87 U0 current.active block.b)
          (fun w => U0.cover.tube block.b.val w.val) hNsRadius
        have hnsFull := hns.trans (mul_le_mul_left' hmono (Cden2 : ENNReal))
        have hbody : Kakeya.maxDensity (part P) (fun w => (Wplus w).toConvexSpaceBody) =
            Kakeya.maxDensity (part P) (fun w => (U0.cover.tube block.b.val w.val).toConvexSpaceBody) := by
          apply Kakeya.maxDensity_congr
          intro w hw
          exact congrArg Tube.toConvexSpaceBody (htubes w).2.1
        rw [hbody, hWtube]
        calc
          _ <= (Cden1 : ENNReal) * (d : ENNReal) ^ (p.ε * (p.η (block.label.val + 1) / 2) / 2) *
              allExactTubeNsW87 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
                (fun Q => ((calls.normalization R hR).normalized Q).toTube) r := hcompare
          _ <= (Cden1 : ENNReal) * (d : ENNReal) ^ (p.ε * (p.η (block.label.val + 1) / 2) / 2) *
              ((Cden2 : ENNReal) * allExactTubeNsW87 (canonicalQNodeFinsetW87 U0 current.active block.b)
                (fun w => U0.cover.tube block.b.val w.val) working) := mul_le_mul_left' hnsFull _
          _ = ((Cden1 * Cden2 : NNReal) : ENNReal) *
              (d : ENNReal) ^ (p.ε * (p.η (block.label.val + 1) / 2) / 2) *
                allExactTubeNsW87 (canonicalQNodeFinsetW87 U0 current.active block.b)
                  (fun w => U0.cover.tube block.b.val w.val) working := by rw [ENNReal.coe_mul]; ring
          _ <= _ := mul_le_mul_right'
            (hpayDensity hd hdDensity hdp hdsmall.le block.block_long block.label block.label_active) _
      let raw : LiteralInnerDropOutputW87 U0 block.b W nodeFamily nodeTube part d p.ε
          (p.η (block.label.val + 1) / 2) Kout :=
        { FPlus := Fplus
          YPlus := Wplus
          FPlus_nonempty := hFplusNe
          FPlus_subset := hFplusSub
          middle_same_tube := fun w => (htubes w).1
          subshading := fun w hw => ⟨(htubes w).2.1.trans (htubes w).1.symm, (htubes w).2.2⟩
          assigned_cover := hcover
          assigned_disjoint := hdisjoint
          part_subset := fun P hP => (hpart P hP).1
          part_parent_containment := hcontain
          parent_boundedOverlap := hOverlap
          member_twice_le_working := htwice
          per_cell_density_drop := hDensity
          Ktr_pos := Nat.zero_lt_of_lt hKout
          mass_retention := hrawMass }
      have hYcurrent : ∀ i ∈ Fdagger, (Ydagger i).toTube = (current.shading i).toTube ∧
          (Ydagger i).shade ⊆ (current.shading i).shade := by
        intro i hi
        exact ⟨(hYdagger i (hFF0 hi)).1,
          (hYdagger i (hFF0 hi)).2.1.trans (hfineShade i (hFfine hi))⟩
      have hpaidFinal := hprofile hd hdProfile hdd hdsmall block.block_long current U0 block.b ellPred
        block.label block.label_active raw hroundLower hroundUpper Fdagger Ydagger hFne hFcurrent
        hYcurrent himage hretCurrent
      exact ⟨drops, working, trialLevel, ellPred, nodeFamily, middlePlus, Fdagger, nodeTube,
        part, W, raw, Zplus, Ydagger, c, hwpos, hwsmall.le, hellM, hroundLower, hroundUpper,
        hwlower, hworkingEq.le, hFne, hFfine,
        (fun i hi => ⟨(hYdagger i (hFF0 hi)).1, (hYdagger i (hFF0 hi)).2.1⟩), rfl,
        hmiddleSub.trans hmiddle0Sub, hmiddleFinal, hfinalMiddleMass, himage, hsupport, hc,
        hWmass, (fun w hw => hWplusMass w), hWsupport, (fun w hw => hWplusSupport w),
        hretCurrent, hpaidFinal⟩

end



end Kakeya.ml1Boot.TrialRestartW94

