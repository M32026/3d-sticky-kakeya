module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.PaidRetainedStateW100

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

/-- Actual raw assigned geometry, its canonical image, and its retained fine
mass yield the paid decrement of the fixed original canonical profile. -/
theorem exists_paid_drop_transition_of_raw_w101
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (Ccan : NNReal) (hCcan : 1 <= Ccan)
    (CM Kout : Nat) (hKout : 1 <= Kout) (Cpass : NNReal) (hCpass : 1 <= Cpass) :
    ∃ delta0 : NNReal, 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta d working : NNReal}, 0 < delta -> delta < delta0 ->
      delta <= d -> d < 1 -> d <= delta ^ p.ε ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {B : Finset iota} {V : iota -> ShadedTube delta E}
        (current : RetainedStateW94 B V)
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
        (q ellPred : Fin (M + 1)) (m : Fin (p.N + 1)),
        m.val < p.N ->
      ∀ {W : CanonicalQNodeW87 U0 current.active q ->
          ShadedTube (Tube.gridScale delta M q.val) E}
        {nodeFamily : Finset iota} {nodeTube : iota -> Tube working E}
        {part : iota -> Finset (CanonicalQNodeW87 U0 current.active q)}
        (raw : LiteralInnerDropOutputW87 U0 q W nodeFamily nodeTube part d p.ε
          (p.η (m.val + 1) / 2) Kout),
        Tube.gridScale delta M (ellPred.val + 1) <= working ->
        working < Tube.gridScale delta M ellPred.val ->
      ∀ (Fdagger : Finset iota) (Ydagger : iota -> ShadedTube delta E),
        Fdagger.Nonempty -> Fdagger ⊆ current.active ->
        (∀ i ∈ Fdagger, (Ydagger i).toTube = (current.shading i).toTube ∧
          (Ydagger i).shade ⊆ (current.shading i).shade) ->
        Fdagger.image (U0.cover.assign q.val) = raw.FPlus.image Subtype.val ->
        trialRetainedFractionW94 d Kout *
          (∑ i ∈ current.active, volume (current.shading i).shade) <=
            ∑ i ∈ Fdagger, volume (Ydagger i).shade ->
        ∃ (next : RetainedStateW94 B V)
          (step : PaidDropTransitionW94 U0 current next CM Cpass (sourceFlatDropW95 p)),
          step.trialScale = d ∧ step.Ktr = Kout ∧
          step.daggerFamily = Fdagger ∧ step.Ydagger = Ydagger ∧
          step.drop_q = q ∧ step.drop_ell = ellPred ∧
          current.retained / uniformPaidPassCostW95 delta M CM Kout Cpass <= next.retained := by
  let pClip : Params := { p with η := fun n => p.η (min n p.N) }
  let P : RevisedProfileParametersW87 pClip :=
    { M := M
      CM := 1
      canonicalC := Ccan
      M_pos := hp.M_pos
      CM_pos := by norm_num
      canonicalC_one := hCcan
      epsilon_pos := hp.epsilon_pos
      zeta0_pos := by simpa [pClip] using hp.zeta_pos 0 (Nat.zero_le p.N)
      zeta_mono := by
        intro k l hkl
        exact hp.zeta_mono _ _ (min_le_min_right p.N hkl) (min_le_right _ _)
      reciprocal_M_small := by simpa [pClip] using hp.M_profile }
  have hflat : sourceCFlatW87 pClip = sourceFlatDropW95 p := by
    simp [sourceCFlatW87, sourceFlatDropW95, pClip]
  obtain ⟨delta0, hdelta0, hdelta01, habsorb⟩ := exists_deltaProfileAbsorb_w87 P
  refine ⟨delta0, hdelta0, hdelta01, ?_⟩
  intro delta d working hdelta hsmall hdd hd1 hdscale iota inst B V current U0
    q ellPred m hm W nodeFamily nodeTube part raw hroundLower hround Fdagger
    Ydagger hFne hFsub hY himage hmass
  have hdelta1 : delta < 1 := hsmall.trans hdelta01
  have hdp : 0 < d := hdelta.trans_le hdd
  have hzetaNext : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
  have hzeta : p.η 0 <= p.η (m.val + 1) / 2 := by
    have hmono := hp.zeta_mono 0 m.val (Nat.zero_le _) (by omega)
    have hrung := hp.rung_next m.val hm
    have heps := hp.epsilon_small
    nlinarith
  have hcoefficient : canonicalComparisonFactorW87 P delta d (p.η (m.val + 1) / 2) <=
      (delta : Real) ^ sourceFlatDropW95 p := by
    rw [← hflat]
    apply habsorb delta hdelta hsmall.le d (p.η (m.val + 1) / 2) hdp hd1.le
    · exact_mod_cast hdscale
    · simpa [pClip] using hzeta
  let Sat := saturatedFineLiftW87 U0 current.active q (canonicalQNodeValuesW87 raw.FPlus)
  have hFsat : Fdagger ⊆ Sat := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨hFsub hi, ?_⟩
    change U0.cover.assign q.val i ∈ raw.FPlus.image Subtype.val
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hraw := raw_literalCanonicalD_drop_w87 P U0 q ellPred
    (p.η (m.val + 1) / 2) raw hdim hdelta hdelta1 hdp hd1.le
    (mul_nonneg hp.epsilon_pos.le (div_nonneg hzetaNext.le (by norm_num)))
    current.active_subset (next := Sat) rfl hroundLower hround
  have hDdrop : literalCanonicalDW87 U0 Fdagger q ellPred <=
      ENNReal.ofReal ((delta : Real) ^ sourceFlatDropW95 p) *
        literalCanonicalDW87 U0 current.active q ellPred :=
    ((literalCanonicalD_mono_w87 U0 hFsat q ellPred).trans hraw).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hcoefficient) _)
  have htauEll : Tube.gridScale delta M q.val <= Tube.gridScale delta M ellPred.val := by
    have hmember := raw.member_twice_le_working
    linarith [show (0 : NNReal) <= Tube.gridScale delta M q.val from by positivity]
  have hafter1 : 1 <= literalCanonicalDW87 U0 Fdagger q ellPred :=
    one_le_allExactTubeNs_of_nonempty_w87 (fun w => U0.cover.tube q.val w)
      (hFne.image (U0.cover.assign q.val)) (Tube.gridScale_pos hdelta M q.val)
      (Tube.gridScale_le_one hdelta1.le M q.val) htauEll
  have hbefore1 : 1 <= literalCanonicalDW87 U0 current.active q ellPred :=
    hafter1.trans (literalCanonicalD_mono_w87 U0 hFsub q ellPred)
  have hmax := max_one_literalCanonicalD_drop_w87 U0 q ellPred
    (sourceFlatDropW95 p) hbefore1 hafter1 hDdrop
  have hprofile : literalProfileCoordW87 U0 Fdagger q ellPred + sourceFlatDropW95 p <=
      literalProfileCoordW87 U0 current.active q ellPred := by
    have hdeltaR : (0 : Real) < delta := hdelta
    have hdeltaR1 : (delta : Real) < 1 := hdelta1
    have hbeforePos : 0 < max 1 (literalCanonicalDW87 U0 current.active q ellPred).toReal :=
      zero_lt_one.trans_le (le_max_left _ _)
    have hafterPos : 0 < max 1 (literalCanonicalDW87 U0 Fdagger q ellPred).toReal :=
      zero_lt_one.trans_le (le_max_left _ _)
    have hlog := Real.log_le_log hafterPos hmax
    rw [Real.log_mul (Real.rpow_pos_of_pos hdeltaR _).ne' hbeforePos.ne',
      Real.log_rpow hdeltaR] at hlog
    have hbase : Real.log ((delta : Real) ^ (-1 : Real)) = -Real.log (delta : Real) := by
      rw [Real.log_rpow hdeltaR]
      ring
    have hlogPos : 0 < Real.log ((delta : Real) ^ (-1 : Real)) := by
      rw [Real.rpow_neg_one]
      exact Real.log_pos ((one_lt_inv₀ hdeltaR).mpr hdeltaR1)
    have hnum :
        Real.log (max 1 (literalCanonicalDW87 U0 Fdagger q ellPred).toReal) +
            sourceFlatDropW95 p * Real.log ((delta : Real) ^ (-1 : Real)) <=
          Real.log (max 1 (literalCanonicalDW87 U0 current.active q ellPred).toReal) := by
      rw [hbase]
      nlinarith
    unfold literalProfileCoordW87
    calc
      _ = (Real.log (max 1 (literalCanonicalDW87 U0 Fdagger q ellPred).toReal) +
          sourceFlatDropW95 p * Real.log ((delta : Real) ^ (-1 : Real))) /
            Real.log ((delta : Real) ^ (-1 : Real)) := by
        rw [add_div, mul_div_cancel_right₀ _ hlogPos.ne']
      _ <= _ := div_le_div_of_nonneg_right hnum hlogPos.le
  obtain ⟨next, hactive, hshade, hretained, hnextsub, hnextshade, hselector, huniform⟩ :=
    exists_paid_retained_state_from_trial_lift_w100 current hdelta hdd hd1 M CM Kout
      Cpass hCpass Fdagger Ydagger hFne hFsub hY hmass
  let step : PaidDropTransitionW94 U0 current next CM Cpass (sourceFlatDropW95 p) :=
    { trialScale := d
      trialScale_lower := hdd
      trialScale_lt_one := hd1
      Ktr := Kout
      Ktr_pos := hKout
      daggerFamily := Fdagger
      Ydagger := Ydagger
      dagger_subset := hFsub
      dagger_same_tube := fun i hi => (hY i hi).1
      dagger_subshade := fun i hi => (hY i hi).2
      prior_trial_retention := hmass
      next_subset := hnextsub
      next_subshade := hnextshade
      selector_retention := hselector
      coefficient_paid := hretained.ge
      drop_q := q
      drop_ell := ellPred
      profile_drop := by simpa only [persistentProfileW94, hactive] using hprofile }
  exact ⟨next, step, rfl, rfl, rfl, rfl, rfl, rfl, huniform⟩

end

end Kakeya.ml1Boot.TrialRestartW94
