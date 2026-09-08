module

public import Kakeya.Bootstrap
public import Kakeya.FrostmanTransfer
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceSameMassOuterFullnessW100
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourcePassNumericsConstructionW104
public import Kakeya.DimensionThree.MainLemma1.CaseOne
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceQuotientGridW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceTerminalOriginalInputW104
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCentringReductionProofW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringBandTransportW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringBandDensityW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ProtectedLineBudgetW103
public import Kakeya.DimensionThree.FrostmanEstimateOne
public import Kakeya.Tube.EssentiallyDistinctShadeSelection

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter
open scoped ENNReal NNReal Topology

namespace Kakeya.ml1Boot.RevisedSourceRepairW110

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open TrialRestartW94

/-- A genuine sticky theorem witness, selected before the ladder and gamma. -/
structure StickyWitnessW110 (E : Type uE) [NormedAddCommGroup E]
    [InnerProductSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] (gammaZero : Real) where
  etaStar : Real
  etaStar_pos : 0 < etaStar
  actual_sticky :
    ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
      ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
        (∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (s : Set iota).Pairwise
          (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ->
        ∀ {C : NNReal}, C <= ShadedTube.ssfUniformConst (Module.finrank Real E) ->
        ∀ U : ShadedTube.ShadedUniformTubeSet s Y (Tube.ssfGridLen delta) C,
          (delta : ENNReal) ^ etaStar <=
            (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ENNReal) ->
          U.tubeUniform.IsFrostmanAtEveryScale ((delta : ENNReal) ^ (-etaStar)) ->
          (delta : ENNReal) ^ (gammaZero / 4) <= volume (⋃ i ∈ s, (Y i).shade)

theorem exists_sticky_witness_w110
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{uE, uI} (E := E))
    {gammaZero : Real} (hgammaZero : 0 < gammaZero) :
    Nonempty (StickyWitnessW110.{uE, uI} E gammaZero) := by
  obtain ⟨eta, heta, hactual⟩ :=
    StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale (E := E) hSFE
      (show 0 < gammaZero / 4 by positivity)
  refine ⟨{ etaStar := eta, etaStar_pos := heta, actual_sticky := ?_ }⟩
  filter_upwards [hactual] with delta hdelta
  intro iota s Y hball hED C hC U hfull hCF
  apply hdelta s Y hball hED hC U _ hCF
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.coe_rpow_of_nonneg _ heta.le] using hfull

/-- The existing Params type is only a carrier of N, epsilon and zeta.
This package does NOT assert Params.Spec or certify p.etaGamma. The source
ladder inequalities and the source step replace those claims explicitly. -/
structure SourceStructureW110 (beta gammaZero etaStar : Real) where
  p : Params
  xi : Fin (p.N + 1) -> Real
  xiMin : Real
  M : Nat
  numerics : SourcePassNumericsW95 p (betaPrime beta gammaZero) gammaZero xi xiMin M
  etaStar_eq : p.ηStar = etaStar
  sticky_margin : 5 * p.ε <= etaStar / 4
  step_eq : p.c = min (min xiMin (gammaZero / 4))
    ((gammaZero - betaPrime beta gammaZero) / 2)

/-- Choose all structural data before gamma, hKT, hKF and requested loss.
The shifted beta is fixed at gammaZero, covering the public beta = 0 case. -/
theorem exists_source_structure_w110
    {beta gammaZero etaStar : Real} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1) (hetaStar : 0 < etaStar) :
    Nonempty (SourceStructureW110 beta gammaZero etaStar) := by
  have hgammaPos : 0 < gammaZero := hbeta.trans_lt hgammaZero.1
  have hbp : 0 < betaPrime beta gammaZero :=
    (half_pos hgammaPos).trans_le (le_max_right _ _)
  have hbpGap : betaPrime beta gammaZero < gammaZero :=
    max_lt hgammaZero.1 (half_lt_self hgammaPos)
  obtain ⟨p, xi, xiMin, M, hp, heps⟩ :=
    exists_source_pass_numerics_w104 hbp hbpGap hgammaZero.2
      (show 0 < etaStar / 20 by positivity)
  let p' : Params := { p with
    ηStar := etaStar
    c := min (min xiMin (gammaZero / 4)) ((gammaZero - betaPrime beta gammaZero) / 2) }
  refine ⟨{
    p := p'
    xi := xi
    xiMin := xiMin
    M := M
    numerics := ?_
    etaStar_eq := rfl
    sticky_margin := ?_
    step_eq := rfl }⟩
  · exact {
      beta_pos := hp.beta_pos
      gammaZero_gt := hp.gammaZero_gt
      gammaZero_le := hp.gammaZero_le
      N_large := hp.N_large
      epsilon_eq := hp.epsilon_eq
      epsilon_pos := hp.epsilon_pos
      epsilon_small := hp.epsilon_small
      gap := hp.gap
      zeta_pos := hp.zeta_pos
      zeta_mono := hp.zeta_mono
      zeta_top := hp.zeta_top
      xi_pos := hp.xi_pos
      xi_beta := hp.xi_beta
      xi_next := hp.xi_next
      rung_next := hp.rung_next
      rung_xi := hp.rung_xi
      xiMin_pos := hp.xiMin_pos
      xiMin_lower := hp.xiMin_lower
      xiMin_attained := hp.xiMin_attained
      M_pos := hp.M_pos
      M_zeta := hp.M_zeta
      M_xi := hp.M_xi
      M_profile := hp.M_profile
      M_next := hp.M_next }
  · change 5 * p.ε <= etaStar / 4
    linarith only [heps]

theorem shifted_estimate_for_source_w110 [Nontrivial E]
    {beta gammaZero : Real} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (hKT : KatzTaoEstimate.{uI} E beta) :
    0 < betaPrime beta gammaZero ∧ betaPrime beta gammaZero < gammaZero ∧
      KatzTaoEstimate.{uI} E (betaPrime beta gammaZero) := by
  have hgammaPos : 0 < gammaZero := hbeta.trans_lt hgammaZero.1
  exact ⟨(half_pos hgammaPos).trans_le (le_max_right _ _),
    max_lt hgammaZero.1 (half_lt_self hgammaPos), hKT.mono (le_max_left _ _)⟩

theorem source_step_positive_w110
    {beta gammaZero etaStar : Real} (G : SourceStructureW110 beta gammaZero etaStar) :
    0 < G.p.c ∧ G.p.c <= 1 ∧ G.p.c <= gammaZero / 4 ∧
      G.p.c <= G.xiMin ∧ G.p.c < gammaZero - betaPrime beta gammaZero := by
  have hgammaPos : 0 < gammaZero := G.numerics.beta_pos.trans G.numerics.gammaZero_gt
  have hgap : 0 < gammaZero - betaPrime beta gammaZero := sub_pos.mpr G.numerics.gammaZero_gt
  rw [G.step_eq]
  have hx : min (min G.xiMin (gammaZero / 4))
      ((gammaZero - betaPrime beta gammaZero) / 2) <= min G.xiMin (gammaZero / 4) :=
    min_le_left _ _
  have hg := hx.trans (min_le_right _ _)
  refine ⟨lt_min (lt_min G.numerics.xiMin_pos (by positivity)) (half_pos hgap),
    hg.trans ?_, hg, hx.trans (min_le_left _ _), ?_⟩
  · linarith only [G.numerics.gammaZero_le]
  · exact (min_le_right _ _).trans_lt (half_lt_self hgap)

/-- The full family-uniform KT conclusion at the returned threshold.
The all-indices ball condition is exactly the production lemma's condition. -/
def ActualKTThresholdW110 (beta loss eta : Real) : Prop :=
  ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
    ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
      (∀ i, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
      (delta : Real) ^ eta <=
        (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : Real) ->
      ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
        (delta : ENNReal) ^ (-loss) *
          (Kakeya.maxDensity s (fun i => (Y i).toConvexSpaceBody)) ^ (1 - beta) *
          (s.card : ENNReal) ^ beta

/-- The actual auxiliary-scale KF conclusion, including CF of this family.
eta and the reference-scale cutoff precede rho and the family. -/
def ActualKFThresholdW110 (gamma loss eta : Real) : Prop :=
  ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
    ∀ rho : NNReal, delta <= rho -> rho <= 1 ->
    ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube rho E),
      s.Nonempty ->
      (∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
      (s : Set iota).Pairwise
        (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ->
      (delta : ENNReal) ^ eta <=
        (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ENNReal) ->
      ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
        (delta : ENNReal) ^ (-loss) *
          frostmanConstIn s (fun i => (Y i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall ^ (1 - gamma / 2) *
          (rho : ENNReal) ^ (-2 * gamma) *
          ((s.card : ENNReal) * (rho : ENNReal) ^
            (Module.finrank Real E - 1)) ^ (1 - gamma / 2)

/-- Full analytic witnesses, not positive functions standing for witnesses.
The geometry constants are parameters: they precede every threshold. -/
structure AnalyticScheduleW110 [Nontrivial E]
    {beta gammaZero etaStar : Real} (G : SourceStructureW110 beta gammaZero etaStar)
    (gamma : Real) (Ctw Ccell : NNReal) where
  etaKT : Real
  etaKF : Real
  etaKT_pos : 0 < etaKT
  etaKF_pos : 0 < etaKF
  actual_KT : ActualKTThresholdW110.{uE, uI} (E := E)
    (betaPrime beta gammaZero) (G.p.η 0) etaKT
  actual_KF : ActualKFThresholdW110.{uE, uI} (E := E) gamma (G.p.η 0) etaKF
  inner : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E)
    G.p G.xi gamma Ctw Ccell G.M
  auxiliary : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E)
    G.p G.xi gamma Ctw Ccell G.M
  inner_window : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma G.p.ε (G.xi m)
      (G.p.η (m.val + 1)) Ctw Ccell G.M
      (inner.inner m) (inner.cutoff m) (inner.Ktr m)
  auxiliary_window : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    windowDetailedTrialAtThresholdW98.{uE, uI} (E := E) gamma G.p.ε (G.xi m)
      (G.p.η (m.val + 1) / 2) Ctw Ccell G.M
      (auxiliary.inner m) (auxiliary.cutoff m) (auxiliary.Ktr m)

/-- Package the proved window-aware trial at both rung choices and the
actual KT/KF witnesses. The new packaging proof remains an obligation. -/
theorem exists_actual_analytic_schedule_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero etaStar : Real} (G : SourceStructureW110 beta gammaZero etaStar)
    {gamma : Real} (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    (Ctw Ccell : NNReal) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell) :
    Nonempty (AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell) := by
  classical
  let p := G.p
  let betaS := betaPrime beta gammaZero
  let xi := G.xi
  let M := G.M
  have hp : SourcePassNumericsW95 p betaS gammaZero xi G.xiMin M := G.numerics
  have hKT' : KatzTaoEstimate.{uI} E betaS := hKT.mono (le_max_left _ _)
  have hbetagamma : betaS < gamma := hp.gammaZero_gt.trans_le hgamma.1
  have hgap : 3 * p.ε / 2 <= (gamma - betaS) / 1000 := by
    linarith only [hp.gap, hgamma.1]
  have heps32 : 32 * p.ε <= 1 := by
    linarith only [hp.gap, hp.gammaZero_le, hp.beta_pos]
  have heps1 : p.ε <= 1 := hp.epsilon_small.le.trans (by norm_num)
  have hMpos : (0 : Real) < M := by exact_mod_cast hp.M_pos
  have hdenom : 0 < p.ε ^ 2 * betaS := mul_pos (sq_pos_of_pos hp.epsilon_pos) hp.beta_pos
  have hnext : ∀ m : Fin (p.N + 1), m.val < p.N ->
      4000 * xi m / (p.ε ^ 2 * betaS) <= p.η (m.val + 1) / 2 := by
    intro m hm
    apply (div_le_iff₀ hdenom).mpr
    nlinarith only [hp.xi_next m hm]
  have hMmin : ∀ m : Fin (p.N + 1), m.val < p.N ->
      (1 : Real) / M <= min (xi m) p.ε / 100 := by
    intro m hm
    have hxiMin1 : G.xiMin <= 1 := by
      obtain ⟨k, hk, hkMin⟩ := hp.xiMin_attained
      have hbeta1 : betaS <= 1 := hp.gammaZero_gt.le.trans hp.gammaZero_le
      have heps3 : p.ε ^ 3 <= 1 := pow_le_one₀ hp.epsilon_pos.le heps1
      have hprod : p.ε ^ 3 * betaS <= 1 := mul_le_one₀ heps3 hp.beta_pos.le hbeta1
      rw [← hkMin]
      nlinarith only [hp.xi_beta k hk, hprod]
    have hleft : p.ε * G.xiMin / 200 <= xi m / 100 := by
      have hprod : p.ε * G.xiMin <= G.xiMin :=
        mul_le_of_le_one_left hp.xiMin_pos.le heps1
      linarith only [hprod, hp.xiMin_lower m hm, hp.xi_pos m hm]
    have hright : p.ε * G.xiMin / 200 <= p.ε / 100 := by
      have hprod : p.ε * G.xiMin <= p.ε :=
        mul_le_of_le_one_right hp.epsilon_pos.le hxiMin1
      linarith only [hprod, hp.epsilon_pos]
    rw [← min_div_div_right (by norm_num : (0 : Real) <= 100)]
    exact le_min (hp.M_xi.trans hleft) (hp.M_xi.trans hright)
  have hMhalf : ∀ m : Fin (p.N + 1), m.val < p.N ->
      (160000 : Real) / (p.ε * (p.η (m.val + 1) / 2)) <= M := by
    intro m hm
    have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
    have hzero : p.η 0 <= p.ε * p.η (m.val + 1) / 100 :=
      (hp.zeta_mono 0 m.val (Nat.zero_le _) (by omega)).trans (hp.rung_next m.val hm)
    have hmul := mul_le_mul_of_nonneg_left hzero hp.epsilon_pos.le
    have hmargin := mul_le_mul_of_nonneg_right heps32 (mul_nonneg hp.epsilon_pos.le hz.le)
    have hsmall : (1 : Real) / M <= p.ε * p.η (m.val + 1) / 320000 := by
      nlinarith only [hp.M_zeta, hmul, hmargin]
    apply (div_le_iff₀ (mul_pos hp.epsilon_pos (half_pos hz))).mpr
    have hsmall' := (div_le_iff₀ hMpos).mp hsmall
    nlinarith only [hsmall']
  have hlabels : ∀ (half : Bool) (m : Fin (p.N + 1)),
      ∃ (inner : Real) (cutoff : NNReal) (Ktr : Nat),
        0 < inner ∧ 0 < cutoff ∧ cutoff < 1 ∧ 1 <= Ktr ∧
        (m.val < p.N -> windowDetailedTrialAtThresholdW98.{uE, uI} (E := E)
          gamma p.ε (xi m) (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1))
          Ctw Ccell M inner cutoff Ktr) := by
    intro half m
    by_cases hm : m.val < p.N
    · have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
      have hzlower : p.η (m.val + 1) / 2 <=
          (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1)) := by
        cases half <;> simp only [Bool.false_eq_true, reduceIte] <;> linarith only [hz]
      have hzpos := (half_pos hz).trans_le hzlower
      have hscale : (160000 : Real) /
          (p.ε * (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1))) <= M :=
        (div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hp.epsilon_pos (half_pos hz))
          (mul_le_mul_of_nonneg_left hzlower hp.epsilon_pos.le)).trans (hMhalf m hm)
      obtain ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, htrial⟩ :=
        exists_literal_window_trial_threshold_w98 hdim betaS gamma p.ε (xi m)
          (if half then p.η (m.val + 1) / 2 else p.η (m.val + 1))
          hp.beta_pos hbetagamma hgamma.2 hp.epsilon_pos hp.epsilon_small hgap
          (hp.xi_pos m hm) (hp.xi_beta m hm) ((hnext m hm).trans hzlower)
          Ctw Ccell hCtw hCcell M hp.M_pos (hMmin m hm) hscale hKT' hKF
      exact ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, fun _ => htrial⟩
    · exact ⟨1, 1 / 2, 1, by norm_num, by norm_num, by norm_num, le_rfl,
        fun hm' => (hm hm').elim⟩
  choose inner cutoff Ktr hinner hcutoff hcutoff1 hKtr htrial using hlabels
  let full : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E)
      p xi gamma Ctw Ccell M :=
    { inner := inner false, cutoff := cutoff false, Ktr := Ktr false,
      inner_pos := hinner false, cutoff_pos := hcutoff false,
      cutoff_lt_one := hcutoff1 false, Ktr_pos := hKtr false,
      actual_trial := by
        intro m hm d hd hd0 iota inst F Y rho cells input
        rcases htrial false m hm hd hd0 F Y rho cells input with hg | hd
        · exact Or.inl hg
        · exact Or.inr (hd.map fun drop => drop.toDetailedTrialDropW94) }
  let aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E)
      p xi gamma Ctw Ccell M :=
    { inner := inner true, cutoff := cutoff true, Ktr := Ktr true,
      inner_pos := hinner true, cutoff_pos := hcutoff true,
      cutoff_lt_one := hcutoff1 true, Ktr_pos := hKtr true,
      actual_trial := by
        intro m hm d hd hd0 iota inst F Y rho cells input
        rcases htrial true m hm hd hd0 F Y rho cells input with hg | hd
        · exact Or.inl hg
        · exact Or.inr (hd.map fun drop => drop.toDetailedTrialDropW94) }
  have heta : 0 < p.η 0 := hp.zeta_pos 0 (Nat.zero_le _)
  obtain ⟨etaKT, hetaKT, hactualKT⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize (E := E) hp.beta_pos.le hKT' (p.η 0) heta
  obtain ⟨etaKF, hetaKF, hactualKF⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale E
      (hp.beta_pos.trans hbetagamma).le hgamma.2 (by rw [hdim]; norm_num) hKF (p.η 0) heta
  refine ⟨{
    etaKT := etaKT
    etaKF := etaKF
    etaKT_pos := hetaKT
    etaKF_pos := hetaKF
    actual_KT := ?_
    actual_KF := hactualKF
    inner := full
    auxiliary := aux
    inner_window := ?_
    auxiliary_window := ?_ }⟩
  · filter_upwards [hactualKT, self_mem_nhdsWithin] with delta hdelta hd
    intro iota s Y hball hfull
    exact hdelta delta hd le_rfl s Y hball (by exact_mod_cast hfull)
  · intro m hm
    exact htrial false m hm
  · intro m hm
    exact htrial true m hm

/-- The working exponent, then the public input exponent, are selected
after the actual schedule. Extra smallness reserves pay initial banding,
finite restarts and the requested final loss; they are outputs, not inputs. -/
structure InputChoiceW110 [Nontrivial E]
    {beta gammaZero etaStar gamma : Real}
    {G : SourceStructureW110 beta gammaZero etaStar} {Ctw Ccell : NNReal}
    (A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell)
    (accuracy : Real) where
  workingEta : Real
  inputEta : Real
  working_pos : 0 < workingEta
  input_pos : 0 < inputEta
  input_eq : inputEta = workingEta / 8
  ladder_reserve : workingEta <= G.p.η 0 / 1000
  sticky_reserve : workingEta <= etaStar / 10
  inner_reserve : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    workingEta <= G.p.ε * min (A.inner.inner m) (A.auxiliary.inner m) / 1000
  gain_reserve : workingEta <= G.p.ε * G.xiMin / 1000
  cf_reserve : ∀ m : Fin (G.p.N + 1), m.val < G.p.N ->
    workingEta <= G.p.ε * G.xi m / 160000
  KT_reserve : workingEta <= A.etaKT / 1000
  KF_reserve : workingEta <= A.etaKF / 1000
  requested_loss_reserve : workingEta <= accuracy / 1000
  unit_reserve : workingEta <= 1 / 1000

theorem exists_input_choice_w110 [Nontrivial E]
    {beta gammaZero etaStar gamma : Real}
    {G : SourceStructureW110 beta gammaZero etaStar} {Ctw Ccell : NNReal}
    (A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell)
    {accuracy : Real} (haccuracy : 0 < accuracy) :
    Nonempty (InputChoiceW110 A accuracy) := by
  classical
  have hp := G.numerics
  have heta : 0 < G.p.η 0 := hp.zeta_pos 0 (Nat.zero_le _)
  have hepsilon := hp.epsilon_pos
  have hxiMin := hp.xiMin_pos
  have hsticky : 0 < etaStar := by
    have hm := G.sticky_margin
    have he := hp.epsilon_pos
    linarith only [hm, he]
  let fixed : Real := min (G.p.η 0 / 1000) (min (etaStar / 10)
    (min (G.p.ε * G.xiMin / 1000) (min (G.p.ε * G.xiMin / 160000)
      (min (A.etaKT / 1000) (min (A.etaKF / 1000)
        (min (accuracy / 1000) (1 / 1000)))))))
  have hfixed : 0 < fixed := by
    dsimp only [fixed]
    exact lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min (by positivity)
        (lt_min (div_pos A.etaKT_pos (by norm_num))
          (lt_min (div_pos A.etaKF_pos (by norm_num))
            (lt_min (by positivity) (by norm_num)))))))
  let budget : Fin (G.p.N + 1) -> Real := fun m =>
    min fixed (G.p.ε * min (A.inner.inner m) (A.auxiliary.inner m) / 1000)
  have hbudget : ∀ m, 0 < budget m := by
    intro m
    exact lt_min hfixed (div_pos (mul_pos hp.epsilon_pos
      (lt_min (A.inner.inner_pos m) (A.auxiliary.inner_pos m))) (by norm_num))
  obtain ⟨m0, hm0, hmin⟩ := Finset.exists_min_image Finset.univ budget Finset.univ_nonempty
  let e := budget m0
  have he : 0 < e := hbudget m0
  have hbound : e <= fixed := min_le_left _ _
  have hbounds : e <= G.p.η 0 / 1000 ∧ e <= etaStar / 10 ∧
      e <= G.p.ε * G.xiMin / 1000 ∧ e <= G.p.ε * G.xiMin / 160000 ∧
      e <= A.etaKT / 1000 ∧ e <= A.etaKF / 1000 ∧
      e <= accuracy / 1000 ∧ e <= 1 / 1000 := by
    simpa only [fixed, le_min_iff] using hbound
  refine ⟨{
    workingEta := e
    inputEta := e / 8
    working_pos := he
    input_pos := by positivity
    input_eq := rfl
    ladder_reserve := hbounds.1
    sticky_reserve := hbounds.2.1
    inner_reserve := ?_
    gain_reserve := hbounds.2.2.1
    cf_reserve := ?_
    KT_reserve := hbounds.2.2.2.2.1
    KF_reserve := hbounds.2.2.2.2.2.1
    requested_loss_reserve := hbounds.2.2.2.2.2.2.1
    unit_reserve := hbounds.2.2.2.2.2.2.2 }⟩
  · intro m hm
    exact (hmin m (Finset.mem_univ m)).trans (min_le_right _ _)
  · intro m hm
    exact hbounds.2.2.2.1.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hp.xiMin_lower m hm) hp.epsilon_pos.le) (by norm_num))

/-- Exactly the family hypotheses of FrostmanEstimate at one input exponent. -/
structure OriginalInputW110 {iota : Type uI} {delta : NNReal}
    (s : Finset iota) (Y : iota -> ShadedTube delta E) (eta : Real) : Prop where
  ball : ∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1
  essentially_distinct : (s : Set iota).Pairwise
    (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier)
  frostman : IsFrostmanIn s (fun i => (Y i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall ((delta : ENNReal) ^ (-eta))
  fullness : (delta : ENNReal) ^ eta <=
    (ShadedBody.fullness s (fun i => (Y i).toShadedBody) : ENNReal)

/-- The existing banding conclusion, with its paid original shaded-mass
share exposed. -/
structure BandedInputW110 {iota : Type uI} {delta : NNReal}
    (s : Finset iota) (Y : iota -> ShadedTube delta E) (workingEta : Real) where
  s2 : Finset iota
  subset : s2 ⊆ s
  nonempty : s2.Nonempty
  hereditary_fullness : ∀ t ⊆ s2, t.Nonempty ->
    (delta : ENNReal) ^ workingEta <=
      (ShadedBody.fullness t (fun i => (Y i).toShadedBody) : ENNReal)
  frostman : frostmanConstIn s2 (fun i => (Y i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-workingEta)
  uniform : Tube.UniformTubeSet s2 (fun i => (Y i).toTube) (Tube.ssfGridLen delta)
    (Tube.uniformConst (Module.finrank Real E))
  original_mass_retention :
    (delta : ENNReal) ^ workingEta * (∑ i ∈ s, volume (Y i).shade) <=
      ∑ i ∈ s2, volume (Y i).shade

theorem band_at_selected_working_exponent_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero etaStar gamma : Real}
    {G : SourceStructureW110 beta gammaZero etaStar} {Ctw Ccell : NNReal}
    {A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell}
    {accuracy : Real} (I : InputChoiceW110 A accuracy) :
    ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
      ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
        OriginalInputW110 s Y I.inputEta ->
        Nonempty (BandedInputW110 s Y I.workingEta) := by
  classical
  let η : Real := I.inputEta
  let θ : Real := I.workingEta
  have hη : 0 < η := I.input_pos
  have hθ : 0 < θ := I.working_pos
  have hηθ : η ≤ θ / 8 := by exact le_of_eq I.input_eq
  have hθ4 : (0 : ℝ) < θ / 4 := by positivity
  have hθ8 : (0 : ℝ) < θ / 8 := by positivity
  obtain ⟨δU, hδUpos, _hδUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (θ / 4) hθ4
  obtain ⟨δ2, hδ2pos, _hδ2le1, h2thr⟩ := exists_threshold_natCast_le_rpow 2 (θ / 8) hθ8
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_nhdsGT (c := δU) hδUpos,
      eventually_le_nhdsGT (c := δ2) hδ2pos,
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin]
    with δ hcard7 hδU hδ2 hδ1 hδmem
  have hδ0 : (0 : NNReal) < δ := hδmem
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδe0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : ((δ : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have h2E : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(θ / 8)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(θ / 8)),
      show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h2thr hδ0 hδ2)
  intro ι s V hin
  have hball := hin.ball
  have hED := hin.essentially_distinct
  have hfull := hin.fullness
  have hfro := ConvexSpaceBody.frostmanConstIn_le hin.frostman
  set F : ENNReal := (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) with hF_def
  have hFtop : F ≠ ⊤ := by rw [hF_def]; exact ENNReal.coe_ne_top
  have hFpos : 0 < F :=
    lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop) hfull
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd hFpos (by simp [hF_def])
    · exact h
  obtain ⟨j₀, hj₀⟩ := hs
  set v : ENNReal := volume (V j₀).carrier with hv_def
  have hvpos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (V j₀).toTube)
  have hvtop : v ≠ ⊤ := (V j₀).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (V i).carrier = v := fun i => by
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V j₀).toTube
  have hsumcar : ∀ X : Finset ι, ∑ i ∈ X, volume (V i).carrier = (X.card : ENNReal) * v :=
    fun X => by
      simpa [hv_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (V i).toTube) (V j₀).toTube X
  have hM : ∑ i ∈ s, volume (V i).shade = F * ((s.card : ENNReal) * v) := by
    rw [← hsumcar s, hF_def]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody)
  -- **Step 1.**  Discard the tubes of below-average shade density.
  set sa : Finset ι :=
    ShadedBody.discardLowShading s (fun i => (V i).toShadedBody) (2⁻¹ : NNReal) with hsa_def
  have hsa_sub : sa ⊆ s := ShadedBody.discardLowShading_subset _ _ _
  have hmass_a : (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ sa, volume (V i).shade := by
    have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s
      (fun i => (V i).toShadedBody) (c := (2⁻¹ : NNReal)) (by norm_num)
    have hhalf : ((1 - (2⁻¹ : NNReal) : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
      norm_num
    rwa [hhalf] at h
  have hband_a : ∀ i ∈ sa, (2 : ENNReal)⁻¹ * F * v ≤ volume (V i).shade := by
    intro i hi
    have h := ShadedBody.le_volume_shade_of_mem_discardLowShading (c := (2⁻¹ : NNReal)) hi
    have hc : (((2⁻¹ : NNReal)) : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
    rwa [hc, ← hF_def, hcarr i] at h
  have hcount_a : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) ≤ (sa.card : ENNReal) := by
    have hupper : ∑ i ∈ sa, volume (V i).shade ≤ (sa.card : ENNReal) * v := by
      calc ∑ i ∈ sa, volume (V i).shade
          ≤ ∑ i ∈ sa, volume (V i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset
        _ = (sa.card : ENNReal) * v := hsumcar sa
    have hchain : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * v ≤ (sa.card : ENNReal) * v := by
      calc (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * v
          = (2 : ENNReal)⁻¹ * (F * ((s.card : ENNReal) * v)) := by ring
        _ = (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (V i).shade) := by rw [hM]
        _ ≤ ∑ i ∈ sa, volume (V i).shade := hmass_a
        _ ≤ (sa.card : ENNReal) * v := hupper
    exact (ENNReal.mul_le_mul_iff_right hvpos.ne' hvtop).mp
      (by simpa [mul_comm] using hchain)
  have hsane : sa.Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ENNReal)]
    refine lt_of_lt_of_le ?_ hcount_a
    have hcs : (0 : ENNReal) < (s.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr ⟨j₀, hj₀⟩
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (show ((2 : ENNReal))⁻¹ ≠ 0 by simp) hFpos.ne').ne' hcs.ne'
  -- **Step 2.**  Uniformize the tubes on the truncated index set.
  have hcards : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hcard7 δ le_rfl s (fun i => (V i).toTube) (by simpa using hball) (by simpa using hED)
  have hcards_a : (sa.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsa_sub) hcards
  obtain ⟨s₂, h₂a, hcardret, hunif⟩ :=
    hU hδ0 hδU sa (fun i => (V i).toTube)
      (fun i hi => by simpa using hball i (hsa_sub hi)) hcards_a
  have hs₂s : s₂ ⊆ s := h₂a.trans hsa_sub
  have hs₂ne : s₂.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos s₂.card with hz | hpos
    · exfalso
      rw [hz] at hcardret
      norm_num at hcardret
      exact (Finset.not_nonempty_iff_eq_empty.mpr hcardret) hsane
    · exact hpos
  have hcardE : (sa.card : ENNReal)
      ≤ (δ : ENNReal) ^ (-(θ / 4)) * (s₂.card : ENNReal) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(θ / 4)), ← ENNReal.ofReal_natCast sa.card,
      ← ENNReal.ofReal_natCast s₂.card, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)]
    exact ENNReal.ofReal_le_ofReal hcardret
  have hκcard : (δ : ENNReal) ^ (θ / 2) * (s.card : ENNReal) ≤ (s₂.card : ENNReal) := by
    have hkey : (δ : ENNReal) ^ (θ / 2)
        ≤ (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η) := by
      have h2 : (2 : ENNReal) * (δ : ENNReal) ^ (θ / 2)
          ≤ (δ : ENNReal) ^ (θ / 4) * (δ : ENNReal) ^ η := by
        calc (2 : ENNReal) * (δ : ENNReal) ^ (θ / 2)
            ≤ (δ : ENNReal) ^ (-(θ / 8)) * (δ : ENNReal) ^ (θ / 2) := mul_le_mul_right' h2E _
          _ = (δ : ENNReal) ^ (-(θ / 8) + θ / 2) := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ (δ : ENNReal) ^ (θ / 4 + η) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
          _ = (δ : ENNReal) ^ (θ / 4) * (δ : ENNReal) ^ η := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
      calc (δ : ENNReal) ^ (θ / 2) = (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ (θ / 2)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ENNReal)⁻¹ * ((δ : ENNReal) ^ (θ / 4) * (δ : ENNReal) ^ η) :=
            mul_le_mul_left' h2 _
        _ = (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η) := by ring
    calc (δ : ENNReal) ^ (θ / 2) * (s.card : ENNReal)
        ≤ ((δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η))
            * (s.card : ENNReal) := mul_le_mul_right' hkey _
      _ = (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η
            * (s.card : ENNReal)) := by ring
      _ ≤ (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * F * (s.card : ENNReal)) := by
            gcongr
      _ ≤ (δ : ENNReal) ^ (θ / 4) * (sa.card : ENNReal) := by
            exact mul_le_mul_left' hcount_a _
      _ ≤ (δ : ENNReal) ^ (θ / 4) * ((δ : ENNReal) ^ (-(θ / 4)) * (s₂.card : ENNReal)) := by
            exact mul_le_mul_left' hcardE _
      _ = (s₂.card : ENNReal) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
            simp
  refine ⟨⟨s₂, hs₂s, hs₂ne, ?_, ?_, Classical.choice hunif, ?_⟩⟩
  -- **The fullness clause**, termwise on `sa` and hence on every nonempty subfamily.
  · have hstep : (δ : ENNReal) ^ θ ≤ (2 : ENNReal)⁻¹ * F := by
      have h2 : (2 : ENNReal) * (δ : ENNReal) ^ θ ≤ F := by
        calc (2 : ENNReal) * (δ : ENNReal) ^ θ
            ≤ (δ : ENNReal) ^ (-(θ / 8)) * (δ : ENNReal) ^ θ := mul_le_mul_right' h2E _
          _ = (δ : ENNReal) ^ (-(θ / 8) + θ) := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ (δ : ENNReal) ^ η :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
          _ ≤ F := hfull
      calc (δ : ENNReal) ^ θ = (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ θ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ENNReal)⁻¹ * F := mul_le_mul_left' h2 _
    have hterm : ∀ i ∈ sa,
        (δ : ENNReal) ^ θ * volume ((fun i => (V i).toShadedBody) i).carrier
          ≤ volume ((fun i => (V i).toShadedBody) i).shade := by
      intro i hi
      refine le_trans ?_ (hband_a i hi)
      have hcv : volume ((fun i => (V i).toShadedBody) i).carrier = v := hcarr i
      rw [hcv]
      exact mul_le_mul_right' hstep v
    intro t ht htne
    exact ml1Boot.le_fullness_of_termwise (fun i => (V i).toShadedBody)
      (fun i _ => by rw [hcarr i]; exact hvpos)
      (fun i _ => by rw [hcarr i]; exact hvtop) hterm (ht.trans h₂a) htne
  -- The same chosen family's Frostman bound.
  · have hκpos : ((δ : ENNReal) ^ (θ / 2)) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop).ne'
    have hWK : ∀ i ∈ s, (V i).toConvexSpaceBody
        ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
      intro i hi
      change (V i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i hi
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := s) (s' := s₂) (W := fun i => (V i).toConvexSpaceBody)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (κ := (δ : ENNReal) ^ (θ / 2)) (v := v) ⟨j₀, hj₀⟩ (fun i _ => hcarr i) hWK hs₂s
      hκpos hκcard
    rw [← ENNReal.rpow_neg] at hf
    refine hf.trans ?_
    calc (δ : ENNReal) ^ (-(θ / 2)) * ConvexSpaceBody.frostmanConstIn s
            (fun i => (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ≤ (δ : ENNReal) ^ (-(θ / 2)) * (δ : ENNReal) ^ (-η) := mul_le_mul_left' hfro _
      _ = (δ : ENNReal) ^ (-(θ / 2) + -η) := by rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
      _ ≤ (δ : ENNReal) ^ (-θ) := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  · have hpow : (δ : ENNReal) ^ θ ≤ (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (θ / 2) := by
      have htwo : (2 : ENNReal) * (δ : ENNReal) ^ θ ≤ (δ : ENNReal) ^ (θ / 2) := by
        calc
          _ ≤ (δ : ENNReal) ^ (-(θ / 8)) * (δ : ENNReal) ^ θ :=
            mul_le_mul' h2E le_rfl
          _ = (δ : ENNReal) ^ (-(θ / 8) + θ) := by
            rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith only [hθ])
      calc
        _ = (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ θ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ _ := mul_le_mul' le_rfl htwo
    calc
      _ = (δ : ENNReal) ^ θ * (F * ((s.card : ENNReal) * v)) := by rw [hM]
      _ ≤ ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (θ / 2)) *
          (F * ((s.card : ENNReal) * v)) := mul_le_mul' hpow le_rfl
      _ = (2 : ENNReal)⁻¹ * F * ((δ : ENNReal) ^ (θ / 2) * (s.card : ENNReal)) * v := by ring
      _ ≤ (2 : ENNReal)⁻¹ * F * (s₂.card : ENNReal) * v :=
        mul_le_mul' (mul_le_mul' le_rfl hκcard) le_rfl
      _ = ∑ _i ∈ s₂, (2 : ENNReal)⁻¹ * F * v := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hband_a i (h₂a hi))


/-- A concrete source producer below the restart layer. The actual
nonatomic fine cut, its full-middle denominator and the product of three
actual counts are returned together for the SAME selections. -/
theorem exists_same_mass_balanced_selections_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3) (M : Nat) (hM : 1 <= M)
    (Ccan Ctw Ccell : NNReal)
    (hCcan : 1 <= Ccan) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    {reserve : Real} (hreserve : 0 < reserve) :
    ∃ (Cselect : NNReal) (Kselect : Nat), 1 <= Cselect ∧ 1 <= Kselect ∧
      ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
        ∀ {iota : Type uI} [DecidableEq iota]
          (s : Finset iota) (Y : iota -> ShadedTube delta E)
          (U : RevisedLiteralProfileInterfaceFormalizerW87.CanonicalProfileNetW87
            s (fun i => (Y i).toTube) M Ccan),
          s.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
          (∀ i ∈ s, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          (delta : ENNReal) ^ reserve <= fullness' s (fun i => (Y i).toShadedBody) ->
          ∀ {p : Params} {BF : NNReal} (block : ActualSourceDividingBlockW95 U p BF),
            let loss := Cselect * Real.toNNReal
              ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ Kselect)
            ∃ selections : ActualSameMassSelectionsW95 block loss,
              ((loss : ENNReal) ^ (6 : Nat))⁻¹ *
                  (fullness' s (fun i => (Y i).toShadedBody)) ^ (2 : Nat) <=
                fullness' (U.cover.indexSet block.b.val)
                  (fun Q => (zeroExtend selections.secondFamily (U.cover.tube block.b.val)
                    selections.secondShading Q).toShadedBody) ∧
              ((completeFibreW94 s (U.cover.assign block.b.val) selections.fineLabel).card : Real) *
                ((completeFibreW94 (U.cover.indexSet block.b.val) selections.coarseAssign
                  selections.middleLabel).card : Real) *
                (selections.coarseFamily.card : Real) <= 4 * (s.card : Real) := by
  classical
  have hgeometricProduct {delta : NNReal}
      {iota : Type uI} [DecidableEq iota]
      {p : Params} {BF : NNReal}
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
      (U : RevisedLiteralProfileInterfaceFormalizerW87.CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (block : ActualSourceDividingBlockW95 U p BF)
      (selections : ActualSameMassSelectionsW95 block loss)
      (Q : iota) (hQ : Q ∈ U.cover.indexSet block.b.val)
      (R : iota) (hR : R ∈ U.cover.indexSet block.a.val) :
      ((completeFibreW94 A (U.cover.assign block.b.val) Q).card : ENNReal) *
        ((actualDescendantsW95 A U.cover.assign block.a.val block.b.val R).card : ENNReal) *
        ((U.cover.indexSet block.a.val).card : ENNReal) <= 4 * (A.card : ENNReal) := by
    have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
    have ha : block.a.val <= M := block.a_lt_b.le.trans hb
    let fine := completeFibreW94 A (U.cover.assign block.b.val)
    let middle := actualDescendantsW95 A U.cover.assign block.a.val block.b.val
    have hmidEq : ∀ R', middle R' =
        (U.cover.indexSet block.b.val).filter (fun Q' => selections.coarseAssign Q' = R') := by
      intro R'
      ext Q'
      constructor
      · intro hQ'
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ'
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨U.cover.assign_mem block.b.val hb i hiA,
          (selections.parent_compatibility i hiA).trans hiR⟩
      · intro hQ'
        obtain ⟨hQ'b, hQ'R⟩ := Finset.mem_filter.mp hQ'
        rw [← reg.surjective block.b.val hb] at hQ'b
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ'b
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨hi, (selections.parent_compatibility i hi).symm.trans hQ'R⟩, rfl⟩
    have hparentMap : ∀ Q' ∈ U.cover.indexSet block.b.val,
        selections.coarseAssign Q' ∈ U.cover.indexSet block.a.val := by
      intro Q' hQ'
      rw [← reg.surjective block.b.val hb] at hQ'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ'
      rw [selections.parent_compatibility i hi]
      exact U.cover.assign_mem block.a.val ha i hi
    have hsumFine : (∑ Q' ∈ U.cover.indexSet block.b.val,
        ((fine Q').card : NNReal)) = (A.card : NNReal) := by
      simpa only [fine, completeFibreW94, Finset.sum_const, nsmul_eq_mul, mul_one]
        using Finset.sum_fiberwise_of_maps_to (U.cover.assign_mem block.b.val hb)
          (fun _ => (1 : NNReal))
    have hsumMiddle : (∑ R' ∈ U.cover.indexSet block.a.val,
        ((middle R').card : NNReal)) = ((U.cover.indexSet block.b.val).card : NNReal) := by
      simp_rw [hmidEq]
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one]
        using Finset.sum_fiberwise_of_maps_to hparentMap (fun _ => (1 : NNReal))
    have hbottom : ∀ Q', actualDescendantsW95 A U.cover.assign block.b.val M Q' = fine Q' := by
      intro Q'
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        rw [reg.bottom_assign j (Finset.mem_filter.mp hj).1]
        exact hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, reg.bottom_assign i (Finset.mem_filter.mp hi).1⟩
    let nFine : NNReal := if block.b.val < M then reg.countBand block.b.val M else 1
    have hFineBand : ∀ Q' ∈ U.cover.indexSet block.b.val,
        nFine <= ((fine Q').card : NNReal) ∧ ((fine Q').card : NNReal) <= 2 * nFine := by
      intro Q' hQ'
      by_cases hstrict : block.b.val < M
      · dsimp only [nFine]
        rw [if_pos hstrict, ← hbottom]
        exact ⟨reg.count_lower block.b.val M hstrict le_rfl Q' hQ',
          (reg.count_upper block.b.val M hstrict le_rfl Q' hQ').le⟩
      · have heq : block.b.val = M := by omega
        have hQ'A : Q' ∈ A := by simpa only [heq, reg.bottom_index] using hQ'
        have hf : fine Q' = {Q'} := by
          ext i
          simp only [fine, completeFibreW94, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · intro hi
            simpa only [heq, reg.bottom_assign i hi.1] using hi.2
          · intro hi
            subst i
            exact ⟨hQ'A, by rw [heq, reg.bottom_assign Q' hQ'A]⟩
        simp only [nFine, if_neg hstrict, hf, Finset.card_singleton, Nat.cast_one]
        norm_num
    have hFineTotal : ((U.cover.indexSet block.b.val).card : NNReal) * nFine <=
        (A.card : NNReal) := by
      calc
        _ = ∑ Q' ∈ U.cover.indexSet block.b.val, nFine := by simp
        _ <= ∑ Q' ∈ U.cover.indexSet block.b.val, ((fine Q').card : NNReal) :=
          Finset.sum_le_sum (fun Q' hQ' => (hFineBand Q' hQ').1)
        _ = _ := hsumFine
    have hMiddleTotal : ((U.cover.indexSet block.a.val).card : NNReal) *
        reg.countBand block.a.val block.b.val <= ((U.cover.indexSet block.b.val).card : NNReal) := by
      calc
        _ = ∑ R' ∈ U.cover.indexSet block.a.val, reg.countBand block.a.val block.b.val := by simp
        _ <= ∑ R' ∈ U.cover.indexSet block.a.val, ((middle R').card : NNReal) :=
          Finset.sum_le_sum (fun R' hR' => reg.count_lower block.a.val block.b.val block.a_lt_b hb R' hR')
        _ = _ := hsumMiddle
    have hraw : ((fine Q).card : NNReal) * ((middle R).card : NNReal) *
        ((U.cover.indexSet block.a.val).card : NNReal) <= 4 * (A.card : NNReal) := by
      calc
        _ <= (2 * nFine) * (2 * reg.countBand block.a.val block.b.val) *
            ((U.cover.indexSet block.a.val).card : NNReal) := by
          gcongr
          · exact (hFineBand Q hQ).2
          · exact (reg.count_upper block.a.val block.b.val block.a_lt_b hb R hR).le
        _ = 4 * nFine * (((U.cover.indexSet block.a.val).card : NNReal) *
            reg.countBand block.a.val block.b.val) := by ring
        _ <= 4 * nFine * ((U.cover.indexSet block.b.val).card : NNReal) :=
          mul_le_mul_left' hMiddleTotal _
        _ = 4 * (((U.cover.indexSet block.b.val).card : NNReal) * nFine) := by ring
        _ <= 4 * (A.card : NNReal) := mul_le_mul_left' hFineTotal _
    exact_mod_cast hraw
  obtain ⟨Cselect, Kselect, delta0, hCselect, hKselect, hdelta0, hdelta01, hselect⟩ :=
    exists_actual_same_mass_selections_with_certificate_w99
      hdim M hM Ccan Ctw Ccell hCcan hCtw hCcell reserve hreserve
  refine ⟨Cselect, Kselect, hCselect, hKselect, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hdelta0).filter_mono nhdsWithin_le_nhds] with delta hdelta hd0
  intro iota _ s Y U hs hreg hball hfull p BF block
  obtain ⟨certificate, _⟩ := hselect hdelta hd0 s Y U hs hreg hball hfull block
  refine ⟨certificate.selections, certificate.middle_fullness, ?_⟩
  let selections := certificate.selections
  have hQ := selections.first.parent_subset selections.first.sel_mem
  have hR := selections.second.parent_subset selections.second.sel_mem
  have hgeo := hgeometricProduct U hreg block selections selections.fineLabel hQ
    selections.middleLabel hR
  have hmidEq : actualDescendantsW95 s U.cover.assign block.a.val block.b.val
      selections.middleLabel = completeFibreW94 (U.cover.indexSet block.b.val)
        selections.coarseAssign selections.middleLabel := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiS, hiR⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨U.cover.assign_mem block.b.val (Nat.le_of_lt_succ block.b.isLt) i hiS,
        (selections.parent_compatibility i hiS).trans hiR⟩
    · intro hQ
      obtain ⟨hQb, hQR⟩ := Finset.mem_filter.mp hQ
      rw [← hreg.surjective block.b.val (Nat.le_of_lt_succ block.b.isLt)] at hQb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQb
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨hi, (selections.parent_compatibility i hi).symm.trans hQR⟩, rfl⟩
  rw [hmidEq] at hgeo
  have hcard : (selections.coarseFamily.card : ENNReal) ≤
      ((U.cover.indexSet block.a.val).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card selections.second.parent_subset
  have hpaid := (mul_le_mul' (le_refl
    (((completeFibreW94 s (U.cover.assign block.b.val) selections.fineLabel).card : ENNReal) *
      ((completeFibreW94 (U.cover.indexSet block.b.val) selections.coarseAssign
        selections.middleLabel).card : ENNReal))) hcard).trans hgeo
  exact_mod_cast hpaid


/-- The output is indexed by the original s and Y. Same-tube, subshade and
retained mass are inherited from the actual retained-state definition.
The terminal multiplicity price and the transport price are both explicit. -/
structure OriginalRunW110 [Nontrivial E] {iota : Type uI} {delta : NNReal}
    (s : Finset iota) (Y : iota -> ShadedTube delta E)
    (gamma step accuracy : Real) where
  terminal : RetainedStateW94 s Y
  transport_budget : (delta : ENNReal) ^ (accuracy / 4) <= terminal.retained
  terminal_estimate :
    ShadedBody.multiplicity terminal.active (fun i => (terminal.shading i).toShadedBody) <=
      (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - step)) *
        ((terminal.active.card : ENNReal) * (delta : ENNReal) ^
          (Module.finrank Real E - 1)) ^ (1 - (gamma - step) / 2)

end

end Kakeya.ml1Boot.RevisedSourceRepairW110

namespace Kakeya.ml1Boot.FixedMStickyExitW110

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open TrialRestartW94 RevisedLiteralProfileInterfaceFormalizerW87
open RevisedSourceRepairW110

/-- Quantitative transfer between two potentially different grids,
including the mesh factor of degree eight. -/
theorem mixed_grid_frostman_transfer_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {radius : NNReal}
    (hradius : 0 < radius) (hradius_one : radius <= 1)
    {M J : Nat} (hM : 1 <= M) (hJ : 1 <= J)
    (A B : Finset iota) (Z : iota -> ShadedTube radius E)
    (hA : A.Nonempty) (hB : B.Nonempty) (hBA : B ⊆ A)
    (hball : ∀ i ∈ A, (Z i).carrier ⊆ Metric.closedBall 0 1)
    {Cold Cnew Ctw Ccell : NNReal} (hCtw : 1 <= Ctw)
    (U : CanonicalProfileNetW87 A (fun i => (Z i).toTube) M Cold)
    (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
    (V : Tube.UniformTubeSet B (fun i => (Z i).toTube) J Cnew)
    {L : NNReal} (hcard : (A.card : NNReal) <= L * (B.card : NNReal))
    {H : ENNReal} (hEvery : U.IsFrostmanAtEveryScale H) :
    V.IsFrostmanAtEveryScale
      ((trialNearbyParentCountW96 Ctw : ENNReal) *
        ((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
        (Cold : ENNReal) ^ (2 : Nat) * (Cnew : ENNReal) ^ (3 : Nat) *
        (L : ENNReal) * (radius : ENNReal) ^ (-(8 : Real) / (M : Real)) * H) := by
  classical
  intro j hj jnew hjnew
  let k := Nat.ceil ((M : Real) * j / J)
  have hMpos : (0 : Real) < M := by exact_mod_cast hM
  have hJpos : (0 : Real) < J := by exact_mod_cast hJ
  have hk : k <= M := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hJpos).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hMpos.le
  have hkLower : (j : Real) / J <= (k : Real) / M := by
    apply (le_div_iff₀ hMpos).mpr
    simpa [k, mul_div_assoc, mul_comm] using Nat.le_ceil ((M : Real) * j / J)
  have hkUpper : (k : Real) / M <= (j : Real) / J + 1 / M := by
    apply (div_le_iff₀ hMpos).mpr
    have h := (Nat.ceil_lt_add_one
      (show (0 : Real) <= (M : Real) * j / J by positivity)).le
    dsimp only [k]
    convert h using 1 <;> field_simp
  let r := Tube.gridScale radius M k
  let s := Tube.gridScale radius J j
  have hrpos : 0 < r := Tube.gridScale_pos hradius M k
  have hspos : 0 < s := Tube.gridScale_pos hradius J j
  have hrone : r <= 1 := Tube.gridScale_le_one hradius_one M k
  have hsone : s <= 1 := Tube.gridScale_le_one hradius_one J j
  have hdr : radius <= r := by
    rw [← Tube.gridScale_self radius (show 0 < M by omega)]
    exact Tube.gridScale_antitone hradius hradius_one M hk
  have hds : radius <= s := by
    rw [← Tube.gridScale_self radius (show 0 < J by omega)]
    exact Tube.gridScale_antitone hradius hradius_one J hj
  have hrs : r <= s := NNReal.rpow_le_rpow_of_exponent_ge hradius hradius_one hkLower
  let q : NNReal := s / r
  have hq : 1 <= q := (one_le_div hrpos).mpr hrs
  have hqmesh : q ^ (8 : Nat) <= radius ^ (-(8 : Real) / (M : Real)) := by
    have hqeq : q = radius ^ ((j : Real) / J - (k : Real) / M) := by
      exact (NNReal.rpow_sub hradius.ne' _ _).symm
    rw [hqeq, ← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    apply NNReal.rpow_le_rpow_of_exponent_ge hradius hradius_one
    norm_num
    have ht : -(1 / (M : Real)) <= (j : Real) / J - (k : Real) / M := by
      linarith only [hkUpper]
    calc
      -(8 : Real) / M = 8 * (-(1 / (M : Real))) := by ring
      _ <= 8 * ((j : Real) / J - (k : Real) / M) :=
        mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = _ := by ring
  have hnodeCount : ((V.cover.indexSet j).card : NNReal) <=
      Cnew * ((U.cover.indexSet k).card : NNReal) := by
    have hcov : V.cover.indexSet j ⊆ (U.cover.indexSet k).biUnion (fun old =>
        (V.cover.indexSet j).filter (fun new => ∃ i ∈ B,
          (Z i).toConvexSpaceBody <= (V.cover.tube j new).toConvexSpaceBody ∧
          (Z i).toConvexSpaceBody <=
            ((U.cover.tube k old).rescale s).toConvexSpaceBody)) := by
      intro new hnew
      obtain ⟨i, hi⟩ := MultiScaleFac.coverClass_nonempty_of_mem_parent V hj hB hnew
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      obtain ⟨hiB, hassign⟩ := hi
      refine Finset.mem_biUnion.mpr ⟨U.cover.assign k i,
        U.cover.assign_mem k hk i (hBA hiB), Finset.mem_filter.mpr ⟨hnew,
        i, hiB, ?_, (U.cover.le_tube_assign k hk i (hBA hiB)).trans
          ((U.cover.tube k (U.cover.assign k i)).le_rescale hrs)⟩⟩
      have h := V.cover.le_tube_assign j hj i hiB
      rwa [hassign] at h
    calc
      ((V.cover.indexSet j).card : NNReal) <=
          ((∑ old ∈ U.cover.indexSet k,
            ((V.cover.indexSet j).filter (fun new => ∃ i ∈ B,
              (Z i).toConvexSpaceBody <= (V.cover.tube j new).toConvexSpaceBody ∧
              (Z i).toConvexSpaceBody <=
                ((U.cover.tube k old).rescale s).toConvexSpaceBody)).card : Nat) : NNReal) := by
        exact_mod_cast (Finset.card_le_card hcov).trans Finset.card_biUnion_le
      _ = ∑ old ∈ U.cover.indexSet k,
          (((V.cover.indexSet j).filter (fun new => ∃ i ∈ B,
            (Z i).toConvexSpaceBody <= (V.cover.tube j new).toConvexSpaceBody ∧
            (Z i).toConvexSpaceBody <=
              ((U.cover.tube k old).rescale s).toConvexSpaceBody)).card : NNReal) := by
        push_cast
        rfl
      _ <= ∑ _old ∈ U.cover.indexSet k, Cnew :=
        Finset.sum_le_sum fun old _ => V.boundedOverlap j hj ((U.cover.tube k old).rescale s)
      _ = Cnew * ((U.cover.indexSet k).card : NNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hbranch : U.branchingN k <= Cold * L * Cnew ^ 2 * V.branchingN j := by
    have hpartU : A.card = ∑ old ∈ U.cover.indexSet k,
        (Tube.coverClass A (U.cover.assign k) old).card := by
      simp only [Tube.coverClass]
      convert (Finset.card_eq_sum_card_fiberwise fun i hi => U.cover.assign_mem k hk i hi) using 1
      apply Finset.sum_congr rfl
      intro old hold
      congr 1
      ext i
      simp only [Finset.mem_filter]
    have hpartV : B.card = ∑ new ∈ V.cover.indexSet j,
        (Tube.coverClass B (V.cover.assign j) new).card := by
      simp only [Tube.coverClass]
      convert (Finset.card_eq_sum_card_fiberwise fun i hi => V.cover.assign_mem j hj i hi) using 1
      apply Finset.sum_congr rfl
      intro new hnew
      congr 1
      ext i
      simp only [Finset.mem_filter]
    have hE1 : ((U.cover.indexSet k).card : NNReal) * U.branchingN k <=
        Cold * (A.card : NNReal) := by
      calc
        _ = ∑ _old ∈ U.cover.indexSet k, U.branchingN k := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ old ∈ U.cover.indexSet k,
            Cold * ((Tube.coverClass A (U.cover.assign k) old).card : NNReal) :=
          Finset.sum_le_sum fun old hold => U.le_card_class k hk old hold
        _ = Cold * (A.card : NNReal) := by
          rw [← Finset.mul_sum, hpartU]
          push_cast
          rfl
    have hE2 : (B.card : NNReal) <=
        ((V.cover.indexSet j).card : NNReal) * (Cnew * V.branchingN j) := by
      calc
        _ = ∑ new ∈ V.cover.indexSet j,
            ((Tube.coverClass B (V.cover.assign j) new).card : NNReal) := by
          rw [hpartV]
          push_cast
          rfl
        _ <= ∑ _new ∈ V.cover.indexSet j, Cnew * V.branchingN j :=
          Finset.sum_le_sum fun new hnew => V.card_class_le j hj new hnew
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hnpos : 0 < ((U.cover.indexSet k).card : NNReal) := by
      obtain ⟨i, hi⟩ := hA
      exact_mod_cast Finset.card_pos.mpr ⟨_, U.cover.assign_mem k hk i hi⟩
    apply le_of_mul_le_mul_right (a := ((U.cover.indexSet k).card : NNReal)) _ hnpos
    calc
      _ = ((U.cover.indexSet k).card : NNReal) * U.branchingN k := mul_comm _ _
      _ <= Cold * (A.card : NNReal) := hE1
      _ <= Cold * (L * (B.card : NNReal)) := mul_le_mul_right hcard Cold
      _ <= Cold * (L * (((V.cover.indexSet j).card : NNReal) *
          (Cnew * V.branchingN j))) := by gcongr
      _ <= Cold * (L * ((Cnew * ((U.cover.indexSet k).card : NNReal)) *
          (Cnew * V.branchingN j))) := by gcongr
      _ = _ := by ring
  let W : iota -> ConvexSpaceBody E := fun i => (Z i).toConvexSpaceBody
  obtain ⟨i0, hi0⟩ := hB
  let v := volume (W i0).carrier
  let Knew := (V.cover.tube j jnew).toConvexSpaceBody
  let u := volume Knew.carrier
  let Kvol : NNReal := Tube.volume_le.C 3 / Tube.le_volume.c 3
  let classNew := Tube.coverClass B (V.cover.assign j) jnew
  have hcmem : ∀ i ∈ classNew, i ∈ B ∧ V.cover.assign j i = jnew := by
    intro i hi
    simpa only [classNew, Tube.coverClass, Finset.mem_filter] using hi
  have hcW : ∀ i ∈ classNew, W i <= Knew := by
    intro i hi
    have h := V.cover.le_tube_assign j hj i (hcmem i hi).1
    rwa [(hcmem i hi).2] at h
  have hRHS : densityIn classNew W Knew = (classNew.card : ENNReal) * v / u := by
    rw [densityIn_of_all_le hcW]
    have hv : ∀ i ∈ classNew, volume (W i).carrier = v :=
      fun i _ => Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul]
  intro K' hK'
  let F := classNew.filter (fun i => W i <= K')
  let oldNodes := F.image (U.cover.assign k)
  have hFmem : ∀ i ∈ F, i ∈ B ∧ V.cover.assign j i = jnew ∧ W i <= K' := by
    intro i hi
    obtain ⟨hic, hiK⟩ := Finset.mem_filter.mp hi
    exact ⟨(hcmem i hic).1, (hcmem i hic).2, hiK⟩
  have hOldMem : ∀ old ∈ oldNodes, old ∈ U.cover.indexSet k := by
    intro old hold
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hold
    exact U.cover.assign_mem k hk i (hBA (hFmem i hi).1)
  have hOldCount : (oldNodes.card : NNReal) <=
      (trialNearbyParentCountW96 Ctw : NNReal) * q ^ (6 : Nat) := by
    have hsub : oldNodes ⊆ commonFineMeetingParentsW96 A (fun i => (Z i).toTube)
        (U.cover.indexSet k) (U.cover.tube k) (V.cover.tube j jnew) := by
      intro old hold
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hold
      obtain ⟨hiB, hia, _⟩ := hFmem i hi
      refine Finset.mem_filter.mpr ⟨U.cover.assign_mem k hk i (hBA hiB),
        i, hBA hiB, U.cover.le_tube_assign k hk i (hBA hiB), ?_⟩
      have h := V.cover.le_tube_assign j hj i hiB
      rwa [hia] at h
    have hcount := card_assigned_parents_meeting_exact_cell_w96 hdim hradius hdr hds hrone
      A (fun i => (Z i).toTube) (U.cover.indexSet k) (U.cover.tube k)
      (V.cover.tube j jnew) Ctw hCtw hball (hregular.parent_ball k hk)
      (hregular.parent_line_ed k hk)
    have hqR : (1 : Real) <= (s : Real) / r := by exact_mod_cast hq
    rw [max_eq_right hqR] at hcount
    have hcount' : (oldNodes.card : Real) <=
        (trialNearbyParentCountW96 Ctw : Real) * ((s : Real) / r) ^ (6 : Nat) :=
      (show (oldNodes.card : Real) <=
        ((commonFineMeetingParentsW96 A (fun i => (Z i).toTube)
          (U.cover.indexSet k) (U.cover.tube k) (V.cover.tube j jnew)).card : Real) by
        exact_mod_cast Finset.card_le_card hsub).trans hcount
    exact_mod_cast hcount'
  have hnum : ∑ i ∈ F, volume (W i).carrier <=
      ∑ old ∈ oldNodes, ∑ i ∈ Tube.coverClass A (U.cover.assign k) old
        with W i <= K', volume (W i).carrier := by
    have hfib : (∑ old ∈ oldNodes, ∑ i ∈ F with U.cover.assign k i = old,
        volume (W i).carrier) = ∑ i ∈ F, volume (W i).carrier :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
    rw [← hfib]
    refine Finset.sum_le_sum fun old _ => Finset.sum_le_sum_of_subset ?_
    intro i hi
    obtain ⟨hiF, hia⟩ := Finset.mem_filter.mp hi
    simp only [Tube.coverClass, Finset.mem_filter]
    exact ⟨⟨hBA (hFmem i hiF).1, hia⟩, (hFmem i hiF).2.2⟩
  have hstep1 : densityIn classNew W K' <=
      ∑ old ∈ oldNodes, densityIn (Tube.coverClass A (U.cover.assign k) old) W K' := by
    calc
      _ = (∑ i ∈ F, volume (W i).carrier) / volume K'.carrier := rfl
      _ <= (∑ old ∈ oldNodes, ∑ i ∈ Tube.coverClass A (U.cover.assign k) old
          with W i <= K', volume (W i).carrier) / volume K'.carrier :=
        ENNReal.div_le_div_right hnum _
      _ = _ := by simp only [densityIn, div_eq_mul_inv, Finset.sum_mul]
  have hstep2 : ∀ old ∈ oldNodes,
      densityIn (Tube.coverClass A (U.cover.assign k) old) W K' <=
        H * densityIn (Tube.coverClass A (U.cover.assign k) old) W
          (U.cover.tube k old).toConvexSpaceBody := by
    intro old hold
    have hcOld : ∀ i ∈ Tube.coverClass A (U.cover.assign k) old,
        W i <= (U.cover.tube k old).toConvexSpaceBody := by
      intro i hi
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      have h := U.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at h
    exact (le_maxDensity _ _ K').trans
      ((hEvery k hk old (hOldMem old hold)).maxDensity_le_of_carrier_subset hcOld)
  have hstep3 : ∀ old ∈ oldNodes,
      densityIn (Tube.coverClass A (U.cover.assign k) old) W
          (U.cover.tube k old).toConvexSpaceBody <=
        ((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3) *
          (Kvol : ENNReal) * (q : ENNReal) ^ 2 * densityIn classNew W Knew := by
    intro old hold
    have hcOld : ∀ i ∈ Tube.coverClass A (U.cover.assign k) old,
        W i <= (U.cover.tube k old).toConvexSpaceBody := by
      intro i hi
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      have h := U.cover.le_tube_assign k hk i hi.1
      rwa [hi.2] at h
    have hvols : ∀ i ∈ Tube.coverClass A (U.cover.assign k) old,
        volume (W i).carrier = v :=
      fun i _ => Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube
    have hcardN : ((Tube.coverClass A (U.cover.assign k) old).card : NNReal) <=
        Cold ^ 2 * L * Cnew ^ 3 * (classNew.card : NNReal) := by
      calc
        _ <= Cold * U.branchingN k := U.card_class_le k hk old (hOldMem old hold)
        _ <= Cold * (Cold * L * Cnew ^ 2 * V.branchingN j) := mul_le_mul_right hbranch Cold
        _ <= Cold * (Cold * L * Cnew ^ 2 * (Cnew * (classNew.card : NNReal))) := by
          gcongr
          exact V.le_card_class j hj jnew hjnew
        _ = _ := by ring
    have hcardE : ((Tube.coverClass A (U.cover.assign k) old).card : ENNReal) <=
        (Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3 *
          (classNew.card : ENNReal) := by exact_mod_cast hcardN
    let uold := volume (U.cover.tube k old).carrier
    have huo : uold ≠ 0 := (Tube.volume_pos_and_lt_top hrpos hrone _).1.ne'
    have hut : uold ≠ ⊤ := (Tube.volume_pos_and_lt_top hrpos hrone _).2.ne
    have hu : u ≠ 0 := (Tube.volume_pos_and_lt_top hspos hsone _).1.ne'
    have hutop : u ≠ ⊤ := (Tube.volume_pos_and_lt_top hspos hsone _).2.ne
    have hucomp : u <= (Kvol : ENNReal) * (q : ENNReal) ^ 2 * uold := by
      have hupper : u <= (Tube.volume_le.C 3 : ENNReal) * (s : ENNReal) ^ 2 := by
        simpa only [hdim, Nat.reduceSub] using Tube.volume_le hsone (V.cover.tube j jnew)
      have hlower : (Tube.le_volume.c 3 : ENNReal) * (r : ENNReal) ^ 2 <= uold := by
        simpa only [hdim, Nat.reduceSub] using Tube.le_volume (U.cover.tube k old)
      have heq : Kvol * q ^ 2 * (Tube.le_volume.c 3 * r ^ 2) = Tube.volume_le.C 3 * s ^ 2 := by
        dsimp [Kvol, q]
        field_simp [(Tube.le_volume.c_pos 3).ne', hrpos.ne']
      calc
        u <= (Tube.volume_le.C 3 : ENNReal) * (s : ENNReal) ^ 2 := hupper
        _ = (Kvol : ENNReal) * (q : ENNReal) ^ 2 *
            ((Tube.le_volume.c 3 : ENNReal) * (r : ENNReal) ^ 2) := by
          exact_mod_cast heq.symm
        _ <= _ := mul_le_mul_right hlower _
    rw [densityIn_of_all_le hcOld, Finset.sum_congr rfl hvols,
      Finset.sum_const, nsmul_eq_mul, hRHS]
    apply (ENNReal.div_le_iff huo hut).mpr
    calc
      _ <= ((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3 *
          (classNew.card : ENNReal)) * v := mul_le_mul_left hcardE v
      _ = ((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3) *
          (((classNew.card : ENNReal) * v / u) * u) := by
        rw [ENNReal.div_mul_cancel hu hutop]
        ring
      _ <= ((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3) *
          (((classNew.card : ENNReal) * v / u) *
            ((Kvol : ENNReal) * (q : ENNReal) ^ 2 * uold)) := by gcongr
      _ = _ := by ring
  calc
    densityIn classNew W K' <=
        ∑ old ∈ oldNodes, densityIn (Tube.coverClass A (U.cover.assign k) old) W K' := hstep1
    _ <= ∑ _old ∈ oldNodes, H *
        (((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3) *
          (Kvol : ENNReal) * (q : ENNReal) ^ 2 * densityIn classNew W Knew) :=
      Finset.sum_le_sum fun old hold => (hstep2 old hold).trans
        (mul_le_mul_right (hstep3 old hold) H)
    _ = (oldNodes.card : ENNReal) * (H *
        (((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3) *
          (Kvol : ENNReal) * (q : ENNReal) ^ 2 * densityIn classNew W Knew)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ((trialNearbyParentCountW96 Ctw : ENNReal) * (q : ENNReal) ^ 6) * (H *
        (((Cold : ENNReal) ^ 2 * (L : ENNReal) * (Cnew : ENNReal) ^ 3) *
          (Kvol : ENNReal) * (q : ENNReal) ^ 2 * densityIn classNew W Knew)) := by
      gcongr
      exact_mod_cast hOldCount
    _ = (trialNearbyParentCountW96 Ctw : ENNReal) * (Kvol : ENNReal) *
        (Cold : ENNReal) ^ 2 * (Cnew : ENNReal) ^ 3 * (L : ENNReal) *
        (q : ENNReal) ^ 8 * H * densityIn classNew W Knew := by ring
    _ <= _ := by
      gcongr
      simpa only [ENNReal.coe_pow, ENNReal.coe_rpow_of_ne_zero hradius.ne'] using
        (ENNReal.coe_le_coe.mpr hqmesh)


/-- Construct the actual capped shaded tower from the fixed-M terminal,
then apply the already fixed sticky witness to that same constructed family. -/
theorem eventually_fixed_m_sticky_exit_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real}
    (S : StickyWitnessW110.{uE, uI} E gammaZero)
    (G : SourceStructureW110 beta gammaZero S.etaStar)
    (Cwork Ctw Ccell BF : NNReal)
    (hCwork : 1 <= Cwork) (hCtw : 1 <= Ctw)
    (hCcell : 1 <= Ccell) (hBF : 1 <= BF) :
    ∀ᶠ (radius : NNReal) in 𝓝[>] 0,
      ∀ {iota : Type uI} [DecidableEq iota]
        (A : Finset iota) (Z : iota -> ShadedTube radius E)
        (U : CanonicalProfileNetW87 A
          (fun i => (Z i).toTube) G.M Cwork),
        A.Nonempty ->
        (∀ i ∈ A, (Z i).carrier ⊆ Metric.closedBall 0 1) ->
        lineEssentiallyDistinctW94 A (fun i => (Z i).toTube) Ctw ->
        (A.card : Real) <= (radius : Real) ^ (-7 : Real) ->
        (radius : ENNReal) ^ G.p.ε <=
          fullness' A (fun i => (Z i).toShadedBody) ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        U.IsFrostmanAtEveryScale
          ((BF : ENNReal) ^ (G.p.N + 1) *
            (radius : ENNReal) ^ (-3 * G.p.ε)) ->
        ∃ (B : Finset iota) (W : iota -> ShadedTube radius E)
          (V : ShadedTube.ShadedUniformTubeSet B W
            (Tube.ssfGridLen radius)
            (ShadedTube.ssfUniformConst (Module.finrank Real E))),
          B.Nonempty ∧ B ⊆ A ∧
          (∀ i, (W i).toTube = (Z i).toTube) ∧
          (∀ i, (W i).shade ⊆ (Z i).shade) ∧
          (radius : Real) ^ (3 * G.p.ε / 2) * (A.card : Real)
            <= (B.card : Real) ∧
          (radius : ENNReal) ^ (2 * G.p.ε) *
              (∑ i ∈ A, volume (Z i).shade)
            <= ∑ i ∈ B, volume (W i).shade ∧
          (radius : ENNReal) ^ (2 * G.p.ε)
            <= fullness' B (fun i => (W i).toShadedBody) ∧
          V.tubeUniform.IsFrostmanAtEveryScale
            ((radius : ENNReal) ^ (-5 * G.p.ε)) ∧
          (radius : ENNReal) ^ (gammaZero / 4)
            <= volume (⋃ i ∈ B, (W i).shade) := by
  classical
  let eps : Real := G.p.ε
  have heps : 0 < eps := G.numerics.epsilon_pos
  have hmesh : (8 : Real) / G.M ≤ eps / 4 := by
    have hz := (G.numerics.zeta_mono 0 G.p.N (Nat.zero_le _) le_rfl).trans G.numerics.zeta_top
    have hes := G.numerics.epsilon_small
    have hm := G.numerics.M_zeta
    have hprod := mul_le_mul_of_nonneg_left hz heps.le
    have hsquare := mul_le_mul_of_nonneg_left hes.le heps.le
    dsimp only [eps] at *
    rw [show (8 : Real) / G.M = 8 * (1 / (G.M : Real)) by ring]
    nlinarith only [hm, hprod, hsquare, heps]
  let Ccap := ShadedTube.ssfUniformConst (Module.finrank Real E)
  let MED := lineSelectionMultiplicityW95 (Module.finrank Real E) 1 (Nat.floor (Ctw : Real))
  let K : NNReal := 2 * trialNearbyParentCountW96 Ctw *
    (Tube.volume_le.C 3 / Tube.le_volume.c 3) * Cwork ^ (2 : Nat) *
      Ccap ^ (3 : Nat) * BF ^ (G.p.N + 1)
  obtain ⟨dC, hdC, _hdC1, hC⟩ := exists_threshold_natCast_le_rpow
    (Nat.ceil (max (K : Real) 4)) (eps / 2) (by positivity)
  obtain ⟨d2, hd2, _hd21, h2⟩ := exists_threshold_natCast_le_rpow 2 (eps / 4) (by positivity)
  obtain ⟨dED, hdED, _hdED1, hEDpay⟩ :=
    exists_threshold_natCast_le_rpow MED (eps / 8) (by positivity)
  obtain ⟨dU, hdU, _hdU1, hU⟩ := ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
    (E := E) 7 (eps / 8) (eps / 4) (by positivity) (by positivity)
  obtain ⟨dJ, hdJ, _hdJ1, hJ⟩ := Tube.exists_threshold_polylog_pow_ssfGridLen_le
    1 le_rfl 0 1 1 one_pos
  filter_upwards [self_mem_nhdsWithin, eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
    eventually_le_nhdsGT hdC, eventually_le_nhdsGT hd2, eventually_le_nhdsGT hdED,
    eventually_le_nhdsGT hdU,
    eventually_le_nhdsGT hdJ, S.actual_sticky]
    with radius hradius hradius1 hrC hr2 hrED hrU hrJ hsticky
  have hr : 0 < radius := hradius
  have hrR : (0 : Real) < radius := hr
  have hr0 : (radius : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hr.ne'
  have hrTop : (radius : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hr1 : (radius : ENNReal) ≤ 1 := by exact_mod_cast hradius1
  have hcast (a : Real) : ENNReal.ofReal ((radius : Real) ^ a) =
      (radius : ENNReal) ^ a := (ennreal_coe_nnreal_rpow hrR a).symm
  have hconstR : max (K : Real) 4 ≤ (radius : Real) ^ (-(eps / 2)) :=
    (Nat.le_ceil _).trans (hC hr hrC)
  have hK : (K : ENNReal) ≤ (radius : ENNReal) ^ (-(eps / 2)) := by
    have h := ENNReal.ofReal_le_ofReal ((le_max_left (K : Real) 4).trans hconstR)
    simpa only [ENNReal.ofReal_coe_nnreal, hcast] using h
  have hfour : (4 : ENNReal) ≤ (radius : ENNReal) ^ (-(eps / 2)) := by
    have h := ENNReal.ofReal_le_ofReal ((le_max_right (K : Real) 4).trans hconstR)
    simpa only [ENNReal.ofReal_ofNat, hcast] using h
  have htwo : (2 : ENNReal) ≤ (radius : ENNReal) ^ (-(eps / 4)) := by
    have h2R : (2 : Real) ≤ (radius : Real) ^ (-(eps / 4)) := by
      exact_mod_cast h2 hr hr2
    have h := ENNReal.ofReal_le_ofReal h2R
    simpa only [ENNReal.ofReal_ofNat, hcast] using h
  have hhalfPower (a : Real) :
      (radius : ENNReal) ^ (a + eps / 4) ≤ (2 : ENNReal)⁻¹ * (radius : ENNReal) ^ a := by
    have h := mul_le_mul' htwo (le_refl ((radius : ENNReal) ^ (a + eps / 4)))
    rw [← ENNReal.rpow_add _ _ hr0 hrTop] at h
    have heq : -(eps / 4) + (a + eps / 4) = a := by ring
    rw [heq] at h
    calc
      _ = (2 : ENNReal)⁻¹ * (2 * (radius : ENNReal) ^ (a + eps / 4)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  have hquarterPower : (radius : ENNReal) ^ (2 * eps) ≤
      (4 : ENNReal)⁻¹ * (radius : ENNReal) ^ (3 * eps / 2) := by
    have h := mul_le_mul' hfour (le_refl ((radius : ENNReal) ^ (2 * eps)))
    rw [← ENNReal.rpow_add _ _ hr0 hrTop] at h
    have heq : -(eps / 2) + 2 * eps = 3 * eps / 2 := by ring
    rw [heq] at h
    calc
      _ = (4 : ENNReal)⁻¹ * (4 * (radius : ENNReal) ^ (2 * eps)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  intro iota _ A Z U hA hball hline hcard hfull hregular hEvery
  let lam : ENNReal := fullness' A (fun i => (Z i).toShadedBody)
  have hlamPos : 0 < lam := (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hr) hrTop).trans_le hfull
  have hlamTop : lam ≠ ⊤ := fullness'_ne_top _ _
  let i0 := hA.choose
  let v : ENNReal := volume (Z i0).carrier
  have hvPos : 0 < v := by
    apply lt_of_lt_of_le _ (Tube.le_volume (Z i0).toTube)
    exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos _).ne')
      (pow_ne_zero _ hr0)
  have hvTop : v ≠ ⊤ := (Z i0).isCompact.measure_ne_top
  have hvol (i : iota) : volume (Z i).carrier = v :=
    Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube
  have hcar (F : Finset iota) :
      (∑ i ∈ F, volume (Z i).carrier) = (F.card : ENNReal) * v :=
    Tube.sum_volume_carrier_eq_card_mul (fun i => (Z i).toTube) (Z i0).toTube F
  have hmass : (∑ i ∈ A, volume (Z i).shade) = lam * ((A.card : ENNReal) * v) := by
    rw [sum_volumeReal_shade_eq_fullness_mul A (fun i => (Z i).toShadedBody),
      coe_fullness, hcar]
  let D := discardLowShading A (fun i => (Z i).toShadedBody) (2⁻¹ : NNReal)
  have hDA : D ⊆ A := discardLowShading_subset _ _ _
  have hmassD : (2 : ENNReal)⁻¹ * (∑ i ∈ A, volume (Z i).shade) ≤
      ∑ i ∈ D, volume (Z i).shade := by
    have h := one_sub_mul_sum_volume_shade_le_sum_discardLowShading A
      (fun i => (Z i).toShadedBody) (c := (2⁻¹ : NNReal)) (by norm_num)
    simpa only [show ((1 - (2⁻¹ : NNReal) : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ by norm_num]
      using h
  have hterm : ∀ i ∈ D, (2 : ENNReal)⁻¹ * lam * v ≤ volume (Z i).shade := by
    intro i hi
    have h := le_volume_shade_of_mem_discardLowShading (c := (2⁻¹ : NNReal)) hi
    simpa only [show ((2⁻¹ : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ by norm_num,
      coe_fullness, hvol] using h
  have hcardD : (2 : ENNReal)⁻¹ * lam * (A.card : ENNReal) ≤ (D.card : ENNReal) := by
    have hupper : (∑ i ∈ D, volume (Z i).shade) ≤ (D.card : ENNReal) * v := by
      rw [← hcar]
      exact Finset.sum_le_sum fun i _ => measure_mono (Z i).shade_subset
    have h := hmassD.trans hupper
    rw [hmass] at h
    apply (ENNReal.mul_le_mul_iff_right hvPos.ne' hvTop).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hD : D.Nonempty := by
    have hpos : (0 : ENNReal) < (D.card : ENNReal) :=
      (ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) hlamPos.ne').ne'
        (by exact_mod_cast hA.card_pos.ne')).trans_le hcardD
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  have hDcard : (D.card : Real) ≤ (radius : Real) ^ (-7 : Real) :=
    (Nat.cast_le.mpr (Finset.card_le_card hDA)).trans hcard
  have hlineD : lineEssentiallyDistinctW94 D (fun i => (Z i).toTube) Ctw := by
    intro o d hd
    apply le_trans _ (hline o d hd)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hDA)
  have hcenterD : ∀ i ∈ D, ‖(Z i).center‖ ≤ (1 : Real) := by
    intro i hi
    have hm := Tube.norm_midpoint_le_of_subset_ball hr (Z i).toTube (hball i (hDA hi))
    have heq : (Z i).center = (Z i).toTube.midpoint := by
      change midpoint Real (Z i).x (Z i).y = (1 / 2 : Real) • ((Z i).x + (Z i).y)
      rw [midpoint_eq_smul_add]
      norm_num
    rw [heq]
    exact hm
  have hmassDpos : 0 < ∑ i ∈ D, volume (Z i).shade := by
    have hmassPos : 0 < ∑ i ∈ A, volume (Z i).shade := by
      rw [hmass]
      positivity
    exact lt_of_lt_of_le (ENNReal.mul_pos (by norm_num) hmassPos.ne') hmassD
  have hAline : 1 ≤ Nat.floor (Ctw : Real) := by
    apply (Nat.one_le_floor_iff (R := Real) (Ctw : Real)).mpr
    exact_mod_cast hCtw
  obtain ⟨Q, hQD, hQ, hQED, _hQmass, hQcard, _hQfull, _hQCF, _hQmax, _hQmu⟩ :=
    exists_pairwise_lineED_paid_w95 hr hradius1 D Z hD 1 (by norm_num) hcenterD
      (Nat.floor (Ctw : Real)) hAline
      ((pointwise_lineED_iff_library_floor_w95 D (fun i => (Z i).toTube) Ctw).mp hlineD)
      ConvexSpaceBody.closedUnitBall (fun i hi => SetLike.coe_subset_coe.mpr (hball i (hDA hi)))
      hmassDpos
  change D.card ≤ MED * Q.card at hQcard
  have hQcardReal : (Q.card : Real) ≤ (radius : Real) ^ (-7 : Real) :=
    (Nat.cast_le.mpr (Finset.card_le_card (hQD.trans hDA))).trans hcard
  obtain ⟨B, hBQ, W, hWTube, hWShade, hcardU, hfullU, ⟨V⟩⟩ :=
    hU hr hrU Q Z (fun i hi => hball i (hDA (hQD hi)))
      (by simpa only [Nat.cast_ofNat] using hQcardReal)
  have hBD : B ⊆ D := hBQ.trans hQD
  have hBA : B ⊆ A := hBD.trans hDA
  have hB : B.Nonempty := by
    by_contra h
    have hzero := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hzero] at hcardU
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hcardU
    exact (by exact_mod_cast hQ.card_pos : (0 : Real) < Q.card).not_ge hcardU
  have hcardUE : (D.card : ENNReal) ≤ (radius : ENNReal) ^ (-(eps / 4)) * (B.card : ENNReal) := by
    have hMED : (MED : Real) ≤ (radius : Real) ^ (-(eps / 8)) := hEDpay hr hrED
    have hQcardR : (D.card : Real) ≤ (MED : Real) * (Q.card : Real) := by
      exact_mod_cast hQcard
    have hcombined : (D.card : Real) ≤ (radius : Real) ^ (-(eps / 4)) * (B.card : Real) := by
      calc
        (D.card : Real) ≤ (MED : Real) * (Q.card : Real) := hQcardR
        _ ≤ (radius : Real) ^ (-(eps / 8)) * (Q.card : Real) := by gcongr
        _ ≤ (radius : Real) ^ (-(eps / 8)) *
            ((radius : Real) ^ (-(eps / 8)) * (B.card : Real)) := by gcongr
        _ = (radius : Real) ^ (-(eps / 4)) * (B.card : Real) := by
          rw [← mul_assoc, ← Real.rpow_add hrR]
          congr 1
          ring
    have h := ENNReal.ofReal_le_ofReal hcombined
    simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg hrR.le _), ENNReal.ofReal_natCast, hcast] using h
  have hBED : (B : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (W i).carrier (W j).carrier) := by
    intro i hi j hj hij
    change IsEssentiallyDistinct ((W i).toTube).carrier ((W j).toTube).carrier
    rw [hWTube i, hWTube j]
    exact hQED (hBQ hi) (hBQ hj) hij
  have hcardLower : (radius : ENNReal) ^ (eps / 4) *
      ((2 : ENNReal)⁻¹ * lam) * (A.card : ENNReal) ≤ (B.card : ENNReal) := by
    calc
      _ = (radius : ENNReal) ^ (eps / 4) * ((2 : ENNReal)⁻¹ * lam * (A.card : ENNReal)) := by ring
      _ ≤ (radius : ENNReal) ^ (eps / 4) *
          ((radius : ENNReal) ^ (-(eps / 4)) * (B.card : ENNReal)) :=
        mul_le_mul' le_rfl (hcardD.trans hcardUE)
      _ = _ := by rw [← mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrTop]; simp
  have hfullBZ : (2 : ENNReal)⁻¹ * lam ≤ fullness' B (fun i => (Z i).toShadedBody) := by
    rw [fullness', hcar]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.mul_pos (by exact_mod_cast hB.card_pos.ne') hvPos.ne').ne')
      (Or.inl (ENNReal.mul_ne_top (by finiteness) hvTop))).mpr
    calc
      _ = ∑ _i ∈ B, (2 : ENNReal)⁻¹ * lam * v := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i hi => hterm i (hBD hi)
  have hfullW : (radius : ENNReal) ^ (eps / 4) * ((2 : ENNReal)⁻¹ * lam) ≤
      fullness' B (fun i => (W i).toShadedBody) := by
    rw [hcast] at hfullU
    calc
      _ ≤ (radius : ENNReal) ^ (eps / 4) *
          ((radius : ENNReal) ^ (-(eps / 4)) * fullness' B (fun i => (W i).toShadedBody)) :=
        mul_le_mul' le_rfl (hfullBZ.trans hfullU)
      _ = _ := by rw [← mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrTop]; simp
  have hpowerLam : (2 : ENNReal)⁻¹ * (radius : ENNReal) ^ (5 * eps / 4) ≤
      (radius : ENNReal) ^ (eps / 4) * ((2 : ENNReal)⁻¹ * lam) := by
    calc
      _ = (radius : ENNReal) ^ (eps / 4) * ((2 : ENNReal)⁻¹ * (radius : ENNReal) ^ eps) := by
        have hp : (radius : ENNReal) ^ (eps / 4) * (radius : ENNReal) ^ eps =
            (radius : ENNReal) ^ (5 * eps / 4) := by
          rw [← ENNReal.rpow_add _ _ hr0 hrTop]
          congr 1
          ring
        rw [← hp]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl hfull)
  have hcountStrong : ((2 : ENNReal)⁻¹ * (radius : ENNReal) ^ (5 * eps / 4)) *
      (A.card : ENNReal) ≤ (B.card : ENNReal) :=
    (mul_le_mul' hpowerLam le_rfl).trans hcardLower
  have hpowerCard : (radius : ENNReal) ^ (3 * eps / 2) ≤
      (2 : ENNReal)⁻¹ * (radius : ENNReal) ^ (5 * eps / 4) := by
    convert hhalfPower (5 * eps / 4) using 1 <;> congr 1 <;> ring
  have hcardPaidE := (mul_le_mul' hpowerCard (le_refl (A.card : ENNReal))).trans hcountStrong
  have hcardPaid : (radius : Real) ^ (3 * eps / 2) * (A.card : Real) ≤ (B.card : Real) := by
    have h := ENNReal.toReal_mono (by finiteness : (B.card : ENNReal) ≠ ⊤) hcardPaidE
    have hx : ((radius : ENNReal) ^ (3 * eps / 2)).toReal = (radius : Real) ^ (3 * eps / 2) := by
      rw [← hcast, ENNReal.toReal_ofReal (Real.rpow_nonneg hrR.le _)]
    simpa only [ENNReal.toReal_mul, hx, ENNReal.toReal_natCast] using h
  have hfullPaid : (radius : ENNReal) ^ (2 * eps) ≤ fullness' B (fun i => (W i).toShadedBody) :=
    (ENNReal.rpow_le_rpow_of_exponent_ge hr1 (by linarith only [heps] :
      3 * eps / 2 ≤ 2 * eps)).trans (hpowerCard.trans (hpowerLam.trans hfullW))
  have hcarW : (∑ i ∈ B, volume (W i).carrier) = (B.card : ENNReal) * v := by
    have hbody : ∀ i, (W i).carrier = (Z i).carrier :=
      fun i => congrArg (fun T : Tube radius E => T.carrier) (hWTube i)
    simp_rw [hbody]
    exact hcar B
  have hmassW : (∑ i ∈ B, volume (W i).shade) =
      fullness' B (fun i => (W i).toShadedBody) * ((B.card : ENNReal) * v) := by
    rw [sum_volumeReal_shade_eq_fullness_mul B (fun i => (W i).toShadedBody),
      coe_fullness, hcarW]
  have hmassLower : (4 : ENNReal)⁻¹ * (radius : ENNReal) ^ (eps / 2) * lam *
      (∑ i ∈ A, volume (Z i).shade) ≤ ∑ i ∈ B, volume (W i).shade := by
    rw [hmass, hmassW]
    calc
      _ = ((radius : ENNReal) ^ (eps / 4) * ((2 : ENNReal)⁻¹ * lam)) *
          (((radius : ENNReal) ^ (eps / 4) * ((2 : ENNReal)⁻¹ * lam) * (A.card : ENNReal)) * v) := by
        have hp : (radius : ENNReal) ^ (eps / 4) * (radius : ENNReal) ^ (eps / 4) =
            (radius : ENNReal) ^ (eps / 2) := by
          rw [← ENNReal.rpow_add _ _ hr0 hrTop]
          congr 1
          ring
        calc
          _ = (4 : ENNReal)⁻¹ * ((radius : ENNReal) ^ (eps / 4) *
              (radius : ENNReal) ^ (eps / 4)) * lam * (lam * ((A.card : ENNReal) * v)) := by rw [hp]
          _ = _ := by
            have hc : (4 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
              rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
              norm_num
            rw [hc]
            ring
      _ ≤ _ := mul_le_mul' hfullW (mul_le_mul' hcardLower le_rfl)
  have hmassPaid : (radius : ENNReal) ^ (2 * eps) * (∑ i ∈ A, volume (Z i).shade) ≤
      ∑ i ∈ B, volume (W i).shade := by
    apply le_trans _ hmassLower
    apply mul_le_mul' _ le_rfl
    calc
      _ ≤ (4 : ENNReal)⁻¹ * (radius : ENNReal) ^ (3 * eps / 2) := hquarterPower
      _ = (4 : ENNReal)⁻¹ * (radius : ENNReal) ^ (eps / 2) * (radius : ENNReal) ^ eps := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrTop]
        congr 2
        ring
      _ ≤ _ := mul_le_mul' le_rfl hfull
  let L : NNReal := 2 * radius ^ (-(5 * eps / 4))
  have hL : (A.card : NNReal) ≤ L * (B.card : NNReal) := by
    apply ENNReal.coe_le_coe.mp
    simp only [L, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_natCast,
      ENNReal.coe_rpow_of_ne_zero hr.ne']
    calc
      _ = (2 * (radius : ENNReal) ^ (-(5 * eps / 4))) *
          (((2 : ENNReal)⁻¹ * (radius : ENNReal) ^ (5 * eps / 4)) * (A.card : ENNReal)) := by
        calc
          _ = (2 * (2 : ENNReal)⁻¹) * ((radius : ENNReal) ^ (-(5 * eps / 4)) *
              (radius : ENNReal) ^ (5 * eps / 4)) * (A.card : ENNReal) := by
            rw [← ENNReal.rpow_add _ _ hr0 hrTop,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
            simp
          _ = _ := by ring
      _ ≤ _ := mul_le_mul' le_rfl hcountStrong
  let VZ := V.tubeUniform.copyTubes (fun i => (hWTube i).symm)
  have htransfer := mixed_grid_frostman_transfer_w110 hdim hr hradius1 G.numerics.M_pos
    (Nat.succ_le_iff.mpr (hJ hr hrJ).1) A B Z hA hB hBA hball hCtw U hregular VZ hL hEvery
  have hprice : (trialNearbyParentCountW96 Ctw : ENNReal) *
      ((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
      (Cwork : ENNReal) ^ (2 : Nat) * (Ccap : ENNReal) ^ (3 : Nat) *
      (L : ENNReal) * (radius : ENNReal) ^ (-(8 : Real) / (G.M : Real)) *
      ((BF : ENNReal) ^ (G.p.N + 1) * (radius : ENNReal) ^ (-3 * eps)) ≤
        (radius : ENNReal) ^ (-5 * eps) := by
    calc
      _ = (K : ENNReal) * (radius : ENNReal) ^ (-(5 * eps / 4)) *
          (radius : ENNReal) ^ (-(8 : Real) / (G.M : Real)) *
          (radius : ENNReal) ^ (-3 * eps) := by
        simp only [K, L, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, ENNReal.coe_natCast,
          ENNReal.coe_rpow_of_ne_zero hr.ne']
        ring
      _ ≤ (radius : ENNReal) ^ (-(eps / 2)) * (radius : ENNReal) ^ (-(5 * eps / 4)) *
          (radius : ENNReal) ^ (-(eps / 4)) * (radius : ENNReal) ^ (-3 * eps) := by
        apply mul_le_mul' _ le_rfl
        apply mul_le_mul' (mul_le_mul' hK le_rfl)
        exact ENNReal.rpow_le_rpow_of_exponent_ge hr1
          (by simpa only [neg_div] using neg_le_neg hmesh)
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ hr0 hrTop, ← ENNReal.rpow_add _ _ hr0 hrTop,
          ← ENNReal.rpow_add _ _ hr0 hrTop]
        congr 1
        ring
  have hVEvery : V.tubeUniform.IsFrostmanAtEveryScale ((radius : ENNReal) ^ (-5 * eps)) := by
    have hpaid := htransfer.mono hprice
    have hbody : ∀ i, (W i).toConvexSpaceBody = (Z i).toConvexSpaceBody :=
      fun i => congrArg Tube.toConvexSpaceBody (hWTube i)
    intro k hk j hj
    simpa only [VZ, Tube.UniformTubeSet.copyTubes, hbody] using hpaid k hk j hj
  have hWBall : ∀ i ∈ B, (W i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    change (W i).toTube.carrier ⊆ _
    rw [hWTube i]
    exact hball i (hBA hi)
  have hstickyFull : (radius : ENNReal) ^ S.etaStar ≤
      (fullness B (fun i => (W i).toShadedBody) : ENNReal) := by
    rw [coe_fullness]
    apply le_trans _ hfullPaid
    exact ENNReal.rpow_le_rpow_of_exponent_ge hr1
      (by have hm := G.sticky_margin; have hs := S.etaStar_pos; dsimp only [eps]; linarith)
  have hstickyEvery := hVEvery.mono (ENNReal.rpow_le_rpow_of_exponent_ge hr1
    (by have hm := G.sticky_margin; have hs := S.etaStar_pos; dsimp only [eps]; linarith :
      -S.etaStar ≤ -5 * eps))
  have hunion := hsticky B W hWBall hBED le_rfl V hstickyFull hstickyEvery
  exact ⟨B, W, V, hB, hBA, hWTube, hWShade, hcardPaid, hmassPaid, hfullPaid, hVEvery, hunion⟩

end

end Kakeya.ml1Boot.FixedMStickyExitW110

namespace Kakeya.ml1Boot.RevisedSourceRepairW110

noncomputable section
set_option autoImplicit false

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open TrialRestartW94

private theorem eventually_original_good_payment_w111
    {xi c gamma accuracy : Real}
    (hxi : 0 < xi) (hc : 0 < c) (hcx : c <= xi)
    (hgamma : gamma ∈ Set.Icc (0 : Real) 1)
    (haccuracy : 0 < accuracy)
    (K : ENNReal) (hK : K ≠ ⊤) :
    ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
      ∀ (n : Nat), 1 <= n ->
      K * (delta : ENNReal) ^ (16 * xi) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((n : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - c)) *
          ((n : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^
            (1 - (gamma - c) / 2) := by
  have hgap : 3 * c - accuracy / 4 < 16 * xi := by
    linarith only [hcx, hxi, haccuracy]
  filter_upwards [eventually_mul_rpow_le_rpow hK hgap,
    self_mem_nhdsWithin] with delta hpay hd
  have hdpos : 0 < delta := hd
  have hd0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hdpos).ne'
  have hdtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hq : 0 <= 1 - gamma / 2 := by linarith only [hgamma.2]
  have hr : 0 <= c / 2 := (half_pos hc).le
  intro n hn
  let X : ENNReal := (n : ENNReal) * (delta : ENNReal) ^ (2 : Nat)
  have hnE : (1 : ENNReal) <= n := by exact_mod_cast hn
  have hX : (delta : ENNReal) ^ (2 : Nat) <= X :=
    le_mul_of_one_le_left zero_le hnE
  have hgain : (delta : ENNReal) ^ c <= X ^ (c / 2) := by
    calc
      (delta : ENNReal) ^ c = ((delta : ENNReal) ^ (2 : Nat)) ^ (c / 2) := by
        rw [← ENNReal.rpow_natCast_mul]
        congr 1
        norm_num
        ring
      _ <= X ^ (c / 2) := ENNReal.rpow_le_rpow hX hr
  have hsplit : (delta : ENNReal) ^ (3 * c - accuracy / 4) *
      (delta : ENNReal) ^ (-2 * gamma) =
      (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        (delta : ENNReal) ^ c := by
    rw [← ENNReal.rpow_add _ _ hd0 hdtop, ← ENNReal.rpow_add _ _ hd0 hdtop]
    congr 1
    ring
  calc
    K * (delta : ENNReal) ^ (16 * xi) * (delta : ENNReal) ^ (-2 * gamma) *
        X ^ (1 - gamma / 2) <=
        (delta : ENNReal) ^ (3 * c - accuracy / 4) *
          (delta : ENNReal) ^ (-2 * gamma) * X ^ (1 - gamma / 2) :=
      mul_le_mul' (mul_le_mul' hpay le_rfl) le_rfl
    _ = (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        ((delta : ENNReal) ^ c * X ^ (1 - gamma / 2)) := by
      rw [hsplit, mul_assoc]
    _ <= (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        (X ^ (c / 2) * X ^ (1 - gamma / 2)) :=
      mul_le_mul' le_rfl (mul_le_mul' hgain le_rfl)
    _ = (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - c)) *
        X ^ (1 - (gamma - c) / 2) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hr hq]
      congr 2
      ring

/-- The main revised-source producer. Constants are chosen before A, A
before I, and all before delta and the family. The same-mass two-scale
construction, actual eligible Inner Trial calls, good/drop alternatives,
persistent canonical restart and final exponent payment belong here.
There is no supplied analytic callback, trace or original-s conclusion. -/
theorem exists_certified_original_runs_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (S : StickyWitnessW110.{uE, uI} E gammaZero)
    (G : SourceStructureW110 beta gammaZero S.etaStar)
    {gamma : Real} (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    {accuracy : Real} (haccuracy : 0 < accuracy) :
    ∃ (Ctw Ccell : NNReal), 1 <= Ctw ∧ 1 <= Ccell ∧
      ∃ (A : AnalyticScheduleW110.{uE, uI} (E := E) G gamma Ctw Ccell)
        (I : InputChoiceW110 A accuracy),
        ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
          ∀ {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E),
            OriginalInputW110 s Y I.inputEta ->
            BandedInputW110 s Y I.workingEta ->
            Nonempty (OriginalRunW110 s Y gamma G.p.c accuracy) := by
  classical
  have hp := G.numerics
  have heps := hp.epsilon_pos
  have hxi := hp.xiMin_pos
  have hstep := source_step_positive_w110 G
  have hgammaPos : 0 < gamma := (hbeta.trans_lt hgammaZero.1).trans_le hgamma.1
  have hq : 0 <= 1 - gamma / 2 := by linarith [hgamma.2]
  obtain ⟨_, _, hKTPrime⟩ := shifted_estimate_for_source_w110 hbeta hgammaZero hKT
  obtain ⟨Cline, hCline, hline⟩ := eventually_source_line_budget_of_protected_ED_w103 hdim
  obtain ⟨A0, F0, hA0, hF0, hcentre⟩ := exists_source_centring_reduction_w101 (E := E) hdim
  have hA01 : 1 <= A0 := by rw [hA0]; norm_num
  have hF01 : 1 <= F0 := by rw [hF0]; norm_num
  let bLoss := min G.xiMin (min (G.p.ε / 4) (accuracy / 100))
  have hbLoss : 0 < bLoss := lt_min hxi (lt_min (by positivity) (by positivity))
  have hbLossXi : bLoss <= G.xiMin := min_le_left _ _
  have hbLossEps : bLoss <= G.p.ε / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hbLossAccuracy : bLoss <= accuracy / 100 :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Cgood, Cwork, Ctw, Ccell, BF, eInput, deltaRun,
    hCgood, hCwork, hCtw, hCcell, hBF, heInput, heInputSmall,
    hdeltaRun, hdeltaRun1, hRun⟩ :=
    exists_source_input_alternative_w104 hdim hp hgamma hKTPrime hKF A0 hA01 bLoss hbLoss
  obtain ⟨A⟩ := exists_actual_analytic_schedule_w110 hdim G hgamma hKT hKF Ctw Ccell hCtw hCcell
  obtain ⟨J⟩ := exists_input_choice_w110 A haccuracy
  let working := min J.workingEta (min (eInput / 4) (G.xiMin / 100))
  have hw : 0 < working := lt_min J.working_pos (lt_min (by positivity) (by positivity))
  have hwJ : working <= J.workingEta := min_le_left _ _
  have hwInput : working <= eInput / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hwXi : working <= G.xiMin / 100 := (min_le_right _ _).trans (min_le_right _ _)
  let I : InputChoiceW110 A accuracy :=
    { workingEta := working
      inputEta := working / 8
      working_pos := hw
      input_pos := by positivity
      input_eq := rfl
      ladder_reserve := hwJ.trans J.ladder_reserve
      sticky_reserve := hwJ.trans J.sticky_reserve
      inner_reserve := fun m hm => hwJ.trans (J.inner_reserve m hm)
      gain_reserve := hwJ.trans J.gain_reserve
      cf_reserve := fun m hm => hwJ.trans (J.cf_reserve m hm)
      KT_reserve := hwJ.trans J.KT_reserve
      KF_reserve := hwJ.trans J.KF_reserve
      requested_loss_reserve := hwJ.trans J.requested_loss_reserve
      unit_reserve := hwJ.trans J.unit_reserve }
  let B : NNReal := F0 * Cline
  have hB : 1 <= B := one_le_mul hF01 hCline
  have hB0 : (B : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hB))
  have hfullPay := eventually_mul_rpow_le_rpow (K := (384 : ENNReal) * B)
    (by finiteness) (show eInput / 4 < eInput / 2 by linarith)
  have hCFPay := eventually_mul_rpow_le_rpow (K := (196608 : ENNReal) * B)
    (by finiteness) (show -eInput < -(eInput / 4) by linarith)
  let Kgood : ENNReal := (B : ENNReal) * Cgood * (2 : ENNReal) ^ (2 * gamma)
  have hGoodPayment : ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
      ∀ n : Nat, 1 <= n ->
        Kgood * (delta : ENNReal) ^ (16 * G.xiMin) *
            (delta : ENNReal) ^ (-2 * gamma) *
            ((n : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) <=
          (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - G.p.c)) *
            ((n : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^
              (1 - (gamma - G.p.c) / 2) := by
    exact eventually_original_good_payment_w111 hxi hstep.1 hstep.2.2.2.1
      ⟨hgammaPos.le, hgamma.2⟩ haccuracy Kgood (by dsimp only [Kgood]; finiteness)
  have hStickyUnion : ∀ᶠ (radius : NNReal) in 𝓝[>] 0,
      ∀ {iota : Type uI} [DecidableEq iota]
        (T : Finset iota) (W : iota -> ShadedTube radius E)
        (U : RevisedLiteralProfileInterfaceFormalizerW87.CanonicalProfileNetW87
          T (fun i => (W i).toTube) G.M Cwork),
        T.Nonempty -> (∀ i ∈ T, (W i).carrier ⊆ Metric.closedBall 0 1) ->
        lineEssentiallyDistinctW94 T (fun i => (W i).toTube) Ctw ->
        (T.card : Real) <= (radius : Real) ^ (-7 : Real) ->
        (radius : ENNReal) ^ G.p.ε <= fullness' T (fun i => (W i).toShadedBody) ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        U.IsFrostmanAtEveryScale
          ((BF : ENNReal) ^ (G.p.N + 1) * (radius : ENNReal) ^ (-3 * G.p.ε)) ->
        (radius : ENNReal) ^ (gammaZero / 4) <= volume (⋃ i ∈ T, (W i).shade) := by
    have hexit := FixedMStickyExitW110.eventually_fixed_m_sticky_exit_w110
      hdim S G Cwork Ctw Ccell BF hCwork hCtw hCcell hBF
    filter_upwards [hexit] with radius hfinal
    intro iota _ T W U hT hball hline hcard hfull hregular hevery
    obtain ⟨Bnew, Wnew, Vnew, hBnew, hBT, hsameNew, hshadeNew,
      hcardNew, hmassNew, hfullNew, hfrostmanNew, hvolumeNew⟩ :=
      hfinal T W U hT hball hline hcard hfull hregular hevery
    apply hvolumeNew.trans
    apply measure_mono
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hBT hi, hshadeNew i hxi⟩
  obtain ⟨deltaSticky, hdeltaSticky, hStickyAt⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hStickyUnion
  have hCardPay := eventually_mul_rpow_le_rpow (K := (cardBound.C : ENNReal))
    ENNReal.coe_ne_top (show (-7 : Real) < -4 by norm_num)
  let Cvol : ENNReal := Tube.volume_le.C (Module.finrank Real E)
  let Ccard : ENNReal := cardBound.C
  let Ksticky : ENNReal := Cvol * Ccard * (2 : ENNReal) ^ (gammaZero / 4)
  have hStickyPay := eventually_finite_const_le_rpow_neg (c := Ksticky)
    (by dsimp only [Ksticky, Cvol, Ccard]; finiteness)
    (show 0 < accuracy / 4 by positivity)
  refine ⟨Ctw, Ccell, hCtw, hCcell, A, I, ?_⟩
  filter_upwards [hline, hfullPay, hCFPay, hGoodPayment, hCardPay, hStickyPay, self_mem_nhdsWithin,
    eventually_le_nhdsGT (show (0 : NNReal) < deltaRun / 2 by positivity),
    eventually_le_nhdsGT (half_pos hdeltaSticky),
    eventually_le_nhdsGT (show (0 : NNReal) < 1 / 200 by norm_num)] with
    delta hline hfullPay hCFPay hGoodPayment hCardPay hStickyPay hd hdRun hdSticky hdsmall
  intro iota s Y hinput band
  have hdpos : 0 < delta := hd
  have hd1 : delta <= 1 := hdsmall.trans
    (div_le_self (show (0 : NNReal) <= 1 from zero_le) (by norm_num))
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hd1E : (delta : ENNReal) <= 1 := by exact_mod_cast hd1
  have hr : 0 < delta / 2 := div_pos hdpos (by norm_num)
  have hrdelta : delta / 2 <= delta := div_le_self (show (0 : NNReal) <= delta from zero_le) (by norm_num)
  have hr1 : delta / 2 <= 1 := hrdelta.trans hd1
  have hrRun : delta / 2 < deltaRun :=
    (hrdelta.trans hdRun).trans_lt (by exact half_lt_self hdeltaRun)
  have hs : s.Nonempty := band.nonempty.mono band.subset
  have hbandBall := fun i hi => hinput.ball i (band.subset hi)
  have hbandED := hinput.essentially_distinct.mono (Finset.coe_subset.mpr band.subset)
  obtain ⟨F, parent, Z, hF, hFband, himage, hballZ, hcentredZ, hlineZ,
    hcoverZ, hfibres, hvolZ, hshadeZ, hunionZ, hunionVolZ,
    hcardZLower, hcardZ, hmuZLower, hmuZUpper, hfullZ, hmaxZ, hmassZ⟩ :=
    hcentre hd hdsmall band.s2 Y Cline hCline band.nonempty hbandBall
      (hline band.s2 (fun i => (Y i).toTube) hbandBall hbandED)
  have hballZ1 : ∀ j ∈ F, (Z j).carrier ⊆ Metric.closedBall 0 1 := by
    intro j hj
    exact (hballZ j hj).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hbandFull : (delta : ENNReal) ^ working <=
      fullness' band.s2 (fun i => (Y i).toShadedBody) := by
    simpa only [← ShadedBody.coe_fullness] using
      band.hereditary_fullness band.s2 Finset.Subset.rfl band.nonempty
  have hfullInput : ((delta / 2 : NNReal) : ENNReal) ^ eInput <=
      fullness' F (fun i => (Z i).toShadedBody) := by
    have hlower : (delta : ENNReal) ^ (eInput / 2) <=
        fullness' F (fun i => (Z i).toShadedBody) := by
      have hpaid : ((384 : ENNReal) * B) * (delta : ENNReal) ^ (eInput / 2) <=
          fullness' band.s2 (fun i => (Y i).toShadedBody) :=
        hfullPay.trans ((ENNReal.rpow_le_rpow_of_exponent_ge hd1E hwInput).trans hbandFull)
      have hdivide : (delta : ENNReal) ^ (eInput / 2) <=
          fullness' band.s2 (fun i => (Y i).toShadedBody) /
            ((384 : ENNReal) * B) := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl (by simp [hB0]))
          (Or.inl (by finiteness))).mpr
        simpa only [mul_comm] using hpaid
      exact hdivide.trans (by simpa only [B, ENNReal.coe_mul, mul_assoc] using hfullZ)
    exact (ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) heInput.le).trans
      ((ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith)).trans hlower)
  have hCFZ : frostmanConstIn F (fun i => (Z i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <=
        (196608 : ENNReal) * B * (delta : ENNReal) ^ (-working) := by
    have h := centred_image_frostman_w103 hdim hdsmall band.s2 band.nonempty
      (fun i => (Y i).toTube) parent (fun i => (Z i).toTube) B hbandBall
      (by simpa only [himage] using hballZ1) hcoverZ
      (by simpa only [himage, B] using hfibres)
    rw [himage] at h
    simp only [← frostmanConstIn_eq_frostmanConstant] at h
    exact h.trans (mul_le_mul' le_rfl band.frostman)
  have hCFInput : frostmanConstIn F (fun i => (Z i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= ((delta / 2 : NNReal) : ENNReal) ^ (-eInput) := by
    calc
      _ <= (196608 : ENNReal) * B * (delta : ENNReal) ^ (-working) := hCFZ
      _ <= (196608 : ENNReal) * B * (delta : ENNReal) ^ (-(eInput / 4)) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith))
      _ <= (delta : ENNReal) ^ (-eInput) := hCFPay
      _ <= _ := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr
          (ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) heInput.le)
  have hmassOriginal : (∑ i ∈ s, volume (Y i).shade) <=
      (delta : ENNReal) ^ (-working) * (∑ i ∈ band.s2, volume (Y i).shade) := by
    rw [ENNReal.rpow_neg]
    have hp0 : (delta : ENNReal) ^ working ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hd0]
    have hpTop : (delta : ENNReal) ^ working ≠ ⊤ := by finiteness
    calc
      _ = ((delta : ENNReal) ^ working)⁻¹ *
          ((delta : ENNReal) ^ working * (∑ i ∈ s, volume (Y i).shade)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]
      _ <= _ := mul_le_mul_right band.original_mass_retention _
  have hmuOriginal : ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
      (delta : ENNReal) ^ (-working) * (B : ENNReal) *
        ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) := by
    have hmu := multiplicity_le_mul_of_subset_of_shade_mass band.subset
      (fun i => (Y i).toShadedBody) hmassOriginal
    calc
      _ <= (delta : ENNReal) ^ (-working) *
          ShadedBody.multiplicity band.s2 (fun i => (Y i).toShadedBody) := hmu
      _ <= (delta : ENNReal) ^ (-working) * ((B : ENNReal) *
          ShadedBody.multiplicity F (fun i => (Z i).toShadedBody)) :=
        mul_le_mul_right (by simpa only [B, ENNReal.coe_mul] using hmuZUpper) _
      _ = _ := by rw [mul_assoc]
  have hFS : F ⊆ s := hFband.trans band.subset
  have hcardFS : F.card <= s.card := Finset.card_le_card hFS
  have hscalar : ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
      (delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - G.p.c)) *
        ((s.card : ENNReal) * (delta : ENNReal) ^
          (Module.finrank Real E - 1)) ^ (1 - (gamma - G.p.c) / 2) := by
    rcases hRun hr hrRun F Z hF hballZ1 hcentredZ hlineZ hfullInput hCFInput with
      hgood | hevery
    · have hgain : 0 <= 18 * G.xiMin - bLoss := by linarith
      have hscaleGain : ((delta / 2 : NNReal) : ENNReal) ^ (18 * G.xiMin - bLoss) <=
          (delta : ENNReal) ^ (18 * G.xiMin - bLoss) :=
        ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) hgain
      have hscaleNegative : ((delta / 2 : NNReal) : ENNReal) ^ (-2 * gamma) =
          (delta : ENNReal) ^ (-2 * gamma) * (2 : ENNReal) ^ (2 * gamma) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hr.ne', NNReal.div_rpow,
          ENNReal.coe_div (by simp), ENNReal.coe_rpow_of_ne_zero hdpos.ne',
          ENNReal.coe_rpow_of_ne_zero (by norm_num : (2 : NNReal) ≠ 0)]
        norm_num only [ENNReal.coe_ofNat]
        rw [show -2 * gamma = -(2 * gamma) by ring, ENNReal.rpow_neg (2 : ENNReal),
          div_eq_mul_inv, inv_inv]
      have hscaledCard : (F.card : ENNReal) * ((delta / 2 : NNReal) : ENNReal) ^ (2 : Nat) <=
          (s.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat) := by
        exact mul_le_mul' (by exact_mod_cast hcardFS)
          (pow_le_pow_left' (by exact_mod_cast hrdelta) 2)
      have hrow : ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
          Kgood * (delta : ENNReal) ^ (16 * G.xiMin) * (delta : ENNReal) ^ (-2 * gamma) *
            ((s.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        calc
          _ <= (delta : ENNReal) ^ (-working) * (B : ENNReal) *
              ((Cgood : ENNReal) * ((delta / 2 : NNReal) : ENNReal) ^ (18 * G.xiMin - bLoss) *
                ((delta / 2 : NNReal) : ENNReal) ^ (-2 * gamma) *
                ((F.card : ENNReal) * ((delta / 2 : NNReal) : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2)) :=
            hmuOriginal.trans (mul_le_mul_right hgood _)
          _ <= (delta : ENNReal) ^ (-working) * (B : ENNReal) *
              ((Cgood : ENNReal) * (delta : ENNReal) ^ (18 * G.xiMin - bLoss) *
                ((delta : ENNReal) ^ (-2 * gamma) * (2 : ENNReal) ^ (2 * gamma)) *
                ((s.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2)) := by
            rw [hscaleNegative]
            gcongr
          _ = Kgood * ((delta : ENNReal) ^ (-working) *
                (delta : ENNReal) ^ (18 * G.xiMin - bLoss)) * (delta : ENNReal) ^ (-2 * gamma) *
                ((s.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
            dsimp only [Kgood]
            ring
          _ <= _ := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith))) le_rfl) le_rfl
      exact hrow.trans (by simpa only [hdim] using hGoodPayment s.card hs.card_pos)
    · obtain ⟨T, W, U, hT, hTF, hsame, hshade, hretained, hregular, hfrostman⟩ := hevery
      have hTball : ∀ i ∈ T, (W i).carrier ⊆ Metric.closedBall 0 1 := by
        intro i hi
        change (W i).toTube.carrier ⊆ _
        rw [hsame i hi]
        exact hballZ1 i (hTF hi)
      have hcardOriginal : (s.card : ENNReal) <=
          (cardBound.C : ENNReal) * (delta : ENNReal) ^ (-4 : Real) :=
        card_le hdim hdpos hd1 s (fun i => (Y i).toTube) hinput.ball hinput.essentially_distinct
      have hcardT : (T.card : ENNReal) <= ((delta / 2 : NNReal) : ENNReal) ^ (-7 : Real) := by
        calc
          _ <= (s.card : ENNReal) := by exact_mod_cast Finset.card_le_card (hTF.trans hFS)
          _ <= (delta : ENNReal) ^ (-7 : Real) := hcardOriginal.trans hCardPay
          _ <= _ := by
            rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
            exact ENNReal.inv_le_inv.mpr
              (ENNReal.rpow_le_rpow (by exact_mod_cast hrdelta) (by norm_num))
      have hcardTReal : (T.card : Real) <= ((delta / 2 : NNReal) : Real) ^ (-7 : Real) := by
        have h := ENNReal.toReal_mono (by finiteness) hcardT
        simpa only [ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using h
      obtain ⟨i0, hi0⟩ := hF
      obtain ⟨hv, hvTop⟩ := Tube.volume_pos_and_lt_top hr hr1 (Z i0).toTube
      have hrE : (0 : ENNReal) < (delta / 2 : NNReal) := ENNReal.coe_pos.mpr hr
      obtain ⟨_, hfullT, _, _⟩ := retained_state_fullness_card_frostman_w94
        F T (fun i => (Z i).toShadedBody) (fun i => (W i).toShadedBody)
        ConvexSpaceBody.closedUnitBall (volume (Z i0).carrier)
        (((delta / 2 : NNReal) : ENNReal) ^ eInput)
        (((delta / 2 : NNReal) : ENNReal) ^ (-eInput))
        (((delta / 2 : NNReal) : ENNReal) ^ bLoss)
        ⟨i0, hi0⟩ hTF hv hvTop
        (fun i hi => Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube)
        hballZ1 ConvexSpaceBody.closedUnitBall_volume_pos
        ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
        (fun i hi => congrArg Tube.toConvexSpaceBody (hsame i hi)) hshade
        (ENNReal.rpow_pos hrE ENNReal.coe_ne_top) (by finiteness) hfullInput hCFInput
        (by finiteness) (ENNReal.rpow_pos hrE ENNReal.coe_ne_top) (by finiteness) hretained
      have heInputEps : eInput <= G.p.ε / 4 := by
        have hzeta := (hp.zeta_mono 0 G.p.N (Nat.zero_le _) le_rfl).trans hp.zeta_top
        linarith
      have hfullTEps : ((delta / 2 : NNReal) : ENNReal) ^ G.p.ε <=
          fullness' T (fun i => (W i).toShadedBody) := by
        rw [← ENNReal.rpow_add _ _ hrE.ne' ENNReal.coe_ne_top] at hfullT
        exact (ENNReal.rpow_le_rpow_of_exponent_ge
          (by exact_mod_cast hr1) (by linarith)).trans hfullT
      have hrSticky : delta / 2 < deltaSticky :=
        (hrdelta.trans hdSticky).trans_lt (half_lt_self hdeltaSticky)
      have hlineT : lineEssentiallyDistinctW94 T (fun i => (W i).toTube) Ctw := by
        intro o v hv
        apply le_trans _ (hregular.some.parent_line_ed G.M le_rfl o v hv)
        exact_mod_cast Finset.card_le_card (show
          T.filter (fun i => liesInFiveDeltaLineTubeW94 (W i).toTube o v) ⊆
            (U.cover.indexSet G.M).filter
              (fun i => liesInFiveDeltaLineTubeW94 (U.cover.tube G.M i) o v) from by
            intro i hi
            obtain ⟨hiT, hline⟩ := Finset.mem_filter.mp hi
            have hiBottom : i ∈ U.cover.indexSet G.M := by
              rw [hregular.some.bottom_index]
              exact hiT
            refine Finset.mem_filter.mpr ⟨hiBottom, ?_⟩
            have hbottom := hregular.some.bottom_tube i hiT
            have hcarrier := congrArg ConvexSpaceBody.carrier hbottom
            simpa only [hsame i hiT, liesInFiveDeltaLineTubeW94, hcarrier,
              Tube.gridScale_self (delta / 2) G.numerics.M_pos] using hline)
      have hvolumeT := hStickyAt ⟨hr, hrSticky⟩ T W U hT hTball hlineT hcardTReal hfullTEps
        hregular.some hfrostman
      have hunionTF : (⋃ i ∈ T, (W i).shade) ⊆ ⋃ i ∈ F, (Z i).shade := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨i, hTF hi, hshade i hi hxi⟩
      have hvolumeOriginal : ((delta / 2 : NNReal) : ENNReal) ^ (gammaZero / 4) <=
          volume (⋃ i ∈ s, (Y i).shade) := by
        calc
          _ <= volume (⋃ i ∈ F, (Z i).shade) := hvolumeT.trans (measure_mono hunionTF)
          _ = (1 / 512 : ENNReal) * volume (⋃ i ∈ band.s2, (Y i).shade) := hunionVolZ
          _ <= volume (⋃ i ∈ band.s2, (Y i).shade) := by
            exact mul_le_of_le_one_left' (by norm_num)
          _ <= _ := measure_mono (Set.iUnion₂_subset fun i hi =>
            Set.subset_iUnion₂ (s := fun i (_ : i ∈ s) => (Y i).shade) i (band.subset hi))
      let advanced : Real := gamma - G.p.c
      let X : ENNReal := (s.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)
      have ha0 : 0 < advanced := by
        dsimp only [advanced]
        linarith [hstep.2.2.1, hgamma.1, hgammaZero.1]
      have ha1 : advanced <= 1 := by dsimp only [advanced]; linarith [hgamma.2]
      have haGamma : gammaZero / 4 <= advanced := by
        dsimp only [advanced]
        linarith [hstep.2.2.1, hgamma.1]
      have hX0 : X ≠ 0 := by
        dsimp only [X]
        exact mul_ne_zero (by exact_mod_cast hs.card_pos.ne') (pow_ne_zero _ hd0)
      have hXTop : X ≠ ⊤ := by dsimp only [X]; finiteness
      have hXbound : X <= Ccard * (delta : ENNReal) ^ (-2 : Real) := by
        calc
          _ <= Ccard * (delta : ENNReal) ^ (-4 : Real) *
              (delta : ENNReal) ^ (2 : Nat) := mul_le_mul_left hcardOriginal _
          _ = _ := by
            rw [mul_assoc, ← ENNReal.rpow_natCast,
              ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            norm_num
      have hXpower : X ^ (advanced / 2) <= Ccard * (delta : ENNReal) ^ (-advanced) := by
        calc
          _ <= (Ccard * (delta : ENNReal) ^ (-2 : Real)) ^ (advanced / 2) :=
            ENNReal.rpow_le_rpow hXbound (by positivity)
          _ = Ccard ^ (advanced / 2) * (delta : ENNReal) ^ (-advanced) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
            congr 2
            ring
          _ <= _ := by
            apply mul_le_mul' _ le_rfl
            have hCcard : (1 : ENNReal) <= Ccard := ENNReal.one_le_coe_iff.mpr cardBound.one_le_C
            simpa only [ENNReal.rpow_one] using
              ENNReal.rpow_le_rpow_of_exponent_le hCcard (show advanced / 2 <= 1 by linarith)
      have hXsplit : X <= Ccard * (delta : ENNReal) ^ (-advanced) * X ^ (1 - advanced / 2) := by
        calc
          X = X ^ (advanced / 2) * X ^ (1 - advanced / 2) := by
            rw [← ENNReal.rpow_add _ _ hX0 hXTop,
              show advanced / 2 + (1 - advanced / 2) = (1 : Real) by ring, ENNReal.rpow_one]
          _ <= _ := mul_le_mul_left hXpower _
      have hscaleInv : (((delta / 2 : NNReal) : ENNReal) ^ (gammaZero / 4))⁻¹ =
          (delta : ENNReal) ^ (-(gammaZero / 4)) * (2 : ENNReal) ^ (gammaZero / 4) := by
        rw [← ENNReal.rpow_neg, ← ENNReal.coe_rpow_of_ne_zero hr.ne', NNReal.div_rpow,
          ENNReal.coe_div (by simp), ENNReal.coe_rpow_of_ne_zero hdpos.ne',
          ENNReal.coe_rpow_of_ne_zero (by norm_num : (2 : NNReal) ≠ 0)]
        norm_num only [ENNReal.coe_ofNat]
        rw [ENNReal.rpow_neg (2 : ENNReal), div_eq_mul_inv, inv_inv]
      have hbound := Kakeya.multiplicity_le_div_of_le_volume_iUnionShade hd1 s Y
        (ENNReal.rpow_pos hrE ENNReal.coe_ne_top) hvolumeOriginal
      change ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
        (delta : ENNReal) ^ (-accuracy / 4 - 2 * advanced) *
          ((s.card : ENNReal) * (delta : ENNReal) ^
            (Module.finrank Real E - 1)) ^ (1 - advanced / 2)
      rw [hdim]
      calc
        _ <= Cvol * X / (((delta / 2 : NNReal) : ENNReal) ^ (gammaZero / 4)) := by
          simpa only [Cvol, X, hdim] using hbound
        _ <= Cvol * (Ccard * (delta : ENNReal) ^ (-advanced) * X ^ (1 - advanced / 2)) /
            (((delta / 2 : NNReal) : ENNReal) ^ (gammaZero / 4)) :=
          ENNReal.div_le_div_right (mul_le_mul_right hXsplit _) _
        _ = Ksticky * (delta : ENNReal) ^ (-(gammaZero / 4)) *
            (delta : ENNReal) ^ (-advanced) * X ^ (1 - advanced / 2) := by
          rw [div_eq_mul_inv, hscaleInv]
          dsimp only [Ksticky]
          ring
        _ <= (delta : ENNReal) ^ (-(accuracy / 4)) * (delta : ENNReal) ^ (-(gammaZero / 4)) *
            (delta : ENNReal) ^ (-advanced) * X ^ (1 - advanced / 2) := by
          exact mul_le_mul' (mul_le_mul' (mul_le_mul' hStickyPay le_rfl) le_rfl) le_rfl
        _ = (delta : ENNReal) ^ (-accuracy / 4 - gammaZero / 4 - advanced) *
            X ^ (1 - advanced / 2) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
            ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 2
          ring
        _ <= _ := mul_le_mul'
          (ENNReal.rpow_le_rpow_of_exponent_ge hd1E (by linarith)) le_rfl
  let terminal : RetainedStateW94 s Y :=
    { active := s
      shading := Y
      active_nonempty := hs
      active_subset := Finset.Subset.rfl
      same_tube := fun _ _ => rfl
      subshade := fun _ _ => Set.Subset.rfl
      retained := 1
      retained_pos := by norm_num
      retained_finite := by norm_num
      mass_retention := by simp }
  refine ⟨{ terminal := terminal, transport_budget := ?_, terminal_estimate := hscalar }⟩
  exact ENNReal.rpow_le_one hd1E (by positivity)

/-- Paid transport to the literal caller s, including its own cardinality. -/
theorem original_run_transport_w110 [Nontrivial E]
    {delta : NNReal} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    {iota : Type uI} (s : Finset iota) (Y : iota -> ShadedTube delta E)
    {gamma step accuracy eta : Real} (haccuracy : 0 < accuracy)
    (hadvanced : gamma - step ∈ Set.Icc (0 : Real) 1)
    (hinput : OriginalInputW110 s Y eta)
    (run : OriginalRunW110 s Y gamma step accuracy) :
    ShadedBody.multiplicity s (fun i => (Y i).toShadedBody) <=
      (delta : ENNReal) ^ (-accuracy - 2 * (gamma - step)) *
        ((s.card : ENNReal) * (delta : ENNReal) ^
          (Module.finrank Real E - 1)) ^ (1 - (gamma - step) / 2) := by
  classical
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hd1 : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta_one
  have hp0 : (delta : ENNReal) ^ (accuracy / 4) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hd0]
  have hpTop : (delta : ENNReal) ^ (accuracy / 4) ≠ ⊤ := by finiteness
  have hmass : (∑ i ∈ s, volume (Y i).shade) <=
      (delta : ENNReal) ^ (-accuracy / 4) *
        (∑ i ∈ run.terminal.active, volume (run.terminal.shading i).shade) := by
    have hret := (mul_le_mul' run.transport_budget
      (le_refl (∑ i ∈ s, volume (Y i).shade))).trans run.terminal.mass_retention
    have hexp : -accuracy / 4 = -(accuracy / 4) := by ring
    rw [hexp, ENNReal.rpow_neg]
    calc
      _ = ((delta : ENNReal) ^ (accuracy / 4))⁻¹ *
          ((delta : ENNReal) ^ (accuracy / 4) *
            (∑ i ∈ s, volume (Y i).shade)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]
      _ <= _ := mul_le_mul_right hret _
  have hunion : (⋃ i ∈ run.terminal.active, (run.terminal.shading i).shade) ⊆
      ⋃ i ∈ s, (Y i).shade := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr
      ⟨i, run.terminal.active_subset hi, run.terminal.subshade i hi hxi⟩
  have hmu := multiplicity_le_mul_of_shade_mass
    (fun i => (Y i).toShadedBody)
    (fun i => (run.terminal.shading i).toShadedBody) hunion hmass
  have hq : 0 <= 1 - (gamma - step) / 2 := by linarith [hadvanced.2]
  have hcard : (run.terminal.active.card : ENNReal) <= (s.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card run.terminal.active_subset
  calc
    _ <= (delta : ENNReal) ^ (-accuracy / 4) *
        ShadedBody.multiplicity run.terminal.active
          (fun i => (run.terminal.shading i).toShadedBody) := hmu
    _ <= (delta : ENNReal) ^ (-accuracy / 4) *
        ((delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - step)) *
          ((run.terminal.active.card : ENNReal) * (delta : ENNReal) ^
            (Module.finrank Real E - 1)) ^ (1 - (gamma - step) / 2)) :=
      mul_le_mul_right run.terminal_estimate _
    _ <= (delta : ENNReal) ^ (-accuracy / 4) *
        ((delta : ENNReal) ^ (-accuracy / 4 - 2 * (gamma - step)) *
          ((s.card : ENNReal) * (delta : ENNReal) ^
            (Module.finrank Real E - 1)) ^ (1 - (gamma - step) / 2)) := by
      gcongr
    _ = (delta : ENNReal) ^ (-accuracy / 2 - 2 * (gamma - step)) *
        ((s.card : ENNReal) * (delta : ENNReal) ^
          (Module.finrank Real E - 1)) ^ (1 - (gamma - step) / 2) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      congr 2
      ring
    _ <= _ := mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hd1
      (by linarith)) le_rfl

/-- The exact public input quantifier is restored: eta is an output after
gamma, hKT, hKF and accuracy, and before delta or any tube family. -/
theorem source_structure_gives_frostman_w110 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (S : StickyWitnessW110.{uE, uI} E gammaZero)
    (G : SourceStructureW110 beta gammaZero S.etaStar)
    {gamma : Real} (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    FrostmanEstimate.{uI} E (gamma - G.p.c) := by
  intro accuracy haccuracy
  obtain ⟨Ctw, Ccell, hCtw, hCcell, A, I, hrun⟩ :=
    exists_certified_original_runs_w110 hdim hbeta hgammaZero S G hgamma hKT hKF haccuracy
  refine ⟨I.inputEta, I.input_pos, ?_⟩
  have hband := band_at_selected_working_exponent_w110 hdim I
  have hstep := source_step_positive_w110 G
  have hadvanced : gamma - G.p.c ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> linarith [hgamma.1, hgamma.2, hgammaZero.1]
  filter_upwards [hrun, hband, self_mem_nhdsWithin,
    eventually_le_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hrun hband hd hd1
  intro iota s Y hball hed hCF hfull
  have hinput : OriginalInputW110 s Y I.inputEta :=
    ⟨hball, hed, hCF, by
      rw [← ENNReal.coe_rpow_of_nonneg _ I.input_pos.le]
      exact ENNReal.coe_le_coe.mpr hfull⟩
  obtain ⟨band⟩ := hband s Y hinput
  obtain ⟨run⟩ := hrun s Y hinput band
  exact original_run_transport_w110 hd hd1 s Y haccuracy hadvanced hinput run

/-- Same statement shape and assumptions as exists_uniform_step_general.
No original protected declaration is redefined by this proposal. -/
theorem exists_uniform_step_general_from_revised_w110
    (hdim : Module.finrank Real E = 3)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{uE, uI} (E := E))
    {beta gammaZero : Real} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1) :
    (frostmanStepSet.{uI} E beta gammaZero).Nonempty := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := Real)
    (by rw [hdim]; norm_num)
  obtain ⟨S⟩ := exists_sticky_witness_w110 hSFE (lt_of_le_of_lt hbeta hgammaZero.1)
  obtain ⟨G⟩ := exists_source_structure_w110 hbeta hgammaZero S.etaStar_pos
  have hstep := source_step_positive_w110 G
  refine ⟨G.p.c, ⟨hstep.1, hstep.2.1⟩, ?_⟩
  intro gamma hgamma hKT hKF
  exact source_structure_gives_frostman_w110 hdim hbeta hgammaZero S G hgamma hKT hKF

set_option maxHeartbeats 2000000 in
-- Specializing the sticky estimate also checks its dimension-three argument.
/-- The existing dimension-three specialization can retain its header. -/
theorem exists_uniform_step_from_revised_w110
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, uI}
      (E := EuclideanSpace Real (Fin 3)))
    {beta gammaZero : Real} (hbeta : 0 <= beta)
    (hgammaZero : gammaZero ∈ Set.Ioc beta 1) :
    (frostmanStepSet.{uI} (EuclideanSpace Real (Fin 3)) beta gammaZero).Nonempty := by
  exact exists_uniform_step_general_from_revised_w110 finrank_euclideanSpace_fin
    hSFE hbeta hgammaZero

/-- The existing envelope theorem is reused after the new uniform step. -/
theorem frostman_step_function_from_revised_w110 {beta : Real}
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, uI}
      (E := EuclideanSpace Real (Fin 3)))
    (hbeta : 0 <= beta) (hbeta_one : beta < 1) :
    ∃ nu : Real -> Real, MonotoneOn nu (Set.Ioc beta 1) ∧
      (∀ gamma ∈ Set.Ioc beta 1, 0 < nu gamma) ∧
      ∀ gamma ∈ Set.Ioc beta 1,
        KatzTaoEstimate.{uI} (EuclideanSpace Real (Fin 3)) beta ->
        FrostmanEstimate.{uI} (EuclideanSpace Real (Fin 3)) gamma ->
        FrostmanEstimate.{uI} (EuclideanSpace Real (Fin 3)) (gamma - nu gamma) := by
  exact exists_monotoneOn_frostmanStep finrank_euclideanSpace_fin
    (fun _ hgammaZero => exists_uniform_step_from_revised_w110 hSFE hbeta hgammaZero)

/-- The exact four-public-boundary Main Lemma 1 statement, under a NEW name.
The other three protected public declarations need no statement change. -/
theorem frostmanEstimate_from_revised_w110 {beta gamma : Real}
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, uI}
      (E := EuclideanSpace Real (Fin 3)))
    (hbeta : 0 <= beta) (hbeta_gamma : beta < gamma) (hgamma : gamma <= 1)
    (hKT : KatzTaoEstimate.{uI} (EuclideanSpace Real (Fin 3)) beta) :
    FrostmanEstimate.{uI} (EuclideanSpace Real (Fin 3)) gamma := by
  have hbeta_one : beta < 1 := lt_of_lt_of_le hbeta_gamma hgamma
  obtain ⟨nu, hmono, hpos, hstep⟩ :=
    frostman_step_function_from_revised_w110 hSFE hbeta hbeta_one
  let exponents : Set Real :=
    {g | FrostmanEstimate.{uI} (EuclideanSpace Real (Fin 3)) g}
  have hclosure : Set.Ioc beta 1 ⊆ exponents := by
    apply ioc_subset_of_sub_mem_of_monotoneOn (s := exponents) (f := nu)
    · intro g g' hle hg
      exact FrostmanEstimate.mono (hE := finrank_euclideanSpace_fin) (hββ' := hle) hg
    · exact frostmanEstimate_one
    · intro g hg hgmem
      exact hstep g hg hKT hgmem
    · exact hmono
    · exact hpos
  exact hclosure ⟨hbeta_gamma, hgamma⟩

end

end Kakeya.ml1Boot.RevisedSourceRepairW110
