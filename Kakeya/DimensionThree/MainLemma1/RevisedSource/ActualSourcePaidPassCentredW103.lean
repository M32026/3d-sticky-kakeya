module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualWorkingTowerW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionArrayW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionRawCutsW97
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentredOuterPreparedDropProofW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceSameMassOuterFullnessW100

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

theorem exists_actual_paid_pass_w95
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero gamma xiMin : Real}
    {xi : Fin (p.N + 1) -> Real} {M : Nat}
    (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    (Cbase Ccan CbaseTw CbaseCell : NNReal)
    (hCbase : 1 <= Cbase) (hCcan : 1 <= Ccan)
    (hCbaseTw : 1 <= CbaseTw) (hCbaseCell : 1 <= CbaseCell) :
    ∃ (Cwork Ctw Ccell BF Cgood Cpass : NNReal) (CM Kmax : Nat)
      (eFull eCF : Real) (delta0 : NNReal),
      1 <= Cwork ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧
      1 <= Cgood ∧ 1 <= Cpass ∧ 1 <= CM ∧ 1 <= Kmax ∧
      0 < eFull ∧ 0 < eCF ∧ 0 < delta0 ∧ delta0 < 1 ∧
      (∃ T : LabelledDetailedTrialThresholdsW94.{uE,uI} (E := E) p xi gamma Ctw Ccell M,
        (∀ m : Fin (p.N + 1), m.val < p.N -> Kmax >= T.Ktr m) ∧
        (∀ m : Fin (p.N + 1), m.val < p.N -> eFull < p.ε * T.inner m / 100) ∧
        (∀ m : Fin (p.N + 1), m.val < p.N -> eCF < p.ε * xi m / 16000)) ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (B : Finset iota) (V : iota -> ShadedTube delta E)
          (base : FixedBaseReserveW94 B V)
          (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan),
          SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
          (∀ i ∈ B, centredTubeW94 (V i).toTube) ->
          lineEssentiallyDistinctW94 B (fun i => (V i).toTube) Cbase ->
          (B.card : Real) <= (delta : Real) ^ (-7 : Real) ->
          ∀ current : RetainedStateW94 B V,
            (delta : ENNReal) ^ eFull <= current.retained * base.lambda0 ->
            (current.retained * base.lambda0)⁻¹ * base.F0 <=
              (delta : ENNReal) ^ (-eCF) ->
            (∃ terminal : RetainedStateW94 B V,
              terminal.active ⊆ current.active ∧
              (∀ i ∈ terminal.active,
                (terminal.shading i).shade ⊆ (current.shading i).shade) ∧
              current.retained / uniformPaidPassCostW95 delta M CM Kmax Cpass <=
                terminal.retained ∧
              actualSourceTerminalW95 terminal.active terminal.shading p gamma xiMin M
                Cwork Ctw Ccell BF Cgood) ∨
            (∃ next : RetainedStateW94 B V,
              Nonempty (SourcePaidDropW95 U0 current next p CM Kmax Cpass
                Cwork Ctw Ccell BF)) := by

  have hcurrentReserve {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (B : Finset iota) (V : iota -> ShadedTube delta E)
      (base : FixedBaseReserveW94 B V) (current : RetainedStateW94 B V) :
      current.retained * base.lambda0 <=
        fullness' current.active (fun i => (current.shading i).toShadedBody) ∧
      frostmanConstIn current.active (fun i => (current.shading i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <= (current.retained * base.lambda0)⁻¹ * base.F0 := by
    obtain ⟨_, hfull, _, hCF⟩ := retained_state_fullness_card_frostman_w94
      B current.active (fun i => (V i).toShadedBody)
      (fun i => (current.shading i).toShadedBody) ConvexSpaceBody.closedUnitBall
      base.carrierVolume base.lambda0 base.F0 current.retained
      base.nonempty current.active_subset base.carrierVolume_pos base.carrierVolume_finite
      base.common_volume base.ball ConvexSpaceBody.closedUnitBall_volume_pos
      ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
      (fun i hi => congrArg Tube.toConvexSpaceBody (current.same_tube i hi))
      current.subshade base.lambda0_pos base.lambda0_finite base.fullness
      base.frostman base.F0_finite current.retained_pos current.retained_finite
      current.mass_retention
    exact ⟨hfull, hCF⟩
  have hcurrentGeometry {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (B : Finset iota) (V : iota -> ShadedTube delta E)
      (base : FixedBaseReserveW94 B V) (current : RetainedStateW94 B V)
      (hcentred : ∀ i ∈ B, centredTubeW94 (V i).toTube)
      (hED : lineEssentiallyDistinctW94 B (fun i => (V i).toTube) Cbase) :
      (∀ i ∈ current.active, (current.shading i).carrier ⊆ Metric.closedBall 0 1) ∧
      (∀ i ∈ current.active, centredTubeW94 (current.shading i).toTube) ∧
      lineEssentiallyDistinctW94 current.active (fun i => (current.shading i).toTube) Cbase := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change (current.shading i).toTube.carrier ⊆ _
      rw [current.same_tube i hi]
      exact base.ball i (current.active_subset hi)
    · intro i hi
      rw [current.same_tube i hi]
      exact hcentred i (current.active_subset hi)
    · intro o v hv
      apply le_trans _ (hED o v hv)
      exact_mod_cast Finset.card_le_card (show
        current.active.filter (fun i => liesInFiveDeltaLineTubeW94 (current.shading i).toTube o v) ⊆
        B.filter (fun i => liesInFiveDeltaLineTubeW94 (V i).toTube o v) from by
          intro i hi
          obtain ⟨hi, hline⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨current.active_subset hi, current.same_tube i hi ▸ hline⟩)
  have hretainedComponent {iota : Type uI} {delta : NNReal}
      (B : Finset iota) (V : iota -> ShadedTube delta E)
      (current : RetainedStateW94 B V) (A : Finset iota)
      (hA : A.Nonempty) (hsubset : A ⊆ current.active)
      (r : ENNReal) (hr : 0 < r) (hrfinite : r < ⊤)
      (hmass : r * (∑ i ∈ current.active, volume (current.shading i).shade) <=
        ∑ i ∈ A, volume (current.shading i).shade) :
      ∃ terminal : RetainedStateW94 B V,
        terminal.active = A ∧ terminal.shading = current.shading ∧
        terminal.retained = r * current.retained := by
    let terminal : RetainedStateW94 B V :=
      { active := A
        shading := current.shading
        active_nonempty := hA
        active_subset := hsubset.trans current.active_subset
        same_tube := fun i hi => current.same_tube i (hsubset hi)
        subshade := fun i hi => current.subshade i (hsubset hi)
        retained := r * current.retained
        retained_pos := ENNReal.mul_pos hr.ne' current.retained_pos.ne'
        retained_finite := ENNReal.mul_lt_top hrfinite current.retained_finite
        mass_retention := by
          rw [mul_assoc]
          exact (mul_le_mul' le_rfl current.mass_retention).trans hmass }
    exact ⟨terminal, rfl, rfl, rfl⟩
  have hregularMono {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Cwork : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Cwork)
      {Ctw Ccell Ctw' Ccell' : NNReal}
      (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (hline : Ctw <= Ctw') (hcell : Ccell <= Ccell') :
      SourceRegularizedWorkingTowerW95 U Ctw' Ccell' :=
    { hregular with
      parent_line_ed := fun k hk o v hv => (hregular.parent_line_ed k hk o v hv).trans hline
      geometric_count := fun k hk R hR =>
        (hregular.geometric_count k hk R hR).trans (mul_le_mul' hcell le_rfl) }
  have hreserveAfterPayment {delta : NNReal} (hdelta : 0 < delta)
      (r lambda F0 : ENNReal) (hr : 0 < r) (hrfinite : r < ⊤)
      (a b c : Real) (hpaid : (delta : ENNReal) ^ b <= r)
      (hfull : (delta : ENNReal) ^ a <= lambda)
      (hCF : lambda⁻¹ * F0 <= (delta : ENNReal) ^ (-c)) :
      (delta : ENNReal) ^ (a + b) <= r * lambda ∧
      (r * lambda)⁻¹ * F0 <= (delta : ENNReal) ^ (-(c + b)) := by
    have hdE : (0 : ENNReal) < delta := ENNReal.coe_pos.mpr hdelta
    refine ⟨?_, ?_⟩
    · rw [ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top, mul_comm]
      exact mul_le_mul' hpaid hfull
    · rw [ENNReal.mul_inv (Or.inl hr.ne') (Or.inl hrfinite.ne), mul_assoc]
      calc
        r⁻¹ * (lambda⁻¹ * F0) <= ((delta : ENNReal) ^ b)⁻¹ * (delta : ENNReal) ^ (-c) :=
          mul_le_mul' (ENNReal.inv_le_inv.mpr hpaid) hCF
        _ = (delta : ENNReal) ^ (-(c + b)) := by
          rw [← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
          congr 1
          ring
  have hprepPayment (Cprep : NNReal) (Kprep : Nat) (e : Real) (he : 0 < e) :
      Filter.Eventually (fun delta : NNReal => (delta : ENNReal) ^ e <=
        towerPreparationRetainedW95 delta Cprep Kprep) (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (half_pos he) Kprep,
      eventually_finite_const_le_rpow_neg (c := (Cprep : ENNReal) * 2 ^ Kprep)
        (by finiteness) (half_pos he),
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin] with delta hpoly hconst hd1 hd0
    have hdpos : 0 < delta := hd0
    have hdR : (0 : Real) < delta := hdpos
    let t : Real := Real.logb 2 (1 / (delta : Real))
    have ht0 : 0 <= t := by
      apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
      exact (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1))
    have hbase : ENNReal.ofReal (2 + t) <= 2 * ENNReal.ofReal (1 + t) := by
      have h : 2 + t <= 2 * (1 + t) := by linarith
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal h
    have hden : (Cprep : ENNReal) * ENNReal.ofReal ((2 + t) ^ Kprep) <=
        (delta : ENNReal) ^ (-e) := by
      rw [ENNReal.ofReal_pow (by linarith : 0 <= 2 + t)]
      calc
        (Cprep : ENNReal) * ENNReal.ofReal (2 + t) ^ Kprep <=
            (Cprep : ENNReal) * (2 * ENNReal.ofReal (1 + t)) ^ Kprep := by gcongr
        _ = ((Cprep : ENNReal) * 2 ^ Kprep) * ENNReal.ofReal (1 + t) ^ Kprep := by rw [mul_pow]; ring
        _ <= (delta : ENNReal) ^ (-(e / 2)) * (delta : ENNReal) ^ (-(e / 2)) := mul_le_mul' hconst hpoly
        _ = (delta : ENNReal) ^ (-e) := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hdpos).ne' ENNReal.coe_ne_top]
          congr 1
          ring
    change (delta : ENNReal) ^ e <= ((Cprep : ENNReal) * ENNReal.ofReal ((2 + t) ^ Kprep))⁻¹
    calc
      (delta : ENNReal) ^ e = ((delta : ENNReal) ^ (-e))⁻¹ := by rw [ENNReal.rpow_neg, inv_inv]
      _ <= _ := ENNReal.inv_le_inv.mpr hden
  have hdenominatorMono {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {CM CM' : Nat} (hCM : CM <= CM') :
      fullPassDenominatorW87 delta M CM <= fullPassDenominatorW87 delta M CM' := by
    have hlog : 0 <= Real.log (1 / (delta : Real)) :=
      Real.log_nonneg ((one_le_div (show (0 : Real) < delta from hdelta)).mpr hdelta1)
    have hbase : 1 <= 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by
      have h := div_nonneg hlog (Real.log_nonneg (by norm_num : (1 : Real) <= 2))
      linarith
    have hceil : (Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM) : ENNReal) <=
        Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM') := by
      exact_mod_cast Nat.ceil_mono (pow_le_pow_right₀ hbase hCM)
    unfold fullPassDenominatorW87 sourceLambdaMNatW87 sourceLambdaINatW87 sourceLambdaBalNatW87
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hceil) hceil) hceil
  have hstepCostMono {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      {B : Finset iota} {V : iota -> ShadedTube delta E}
      (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
      {current next : RetainedStateW94 B V} {CM CM' : Nat} {Cpass Cpass' : NNReal}
      (step : PaidDropTransitionW94 U0 current next CM Cpass (sourceFlatDropW95 p))
      (hdelta : 0 < delta) (hdelta1 : delta <= 1) (hCM : CM <= CM') (hCpass : Cpass <= Cpass') :
      ∃ step' : PaidDropTransitionW94 U0 current next CM' Cpass' (sourceFlatDropW95 p),
        step'.trialScale = step.trialScale ∧ step'.Ktr = step.Ktr ∧
        step'.daggerFamily = step.daggerFamily ∧ step'.Ydagger = step.Ydagger ∧
        step'.drop_q = step.drop_q ∧ step'.drop_ell = step.drop_ell := by
    have hden : (Cpass : ENNReal) * fullPassDenominatorW87 delta M CM <=
        (Cpass' : ENNReal) * fullPassDenominatorW87 delta M CM' :=
      mul_le_mul' (ENNReal.coe_le_coe.mpr hCpass) (hdenominatorMono hdelta hdelta1 hCM)
    let step' : PaidDropTransitionW94 U0 current next CM' Cpass' (sourceFlatDropW95 p) :=
      { step with
        selector_retention :=
          (mul_le_mul' (ENNReal.inv_le_inv.mpr hden) le_rfl).trans step.selector_retention
        coefficient_paid := by
          apply le_trans _ step.coefficient_paid
          apply ENNReal.div_le_div le_rfl
          exact ENNReal.div_le_div_right hden _ }
    exact ⟨step', rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpreparationCovered {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      (Cprep Cpass : NNReal) (Kprep CM Ktr : Nat)
      (hC : Cprep <= Cpass) (hK : Kprep <= CM) :
      (towerPreparationRetainedW95 delta Cprep Kprep)⁻¹ <=
        uniformPaidPassCostW95 delta M CM Ktr Cpass := by
    have hdR : (0 : Real) < delta := hdelta
    have hlog : 0 <= Real.log (1 / (delta : Real)) :=
      Real.log_nonneg ((one_le_div hdR).mpr hdelta1)
    let t : Real := 2 + Real.log (1 / (delta : Real)) / Real.log 2
    have ht : 1 <= t := by
      have h := div_nonneg hlog (Real.log_nonneg (by norm_num : (1 : Real) <= 2))
      dsimp [t]
      linarith
    let L : ENNReal := Nat.ceil (t ^ CM)
    have hL : 1 <= L := by
      have h : (1 : Real) <= Nat.ceil (t ^ CM) := (one_le_pow₀ ht).trans (Nat.le_ceil _)
      change (1 : ENNReal) <= Nat.ceil (t ^ CM)
      exact_mod_cast h
    have hpoly : ENNReal.ofReal (t ^ Kprep) <= L := by
      have h := ENNReal.ofReal_le_ofReal ((pow_le_pow_right₀ ht hK).trans (Nat.le_ceil _))
      simpa only [ENNReal.ofReal_natCast] using h
    have hfactor : (1 : ENNReal) <= 4 * ((M + 1 : Nat) : ENNReal) :=
      one_le_mul (by norm_num) (by exact_mod_cast Nat.le_add_left 1 M)
    have hden : L <= fullPassDenominatorW87 delta M CM := by
      calc
        L <= L * (4 * ((M + 1 : Nat) : ENNReal) * L * L) :=
          le_mul_of_one_le_right zero_le (one_le_mul (one_le_mul hfactor hL) hL)
        _ = _ := by
          dsimp [L, t, fullPassDenominatorW87, sourceLambdaMNatW87,
            sourceLambdaINatW87, sourceLambdaBalNatW87]
          ring
    have htrialle : trialRetainedFractionW94 delta Ktr <= 1 :=
      ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg Ktr)))
    unfold towerPreparationRetainedW95
    rw [inv_inv]
    calc
      (Cprep : ENNReal) * ENNReal.ofReal (t ^ Kprep) <=
          (Cpass : ENNReal) * fullPassDenominatorW87 delta M CM :=
        mul_le_mul' (ENNReal.coe_le_coe.mpr hC) (hpoly.trans hden)
      _ <= uniformPaidPassCostW95 delta M CM Ktr Cpass := by
        unfold uniformPaidPassCostW95 actualPaidPassCostW94
        rw [div_eq_mul_inv]
        exact le_mul_of_one_le_right zero_le (ENNReal.one_le_inv.mpr htrialle)
  have hpreparationPositiveFinite {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      (Cprep : NNReal) (hCprep : 1 <= Cprep) (Kprep : Nat) :
      0 < towerPreparationRetainedW95 delta Cprep Kprep ∧
        towerPreparationRetainedW95 delta Cprep Kprep < ⊤ := by
    have hlog : 0 <= Real.log (1 / (delta : Real)) :=
      Real.log_nonneg ((one_le_div (show (0 : Real) < delta from hdelta)).mpr hdelta1)
    have hbase : 0 < 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by
      have h := div_nonneg hlog (Real.log_nonneg (by norm_num : (1 : Real) <= 2))
      linarith
    have hC : (0 : ENNReal) < Cprep := by exact_mod_cast zero_lt_one.trans_le hCprep
    have hpow : 0 < ENNReal.ofReal ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ Kprep) :=
      ENNReal.ofReal_pos.mpr (pow_pos hbase _)
    unfold towerPreparationRetainedW95
    exact ⟨ENNReal.inv_pos.mpr (by finiteness), ENNReal.inv_lt_top.mpr (ENNReal.mul_pos hC.ne' hpow.ne')⟩
  have hterminalFromPrepared {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (B : Finset iota) (V : iota -> ShadedTube delta E)
      (current : RetainedStateW94 B V) (A : Finset iota)
      (hA : A.Nonempty) (hsubset : A ⊆ current.active)
      (Cprep Cpass Cwork Ctw Ccell BF Cgood : NNReal) (Kprep CM Kmax : Nat)
      (hCprep : 1 <= Cprep) (hC : Cprep <= Cpass) (hK : Kprep <= CM)
      (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      (hmass : towerPreparationRetainedW95 delta Cprep Kprep *
        (∑ i ∈ current.active, volume (current.shading i).shade) <=
          ∑ i ∈ A, volume (current.shading i).shade)
      (hterminal : actualSourceTerminalW95 A current.shading p gamma xiMin M Cwork Ctw Ccell BF Cgood) :
      ∃ terminal : RetainedStateW94 B V,
        terminal.active ⊆ current.active ∧
        (∀ i ∈ terminal.active, (terminal.shading i).shade ⊆ (current.shading i).shade) ∧
        current.retained / uniformPaidPassCostW95 delta M CM Kmax Cpass <= terminal.retained ∧
        actualSourceTerminalW95 terminal.active terminal.shading p gamma xiMin M Cwork Ctw Ccell BF Cgood := by
    obtain ⟨hpositive, hfinite⟩ := hpreparationPositiveFinite hdelta hdelta1 Cprep hCprep Kprep
    obtain ⟨terminal, hactive, hshading, hretained⟩ := hretainedComponent B V current A hA hsubset
      (towerPreparationRetainedW95 delta Cprep Kprep) hpositive hfinite hmass
    refine ⟨terminal, hactive ▸ hsubset, ?_, ?_, ?_⟩
    · intro i hi
      rw [hshading]
    · rw [hretained, div_eq_mul_inv, mul_comm current.retained]
      apply mul_le_mul' _ le_rfl
      have h := ENNReal.inv_le_inv.mpr (hpreparationCovered hdelta hdelta1 Cprep Cpass Kprep CM Kmax hC hK)
      simpa only [inv_inv] using h
    · rwa [hactive, hshading]
  have hpreparedReserve {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (B : Finset iota) (V : iota -> ShadedTube delta E)
      (base : FixedBaseReserveW94 B V) (current : RetainedStateW94 B V)
      (A : Finset iota) (hA : A.Nonempty) (hsubset : A ⊆ current.active)
      (r : ENNReal) (hr : 0 < r) (hrfinite : r < ⊤)
      (hmass : r * (∑ i ∈ current.active, volume (current.shading i).shade) <=
        ∑ i ∈ A, volume (current.shading i).shade)
      (e : Real) (hdelta : 0 < delta) (hpaid : (delta : ENNReal) ^ e <= r)
      (hfull : (delta : ENNReal) ^ e <= current.retained * base.lambda0)
      (hCF : (current.retained * base.lambda0)⁻¹ * base.F0 <=
        (delta : ENNReal) ^ (-e)) :
      (delta : ENNReal) ^ (2 * e) <= fullness' A (fun i => (current.shading i).toShadedBody) ∧
      frostmanConstIn A (fun i => (current.shading i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-(2 * e)) := by
    obtain ⟨prepared, hactive, hshading, hretained⟩ :=
      hretainedComponent B V current A hA hsubset r hr hrfinite hmass
    obtain ⟨hfullPrepared, hCFPrepared⟩ := hcurrentReserve B V base prepared
    obtain ⟨hfullPaid, hCFPaid⟩ := hreserveAfterPayment hdelta r
      (current.retained * base.lambda0) base.F0 hr hrfinite e e e hpaid hfull hCF
    rw [hretained, mul_assoc, hactive, hshading] at hfullPrepared hCFPrepared
    constructor
    · simpa only [← two_mul] using hfullPaid.trans hfullPrepared
    · simpa only [← two_mul] using hCFPrepared.trans hCFPaid
  have hmiddleReserve {delta : NNReal} (hdelta : 0 < delta)
      (e : Real) (loss full : ENNReal)
      (hpaid : (delta : ENNReal) ^ e <= loss⁻¹)
      (hfull : (delta : ENNReal) ^ (2 * e) <= full) :
      (delta : ENNReal) ^ (10 * e) <= (loss ^ (6 : Nat))⁻¹ * full ^ (2 : Nat) := by
    calc
      (delta : ENNReal) ^ (10 * e) =
          ((delta : ENNReal) ^ e) ^ (6 : Nat) *
            ((delta : ENNReal) ^ (2 * e)) ^ (2 : Nat) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hdelta).ne' ENNReal.coe_ne_top]
        congr 1
        norm_num
        ring
      _ <= (loss⁻¹) ^ (6 : Nat) * full ^ (2 : Nat) :=
        mul_le_mul' (pow_le_pow_left' hpaid _) (pow_le_pow_left' hfull _)
      _ = _ := by rw [ENNReal.inv_pow]
  obtain ⟨Cwork, Ctw, Ccell, BF, Cprep, Kprep, ePrep, deltaPrep,
    hCwork, hCtw, hCcell, hBF, hCprep, hKprep, hePrep, hePrepSmall,
    hdeltaPrep, hdeltaPrep1, hprepare⟩ :=
    exists_prepared_extended_regularized_stopping_w98 hdim hp normalizationParameterMarginW98
      (by norm_num [normalizationParameterMarginW98])
      (by
        change ((2 : NNReal)⁻¹) ^ (20 : Nat) <= 1 / 100
        exact_mod_cast (by norm_num : ((2 : Real)⁻¹) ^ (20 : Nat) <= 1 / 100)) Cbase hCbase
  obtain ⟨Cselect, Kselect, deltaSelect, hCselect, hKselect, hdeltaSelect,
    hdeltaSelect1, hselect⟩ :=
    exists_actual_same_mass_selections_with_certificate_w99 hdim M hp.M_pos
      Cwork Ctw Ccell hCwork hCtw hCcell ePrep hePrep
  obtain ⟨Rnorm, Cext, Cnorm, CtwNorm, CcellNorm, Ctransport, Cgood, Cpass,
    full, aux, CM, Kout, eFullD, eCFD, deltaD,
    hRnorm, hCext, hCnorm, hCtwNorm, hCcellNorm, htwNorm, hcellNorm,
    hCtransport, hCgood, hCpass, hCM, hKout, heFullD, heCFD,
    hdeltaD, hdeltaD1, hschedule, hdividing⟩ :=
    exists_centred_actual_outer_prepared_dividing_canonical_pass_w101 hdim hp gamma hgamma.1 hgamma.2
      Ccan CbaseTw CbaseCell Cwork Ctw Ccell BF Cprep Cselect
      hCcan hCbaseTw hCbaseCell hCwork hCtw hCcell hBF hCprep hCselect
      Kprep Kselect hKprep hKselect hKT hKF
  let e : Real := min ePrep (min eFullD eCFD) / 16
  have he : 0 < e := div_pos (lt_min hePrep (lt_min heFullD heCFD)) (by norm_num)
  have hePrepBound : 2 * e <= ePrep := by
    have h := min_le_left ePrep (min eFullD eCFD)
    dsimp [e]
    linarith [lt_min hePrep (lt_min heFullD heCFD)]
  have heFullBound : 10 * e <= eFullD := by
    have h := (min_le_right ePrep (min eFullD eCFD)).trans (min_le_left eFullD eCFD)
    dsimp [e]
    linarith [lt_min hePrep (lt_min heFullD heCFD)]
  have heCFBound : 2 * e <= eCFD := by
    have h := (min_le_right ePrep (min eFullD eCFD)).trans (min_le_right eFullD eCFD)
    dsimp [e]
    linarith [lt_min hePrep (lt_min heFullD heCFD)]
  let CMout := max CM Kprep
  let CpassOut := max Cpass Cprep
  have hsmall : Filter.Eventually (fun delta : NNReal =>
      delta < deltaPrep ∧ delta < deltaSelect ∧ delta < deltaD ∧ delta < 1 ∧
      (delta : ENNReal) ^ e <= towerPreparationRetainedW95 delta Cprep Kprep ∧
      (delta : ENNReal) ^ e <= towerPreparationRetainedW95 delta Cselect Kselect)
      (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hdeltaPrep),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hdeltaSelect),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds hdeltaD),
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : NNReal) < 1 by norm_num)),
      hprepPayment Cprep Kprep e he, hprepPayment Cselect Kselect e he]
      with delta h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨deltaCut, hdeltaCut, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  let delta0 : NNReal := min deltaCut (1 / 2)
  have hdelta0 : 0 < delta0 := lt_min hdeltaCut (by norm_num)
  have hdelta01 : delta0 < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨Cwork, CtwNorm, CcellNorm, BF, Cgood, CpassOut, CMout, Kout, e, e, delta0,
    hCwork, hCtwNorm, hCcellNorm, hBF, hCgood, hCpass.trans (le_max_left _ _),
    hCM.trans (le_max_left _ _), hKout, he, he, hdelta0, hdelta01, ?_, ?_⟩
  · refine ⟨full, ?_, ?_, ?_⟩
    · intro m hm
      exact (hschedule m hm).2.2.1
    · intro m hm
      apply lt_of_le_of_lt (show e <= eFullD by linarith) ((hschedule m hm).1.trans_le ?_)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hp.epsilon_pos.le) (by norm_num)
    · intro m hm
      exact (show e <= eCFD by linarith).trans_lt (hschedule m hm).2.1
  intro delta hdelta hdeltaSmall iota inst B V base U0 hbaseRegular hcentred hED hcard current hfull hCF
  obtain ⟨hdPrep, hdSelect, hdD, hd1, hprepPaid, hselectPaid⟩ :=
    hcut ⟨hdelta, hdeltaSmall.trans_le (min_le_left _ _)⟩
  have hdE1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd1.le
  have hpower (a b : Real) (hab : a <= b) : (delta : ENNReal) ^ b <= (delta : ENNReal) ^ a :=
    ENNReal.rpow_le_rpow_of_exponent_ge hdE1 hab
  obtain ⟨hcurrentFull, hcurrentCF⟩ := hcurrentReserve B V base current
  obtain ⟨hcurrentBall, hcurrentCentred, hcurrentED⟩ :=
    hcurrentGeometry B V base current hcentred hED
  obtain ⟨A, U, Uext, hA, hsubset, hmass, ⟨hregular⟩, ⟨hregularExt⟩,
    hrestriction, hmargin, hstop⟩ :=
    hprepare hdelta hdPrep current.active current.shading current.active_nonempty
      hcurrentBall hcurrentCentred hcurrentED
      ((hpower e ePrep (by linarith)).trans (hfull.trans hcurrentFull))
      (hcurrentCF.trans (hCF.trans (hpower (-ePrep) (-e) (by linarith))))
  have hball : ∀ i ∈ A, (current.shading i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => hcurrentBall i (hsubset hi)
  have hregularNorm : SourceRegularizedWorkingTowerW95 U CtwNorm CcellNorm :=
    hregularMono U hregular htwNorm hcellNorm
  rcases hstop with hevery | ⟨block⟩
  · exact Or.inl (hterminalFromPrepared B V current A hA hsubset Cprep CpassOut Cwork
      CtwNorm CcellNorm BF Cgood Kprep CMout Kout hCprep (le_max_right _ _)
      (le_max_right _ _) hdelta hd1.le hmass (Or.inr ⟨U, ⟨hregularNorm⟩, hevery⟩))
  obtain ⟨block⟩ := block
  obtain ⟨hprepPositive, hprepFinite⟩ := hpreparationPositiveFinite hdelta hd1.le Cprep hCprep Kprep
  obtain ⟨hfullA, hCFA⟩ := hpreparedReserve B V base current A hA hsubset
    (towerPreparationRetainedW95 delta Cprep Kprep) hprepPositive hprepFinite
    hmass e hdelta hprepPaid hfull hCF
  obtain ⟨certificate, _⟩ := hselect hdelta hdSelect A current.shading U hA hregular hball
    ((hpower (2 * e) ePrep hePrepBound).trans hfullA) block
  let selections := certificate.selections
  have hmiddle := certificate.middle_fullness
  let loss : NNReal := Cselect * Real.toNNReal
    ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ Kselect)
  have hloss : (loss : ENNReal) = (towerPreparationRetainedW95 delta Cselect Kselect)⁻¹ := by
    simp only [loss, towerPreparationRetainedW95, inv_inv, ENNReal.coe_mul,
      ENNReal.ofReal]
  have hmiddleFunded : (delta : ENNReal) ^ eFullD <=
      fullness' (U.cover.indexSet block.b.val)
        (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) := by
    have hlossPaid : (delta : ENNReal) ^ e <= (loss : ENNReal)⁻¹ := by
      simpa only [hloss, inv_inv] using hselectPaid
    exact (hpower (10 * e) eFullD heFullBound).trans
      ((hmiddleReserve hdelta e loss _ hlossPaid hfullA).trans hmiddle)
  obtain ⟨calls, houtcome⟩ := hdividing hdelta hdD B V base U0 hbaseRegular hcentred hcard current A U Uext
    hA hsubset hrestriction hregular hregularExt hmargin hmass
    ((hpower (2 * e) eFullD (by linarith)).trans hfullA)
    (hCFA.trans (hpower (-eCFD) (-(2 * e)) (by linarith)))
    block loss selections hloss.le hmiddleFunded certificate.coarse_fullness
  rcases houtcome with hgood | hdrop
  · exact Or.inl (hterminalFromPrepared B V current A hA hsubset Cprep CpassOut Cwork
      CtwNorm CcellNorm BF Cgood Kprep CMout Kout hCprep (le_max_right _ _)
      (le_max_right _ _) hdelta hd1.le hmass (Or.inl hgood))
  obtain ⟨drops, working, trialLevel, ellPred, nodeFamily, middlePlus, Fdagger,
    nodeTube, part, W, raw, Zplus, Ydagger, c, hraw⟩ := hdrop
  obtain ⟨_, _, _, _, _, _, _, hFdagger, hFsubset, hYdagger,
    _, _, _, _, _, _, _, _, _, _, _, _, hnext⟩ := hraw
  obtain ⟨next, step, htrialScale, hKtr, hdagger, hY, hq, hell, hpaid⟩ := hnext
  obtain ⟨step', htrialScale', hKtr', hdagger', hY', hq', hell'⟩ :=
    hstepCostMono U0 step hdelta hd1.le (le_max_left _ _) (le_max_left _ _)
  have hcost : uniformPaidPassCostW95 delta M CM Kout Cpass <=
      uniformPaidPassCostW95 delta M CMout Kout CpassOut := by
    unfold uniformPaidPassCostW95 actualPaidPassCostW94
    exact ENNReal.div_le_div
      (mul_le_mul' (ENNReal.coe_le_coe.mpr (le_max_left _ _))
        (hdenominatorMono hdelta hd1.le (le_max_left _ _))) le_rfl
  let source : SourcePaidDropW95 U0 current next p CMout Kout CpassOut
      Cwork CtwNorm CcellNorm BF :=
    { step := step'
      trial_exponent_bound := by rw [hKtr', hKtr]
      workingFamily := A
      working_subset := hsubset
      working_nonempty := hA
      workingNet := U
      regular := hregularNorm
      block := block
      selectionLoss := loss
      selections := selections
      trial_scale_eq := htrialScale'.trans htrialScale
      dagger_same_component := by
        rw [hdagger', hdagger]
        exact hFsubset.trans (selections.fine_subset.trans selections.first.child_subset)
      dagger_from_cut := by rwa [hdagger', hdagger]
      dagger_cut_subshade := by
        intro i hi
        rw [hdagger', hdagger] at hi
        rw [hY', hY]
        exact (hYdagger i hi).2
      uniform_paid := (ENNReal.div_le_div le_rfl hcost).trans hpaid }
  exact Or.inr ⟨next, ⟨source⟩⟩


end

end Kakeya.ml1Boot.TrialRestartW94
