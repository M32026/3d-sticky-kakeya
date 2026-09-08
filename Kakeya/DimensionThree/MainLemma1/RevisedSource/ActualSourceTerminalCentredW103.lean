module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualWorkingTowerW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionArrayW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionRawCutsW97
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceSameMassFullnessW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualSourcePaidPassCentredW103

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
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87







/-- P2 constructs both the final regularized component and its stopping
alternative from raw current mass/fullness/CF data. -/
theorem exists_actual_regularized_stopping_w95
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (Cbase : NNReal) (hCbase : 1 <= Cbase) :
    ∃ (Ccan Ctw Ccell BF Cprep : NNReal) (Kprep : Nat)
      (ePrep : Real) (delta0 : NNReal),
      1 <= Ccan ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧ 1 <= Cprep ∧
      1 <= Kprep ∧ 0 < ePrep ∧ ePrep < p.η 0 / 100 ∧
      0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (F : Finset iota) (Y : iota -> ShadedTube delta E),
          F.Nonempty ->
          (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
          lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase ->
          (delta : ENNReal) ^ ePrep <= fullness' F (fun i => (Y i).toShadedBody) ->
          frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-ePrep) ->
          ∃ (A : Finset iota)
            (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
            A.Nonempty ∧ A ⊆ F ∧
            towerPreparationRetainedW95 delta Cprep Kprep *
              (∑ i ∈ F, volume (Y i).shade) <= ∑ i ∈ A, volume (Y i).shade ∧
            Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
            (actualEveryScaleW95 U p.ε p.N BF ∨
              Nonempty (ActualSourceDividingBlockW95 U p BF)) := by
  obtain ⟨Ccan, Ctw, Ccell, BF, Cprep, Kprep, ePrep, delta0,
    hCcan, hCtw, hCcell, hBF, hCprep, hKprep, hePrep, hePrepSmall,
    hdelta0, hdelta1, hextended⟩ :=
    exists_extended_regularized_stopping_w97 hdim hp Cbase hCbase
  refine ⟨Ccan, Ctw, Ccell, BF, Cprep, Kprep, ePrep, delta0,
    hCcan, hCtw, hCcell, hBF, hCprep, hKprep, hePrep, hePrepSmall,
    hdelta0, hdelta1, ?_⟩
  intro delta hdelta hsmall iota inst F Y hF hball hcentred hED hfull hCF
  obtain ⟨A, U, Uext, hA, hAF, hmass, hregular, hregularExt,
    hindex, hassign, hscale, htube, hstop⟩ :=
    hextended hdelta hsmall F Y hF hball hcentred hED hfull hCF
  exact ⟨A, U, hA, hAF, hmass, hregular, hstop⟩








/-- Exact comparison retaining the factor eight from three ceilings and
the separate prior trial loss. -/
theorem uniform_paid_pass_cost_le_eight_w95
    (delta : NNReal) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (M CM Ktr : Nat) (Cpass : NNReal) :
    uniformPaidPassCostW95 delta M CM Ktr Cpass <=
      8 * (Cpass : ENNReal) * 4 * ((M + 1 : Nat) : ENNReal) *
        ENNReal.ofReal ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (3 * CM)) /
          trialRetainedFractionW94 delta Ktr := by
  let L : Real := 2 + Real.log (1 / (delta : Real)) / Real.log 2
  have hd0 : 0 < (delta : Real) := hdelta
  have hd1 : (delta : Real) <= 1 := hdelta1.le
  have hlog0 : 0 <= Real.log (1 / (delta : Real)) / Real.log 2 := by
    apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
    exact (le_div_iff₀ hd0).mpr (by simpa only [one_mul] using hd1)
  have hL1 : 1 <= L := by dsimp [L]; linarith
  have hp1 : 1 <= L ^ CM := one_le_pow₀ hL1
  have hceilR : (Nat.ceil (L ^ CM) : Real) <= 2 * L ^ CM := by
    have h := Nat.ceil_lt_add_one (zero_le_one.trans hp1)
    linarith
  have hceil : (Nat.ceil (L ^ CM) : ENNReal) <= 2 * ENNReal.ofReal (L ^ CM) := by
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2),
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hceilR
  have hpow : ENNReal.ofReal (L ^ (3 * CM)) = (ENNReal.ofReal (L ^ CM)) ^ (3 : Nat) := by
    rw [← ENNReal.ofReal_pow (zero_le_one.trans hp1)]
    congr 1
    rw [← pow_mul, Nat.mul_comm CM 3]
  unfold uniformPaidPassCostW95 actualPaidPassCostW94
  apply ENNReal.div_le_div_right
  change (Cpass : ENNReal) * (4 * ((M + 1 : Nat) : ENNReal) *
    (Nat.ceil (L ^ CM) : ENNReal) * (Nat.ceil (L ^ CM) : ENNReal) *
    (Nat.ceil (L ^ CM) : ENNReal)) <=
      8 * (Cpass : ENNReal) * 4 * ((M + 1 : Nat) : ENNReal) * ENNReal.ofReal (L ^ (3 * CM))
  calc
    (Cpass : ENNReal) * (4 * ((M + 1 : Nat) : ENNReal) *
        (Nat.ceil (L ^ CM) : ENNReal) * (Nat.ceil (L ^ CM) : ENNReal) *
        (Nat.ceil (L ^ CM) : ENNReal)) <=
        (Cpass : ENNReal) * (4 * ((M + 1 : Nat) : ENNReal) *
          (2 * ENNReal.ofReal (L ^ CM)) * (2 * ENNReal.ofReal (L ^ CM)) *
          (2 * ENNReal.ofReal (L ^ CM))) := by gcongr
    _ = _ := by rw [hpow]; ring

/-- Arithmetic on a supplied trace only; this is not terminal existence.
Every coordinate in the budget is evaluated against the original U0. -/
theorem actual_drop_trace_budget_w95
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E}
    {M CM : Nat} {Ccan Cpass : NNReal} {cFlat : Real}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (initial : RetainedStateW94 B V)
    (trace : ActualDropTraceW94 U0 initial CM Cpass cFlat)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hcFlat : 0 < cFlat)
    (hcard7 : (B.card : Real) <= (delta : Real) ^ (-7 : Real)) :
    (trace.length : Real) * cFlat <= 7 * ((M + 1 : Nat) : Real) ^ 2 ∧
      trace.length <= Nat.ceil (7 * ((M + 1 : Nat) : Real) ^ 2 / cFlat) := by
  let Coord := Fin (M + 1) × Fin (M + 1)
  let Phi : Fin (trace.length + 1) -> Real := fun n =>
    ∑ q : Coord, persistentProfileW94 U0 (trace.state n) q.1 q.2
  have hPhi0 : ∀ n, 0 <= Phi n := by
    intro n
    apply Finset.sum_nonneg
    intro q hq
    exact literalProfileCoord_nonneg_w87 U0 hdelta hdelta1 q.1 q.2
  have hPhi7 : ∀ n, Phi n <= 7 * ((M + 1 : Nat) : Real) ^ 2 := by
    intro n
    calc
      Phi n <= ∑ q : Coord, (7 : Real) := by
        apply Finset.sum_le_sum
        intro q hq
        exact literalProfileCoord_le_seven_w87 U0 hdelta hdelta1
          (trace.state n).active_subset hcard7 q.1 q.2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Coord, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]; ring
  have hstep : ∀ n : Fin trace.length,
      Phi (Fin.succ n) + cFlat <= Phi (Fin.castSucc n) := by
    intro n
    let step := trace.step n
    let q0 : Coord := (step.drop_q, step.drop_ell)
    have hsub : (trace.state (Fin.succ n)).active ⊆ (trace.state (Fin.castSucc n)).active :=
      step.next_subset.trans step.dagger_subset
    have hmono : ∀ q : Coord,
        persistentProfileW94 U0 (trace.state (Fin.succ n)) q.1 q.2 <=
          persistentProfileW94 U0 (trace.state (Fin.castSucc n)) q.1 q.2 := by
      intro q
      exact literalProfileCoord_mono_w87 U0 hdelta hdelta1 hsub q.1 q.2
    have hrest := Finset.sum_le_sum (s := Finset.univ.erase q0)
      (fun q hq => hmono q)
    have hnext := Finset.sum_erase_add (s := Finset.univ)
      (fun q : Coord => persistentProfileW94 U0 (trace.state (Fin.succ n)) q.1 q.2)
      (Finset.mem_univ q0)
    have hcurrent := Finset.sum_erase_add (s := Finset.univ)
      (fun q : Coord => persistentProfileW94 U0 (trace.state (Fin.castSucc n)) q.1 q.2)
      (Finset.mem_univ q0)
    have hdrop : persistentProfileW94 U0 (trace.state (Fin.succ n)) q0.1 q0.2 + cFlat <=
        persistentProfileW94 U0 (trace.state (Fin.castSucc n)) q0.1 q0.2 := step.profile_drop
    dsimp only [Phi]
    linarith
  have htel : ∀ n (hn : n <= trace.length),
      Phi ⟨n, by omega⟩ + (n : Real) * cFlat <= Phi 0 := by
    intro n
    induction n with
    | zero => intro hn; simpa using (le_refl (Phi 0))
    | succ n ih =>
      intro hn
      have hp := ih (by omega)
      have hs := hstep ⟨n, by omega⟩
      change Phi ⟨n + 1, by omega⟩ + cFlat <= Phi ⟨n, by omega⟩ at hs
      push_cast
      nlinarith
  have hbudget : (trace.length : Real) * cFlat <= 7 * ((M + 1 : Nat) : Real) ^ 2 := by
    have h := htel trace.length le_rfl
    have h0 := hPhi0 ⟨trace.length, by omega⟩
    have h7 := hPhi7 0
    linarith
  refine ⟨hbudget, ?_⟩
  have hdiv : (trace.length : Real) <= 7 * ((M + 1 : Nat) : Real) ^ 2 / cFlat :=
    (le_div_iff₀ hcFlat).mpr hbudget
  exact_mod_cast hdiv.trans (Nat.le_ceil _)

/-- P6 constructs a terminal run directly from a raw source family.
The fixed original net is itself an output of initial paid preparation.
All intermediate reserve and mass claims refer to that same base and net.
The final preparation pass is charged once beyond the number of drops. -/
theorem exists_actual_source_terminal_run_w95
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero gamma xiMin : Real}
    {xi : Fin (p.N + 1) -> Real} {M : Nat}
    (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    (Csource : NNReal) (hCsource : 1 <= Csource)
    (bLoss : Real) (hbLoss : 0 < bLoss) :
    ∃ (Ccan CbaseTw CbaseCell Cwork Ctw Ccell BF Cgood Cpass : NNReal)
      (CM Kmax : Nat) (eInput eFull eCF aInitial bInitial fInitial bReserve : Real)
      (delta0 : NNReal),
      1 <= Ccan ∧ 1 <= CbaseTw ∧ 1 <= CbaseCell ∧ 1 <= Cwork ∧
      1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧ 1 <= Cgood ∧ 1 <= Cpass ∧
      1 <= CM ∧ 1 <= Kmax ∧ 0 < eInput ∧ eInput < p.η 0 / 1000 ∧
      0 < eFull ∧ 0 < eCF ∧ 0 < aInitial ∧ 0 < bInitial ∧
      0 < fInitial ∧ 0 < bReserve ∧ bInitial + bReserve < bLoss ∧
      aInitial + bReserve < eFull ∧ aInitial + bReserve + fInitial < eCF ∧
      0 < delta0 ∧ delta0 < 1 ∧
      (∃ T : LabelledDetailedTrialThresholdsW94.{uE,uI} (E := E) p xi gamma Ctw Ccell M,
        (∀ m : Fin (p.N + 1), m.val < p.N -> T.Ktr m <= Kmax) ∧
        (∀ m : Fin (p.N + 1), m.val < p.N -> eFull < p.ε * T.inner m / 100) ∧
        (∀ m : Fin (p.N + 1), m.val < p.N -> eCF < p.ε * xi m / 16000)) ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
        (uniformPaidPassCostW95 delta M CM Kmax Cpass) ^
          (sourceRestartFuelW95 p M + 1) <= (delta : ENNReal) ^ (-bReserve) ∧
        ∀ {iota : Type uI} [DecidableEq iota]
          (F : Finset iota) (Y : iota -> ShadedTube delta E),
          F.Nonempty ->
          (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
          lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Csource ->
          (delta : ENNReal) ^ eInput <= fullness' F (fun i => (Y i).toShadedBody) ->
          frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-eInput) ->
          ∃ (B : Finset iota) (base : FixedBaseReserveW94 B Y)
            (U0 : CanonicalProfileNetW87 B (fun i => (Y i).toTube) M Ccan)
            (initial : RetainedStateW94 B Y)
            (trace : ActualDropTraceW94 U0 initial CM Cpass (sourceFlatDropW95 p))
            (terminal : RetainedStateW94 B Y),
            B ⊆ F ∧ Nonempty (SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell) ∧
            (B.card : Real) <= (delta : Real) ^ (-7 : Real) ∧
            (delta : ENNReal) ^ bInitial * (∑ i ∈ F, volume (Y i).shade) <=
              ∑ i ∈ B, volume (Y i).shade ∧
            (delta : ENNReal) ^ aInitial <= base.lambda0 ∧
            base.F0 <= (delta : ENNReal) ^ (-fInitial) ∧
            initial.active = B ∧ initial.shading = Y ∧ initial.retained = 1 ∧
            trace.length <= sourceRestartFuelW95 p M ∧
            (∀ n : Fin trace.length,
              Nonempty (SourcePaidDropW95 U0 (trace.state (Fin.castSucc n))
                (trace.state (Fin.succ n)) p CM Kmax Cpass Cwork Ctw Ccell BF)) ∧
            (∀ n : Fin (trace.length + 1),
              (uniformPaidPassCostW95 delta M CM Kmax Cpass ^ n.val)⁻¹ <=
                (trace.state n).retained ∧
              (delta : ENNReal) ^ eFull <= (trace.state n).retained * base.lambda0 ∧
              ((trace.state n).retained * base.lambda0)⁻¹ * base.F0 <=
                (delta : ENNReal) ^ (-eCF)) ∧
            terminal.active ⊆ (trace.state (Fin.last trace.length)).active ∧
            (∀ i ∈ terminal.active, (terminal.shading i).shade ⊆
              ((trace.state (Fin.last trace.length)).shading i).shade) ∧
            (trace.state (Fin.last trace.length)).retained /
                uniformPaidPassCostW95 delta M CM Kmax Cpass <= terminal.retained ∧
            (delta : ENNReal) ^ bLoss * (∑ i ∈ F, volume (Y i).shade) <=
              ∑ i ∈ terminal.active, volume (terminal.shading i).shade ∧
            actualSourceTerminalW95 terminal.active terminal.shading p gamma xiMin M
              Cwork Ctw Ccell BF Cgood := by
  have hcost (CM Ktr : Nat) (Cpass : NNReal) (b : Real) (hb : 0 < b) :
      Filter.Eventually (fun delta : NNReal =>
        uniformPaidPassCostW95 delta M CM Ktr Cpass ^ (sourceRestartFuelW95 p M + 1) <=
          (delta : ENNReal) ^ (-b)) (nhdsWithin 0 (Set.Ioi 0)) := by
    let q : Nat := sourceRestartFuelW95 p M + 1
    let n : Nat := 3 * CM + Ktr
    let D : ENNReal := 8 * (Cpass : ENNReal) * 4 * ((M + 1 : Nat) : ENNReal) * 2 ^ (3 * CM)
    filter_upwards [ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (half_pos hb) (n * q),
      eventually_finite_const_le_rpow_neg (c := D ^ q) (by dsimp [D]; finiteness) (half_pos hb),
      eventually_le_nhdsGT (c := (1 / 2 : NNReal)) (by norm_num),
      self_mem_nhdsWithin] with delta hpoly hconst hdhalf hd0
    have hdpos : 0 < delta := hd0
    have hd1 : delta < 1 := hdhalf.trans_lt (by norm_num)
    have hdR : (0 : Real) < delta := hdpos
    have hlog : 0 <= Real.log (1 / (delta : Real)) := Real.log_nonneg
      ((le_div_iff₀ hdR).mpr (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1.le)))
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 <= 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
    let t : Real := Real.logb 2 (1 / (delta : Real))
    have ht0 : 0 <= t := div_nonneg hlog hlog2pos.le
    have hlogt : Real.log (1 / (delta : Real)) <= t :=
      (le_div_iff₀ hlog2pos).mpr (by nlinarith)
    have htrial : (trialRetainedFractionW94 delta Ktr)⁻¹ =
        ENNReal.ofReal (1 + Real.log (1 / (delta : Real))) ^ Ktr := by
      unfold trialRetainedFractionW94
      rw [Real.rpow_neg (by linarith), Real.rpow_natCast,
        ENNReal.ofReal_inv_of_pos (pow_pos (by linarith) _), inv_inv,
        ENNReal.ofReal_pow (by linarith)]
    have hbound : uniformPaidPassCostW95 delta M CM Ktr Cpass <=
        D * ENNReal.ofReal (1 + t) ^ n := by
      have hc := uniform_paid_pass_cost_le_eight_w95 delta hdpos hd1 M CM Ktr Cpass
      rw [div_eq_mul_inv, htrial] at hc
      have hL : ENNReal.ofReal (2 + t) <= 2 * ENNReal.ofReal (1 + t) := by
        simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2), ENNReal.ofReal_ofNat] using
          ENNReal.ofReal_le_ofReal (show 2 + t <= 2 * (1 + t) by linarith)
      have hT : ENNReal.ofReal (1 + Real.log (1 / (delta : Real))) <= ENNReal.ofReal (1 + t) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      change uniformPaidPassCostW95 delta M CM Ktr Cpass <=
        8 * (Cpass : ENNReal) * 4 * ((M + 1 : Nat) : ENNReal) *
          ENNReal.ofReal ((2 + t) ^ (3 * CM)) *
          ENNReal.ofReal (1 + Real.log (1 / (delta : Real))) ^ Ktr at hc
      rw [ENNReal.ofReal_pow (by linarith : 0 <= 2 + t)] at hc
      calc
        uniformPaidPassCostW95 delta M CM Ktr Cpass <=
            8 * (Cpass : ENNReal) * 4 * ((M + 1 : Nat) : ENNReal) *
              (2 * ENNReal.ofReal (1 + t)) ^ (3 * CM) *
              ENNReal.ofReal (1 + t) ^ Ktr := hc.trans (by gcongr)
        _ = D * ENNReal.ofReal (1 + t) ^ n := by
          dsimp [D, n]
          rw [mul_pow, pow_add]
          ring
    calc
      uniformPaidPassCostW95 delta M CM Ktr Cpass ^ (sourceRestartFuelW95 p M + 1) <=
          (D * ENNReal.ofReal (1 + t) ^ n) ^ q := by gcongr
      _ = D ^ q * ENNReal.ofReal (1 + t) ^ (n * q) := by rw [mul_pow, pow_mul]
      _ <= (delta : ENNReal) ^ (-(b / 2)) * (delta : ENNReal) ^ (-(b / 2)) :=
        mul_le_mul' hconst hpoly
      _ = (delta : ENNReal) ^ (-b) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hdpos).ne' ENNReal.coe_ne_top]
        congr 1
        ring
  have hcostBasic (CM Ktr : Nat) (Cpass : NNReal) (hCpass : 1 <= Cpass)
      (delta : NNReal) (hd : 0 < delta) (hd1 : delta < 1) :
      1 <= uniformPaidPassCostW95 delta M CM Ktr Cpass ∧
        uniformPaidPassCostW95 delta M CM Ktr Cpass < ⊤ := by
    have hlog : 0 <= Real.log (1 / (delta : Real)) := Real.log_nonneg
      ((le_div_iff₀ (show (0 : Real) < delta from hd)).mpr
        (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1.le)))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL1 : 1 <= 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by
      have h := div_nonneg hlog hlog2.le
      linarith
    have hceil : (1 : ENNReal) <=
        Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM) := by
      have h : (1 : Real) <=
          Nat.ceil ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ CM) :=
        (one_le_pow₀ hL1).trans (Nat.le_ceil _)
      exact_mod_cast h
    have hden : 1 <= fullPassDenominatorW87 delta M CM := by
      unfold fullPassDenominatorW87 sourceLambdaMNatW87 sourceLambdaINatW87 sourceLambdaBalNatW87
      exact one_le_mul (one_le_mul (one_le_mul
        (one_le_mul (by norm_num) (by exact_mod_cast (Nat.le_add_left 1 M))) hceil) hceil) hceil
    have htrialpos : 0 < trialRetainedFractionW94 delta Ktr :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
    have htrialle : trialRetainedFractionW94 delta Ktr <= 1 :=
      ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg Ktr)))
    unfold uniformPaidPassCostW95 actualPaidPassCostW94
    refine ⟨?_, ENNReal.div_lt_top (by unfold fullPassDenominatorW87; finiteness) htrialpos.ne'⟩
    rw [div_eq_mul_inv]
    exact one_le_mul (one_le_mul (by exact_mod_cast hCpass) hden) (ENNReal.one_le_inv.mpr htrialle)
  have hreserves {delta : NNReal} (hd : 0 < delta) (hd1 : delta < 1)
      (D lambda F0 retained : ENNReal) (hD : 1 <= D)
      (a b f eFull eCF : Real)
      (hfull : a + b < eFull) (hCF : a + b + f < eCF)
      (hpaid : D ^ (sourceRestartFuelW95 p M + 1) <= (delta : ENNReal) ^ (-b))
      (hlambda : (delta : ENNReal) ^ a <= lambda)
      (hF0 : F0 <= (delta : ENNReal) ^ (-f))
      (n : Nat) (hn : n <= sourceRestartFuelW95 p M + 1)
      (hretained : (D ^ n)⁻¹ <= retained) :
      (delta : ENNReal) ^ b <= retained ∧
        (delta : ENNReal) ^ eFull <= retained * lambda ∧
        (retained * lambda)⁻¹ * F0 <= (delta : ENNReal) ^ (-eCF) := by
    have hdE : (0 : ENNReal) < delta := ENNReal.coe_pos.mpr hd
    have hdE1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd1.le
    have hpow : D ^ n <= (delta : ENNReal) ^ (-b) := (pow_le_pow_right₀ hD hn).trans hpaid
    have hr : (delta : ENNReal) ^ b <= retained := calc
      (delta : ENNReal) ^ b = ((delta : ENNReal) ^ (-b))⁻¹ := by rw [ENNReal.rpow_neg, inv_inv]
      _ <= (D ^ n)⁻¹ := ENNReal.inv_le_inv.mpr hpow
      _ <= retained := hretained
    have hl : (delta : ENNReal) ^ (a + b) <= retained * lambda := calc
      (delta : ENNReal) ^ (a + b) = (delta : ENNReal) ^ b * (delta : ENNReal) ^ a := by
        rw [ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top, mul_comm]
      _ <= retained * lambda := mul_le_mul' hr hlambda
    refine ⟨hr, (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 hfull.le).trans hl, ?_⟩
    calc
      (retained * lambda)⁻¹ * F0 <= ((delta : ENNReal) ^ (a + b))⁻¹ * (delta : ENNReal) ^ (-f) :=
        mul_le_mul' (ENNReal.inv_le_inv.mpr hl) hF0
      _ = (delta : ENNReal) ^ (-(a + b + f)) := by
        rw [← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
        congr 1
        ring
      _ <= (delta : ENNReal) ^ (-eCF) := ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)
  obtain ⟨Ccan, CbaseTw, CbaseCell, Cprep, Kprep, deltaPrep,
    hCcan, hCbaseTw, hCbaseCell, hCprep, hKprep, hdeltaPrep, hdeltaPrep1, htower⟩ :=
    exists_actual_source_regularized_working_tower_w95.{uE,uI} hdim M hp.M_pos Csource hCsource
  obtain ⟨Cwork, Ctw, Ccell, BF, Cgood, Cpass, CM, Kmax, eFull, eCF, deltaPass,
    hCwork, hCtw, hCcell, hBF, hCgood, hCpass, hCM, hKmax, heFull, heCF,
    hdeltaPass, hdeltaPass1, hthresholds, hpass⟩ :=
    exists_actual_paid_pass_w95 hdim hp hgamma hKT hKF
      Csource Ccan CbaseTw CbaseCell hCsource hCcan hCbaseTw hCbaseCell
  have hflat : 0 < sourceFlatDropW95 p :=
    div_pos (mul_pos (sq_pos_of_pos hp.epsilon_pos) (hp.zeta_pos 0 (Nat.zero_le _))) (by norm_num)
  have hrun (a b f : Real) (haf : a + b < eFull) (hacf : a + b + f < eCF)
      {delta : NNReal} (hd : 0 < delta) (hdsmall : delta < deltaPass)
      (hpaid : uniformPaidPassCostW95 delta M CM Kmax Cpass ^
        (sourceRestartFuelW95 p M + 1) <= (delta : ENNReal) ^ (-b))
      {iota : Type uI} [DecidableEq iota]
      (B : Finset iota) (V : iota -> ShadedTube delta E)
      (base : FixedBaseReserveW94 B V)
      (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
      (hregular : SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell)
      (hcentred : ∀ i ∈ B, centredTubeW94 (V i).toTube)
      (hline : lineEssentiallyDistinctW94 B (fun i => (V i).toTube) Csource)
      (hcard : (B.card : Real) <= (delta : Real) ^ (-7 : Real))
      (hlambda : (delta : ENNReal) ^ a <= base.lambda0)
      (hF0 : base.F0 <= (delta : ENNReal) ^ (-f)) :
      ∃ (initial : RetainedStateW94 B V)
        (trace : ActualDropTraceW94 U0 initial CM Cpass (sourceFlatDropW95 p))
        (terminal : RetainedStateW94 B V),
        initial.active = B ∧ initial.shading = V ∧ initial.retained = 1 ∧
        trace.length <= sourceRestartFuelW95 p M ∧
        (∀ n : Fin trace.length,
          Nonempty (SourcePaidDropW95 U0 (trace.state (Fin.castSucc n))
            (trace.state (Fin.succ n)) p CM Kmax Cpass Cwork Ctw Ccell BF)) ∧
        (∀ n : Fin (trace.length + 1),
          (uniformPaidPassCostW95 delta M CM Kmax Cpass ^ n.val)⁻¹ <=
            (trace.state n).retained ∧
          (delta : ENNReal) ^ eFull <= (trace.state n).retained * base.lambda0 ∧
          ((trace.state n).retained * base.lambda0)⁻¹ * base.F0 <= (delta : ENNReal) ^ (-eCF)) ∧
        terminal.active ⊆ (trace.state (Fin.last trace.length)).active ∧
        (∀ i ∈ terminal.active, (terminal.shading i).shade ⊆
          ((trace.state (Fin.last trace.length)).shading i).shade) ∧
        (trace.state (Fin.last trace.length)).retained /
          uniformPaidPassCostW95 delta M CM Kmax Cpass <= terminal.retained ∧
        (delta : ENNReal) ^ b <= terminal.retained ∧
        actualSourceTerminalW95 terminal.active terminal.shading p gamma xiMin M
          Cwork Ctw Ccell BF Cgood := by
    let D := uniformPaidPassCostW95 delta M CM Kmax Cpass
    have hd1 : delta < 1 := hdsmall.trans hdeltaPass1
    have hD : 1 <= D := (hcostBasic CM Kmax Cpass hCpass delta hd hd1).1
    have hDfinite : D ≠ ⊤ := (hcostBasic CM Kmax Cpass hCpass delta hd hd1).2.ne
    have hDzero : D ≠ 0 := (zero_lt_one.trans_le hD).ne'
    let initial : RetainedStateW94 B V := {
      active := B
      shading := V
      active_nonempty := base.nonempty
      active_subset := Finset.Subset.refl _
      same_tube := fun _ _ => rfl
      subshade := fun _ _ => Set.Subset.refl _
      retained := 1
      retained_pos := one_pos
      retained_finite := ENNReal.one_lt_top
      mass_retention := by simp }
    let goodTrace : ActualDropTraceW94 U0 initial CM Cpass (sourceFlatDropW95 p) -> Prop :=
      fun trace =>
        (∀ n : Fin trace.length,
          Nonempty (SourcePaidDropW95 U0 (trace.state (Fin.castSucc n))
            (trace.state (Fin.succ n)) p CM Kmax Cpass Cwork Ctw Ccell BF)) ∧
        (∀ n : Fin (trace.length + 1), (D ^ n.val)⁻¹ <= (trace.state n).retained)
    let possible : Nat -> Prop := fun n =>
      ∃ trace : ActualDropTraceW94 U0 initial CM Cpass (sourceFlatDropW95 p),
        trace.length = n ∧ goodTrace trace
    have hzero : possible 0 := by
      let trace0 : ActualDropTraceW94 U0 initial CM Cpass (sourceFlatDropW95 p) := {
        length := 0
        state := fun _ => initial
        head := rfl
        step := Fin.elim0 }
      refine ⟨trace0, rfl, ?_, ?_⟩
      · intro n
        exact Fin.elim0 n
      · intro n
        have hnlt : n.val < 1 := n.isLt
        have hn : n.val = 0 := by omega
        change (D ^ n.val)⁻¹ <= 1
        simp [hn]
    let maxLength := Nat.findGreatest possible (sourceRestartFuelW95 p M)
    have hmax : possible maxLength := Nat.findGreatest_spec (Nat.zero_le _) hzero
    obtain ⟨trace, hlength, hsteps, hretained⟩ := hmax
    have hlengthBound : trace.length <= sourceRestartFuelW95 p M :=
      (actual_drop_trace_budget_w95 U0 initial trace hd hd1 hflat hcard).2
    have hreserve : ∀ n : Fin (trace.length + 1),
        (D ^ n.val)⁻¹ <= (trace.state n).retained ∧
        (delta : ENNReal) ^ eFull <= (trace.state n).retained * base.lambda0 ∧
        ((trace.state n).retained * base.lambda0)⁻¹ * base.F0 <= (delta : ENNReal) ^ (-eCF) := by
      intro n
      have h := hreserves hd hd1 D base.lambda0 base.F0 (trace.state n).retained hD
        a b f eFull eCF haf hacf hpaid hlambda hF0 n.val (by omega) (hretained n)
      exact ⟨hretained n, h.2⟩
    obtain hterminal | ⟨next, ⟨drop⟩⟩ := hpass hd hdsmall B V base U0 hregular hcentred hline hcard
      (trace.state (Fin.last trace.length)) (hreserve (Fin.last _)).2.1 (hreserve (Fin.last _)).2.2
    · obtain ⟨terminal, hsub, hshade, hpay, hterminal⟩ := hterminal
      have hnextRetained : (D ^ (trace.length + 1))⁻¹ <= terminal.retained := calc
        (D ^ (trace.length + 1))⁻¹ = (D ^ trace.length)⁻¹ / D := by
          rw [pow_succ, ENNReal.mul_inv (Or.inr hDfinite) (Or.inr hDzero), div_eq_mul_inv]
        _ <= (trace.state (Fin.last trace.length)).retained / D :=
          ENNReal.div_le_div_right (hretained (Fin.last trace.length)) D
        _ <= terminal.retained := hpay
      have hlast := (hreserves hd hd1 D base.lambda0 base.F0 terminal.retained hD
        a b f eFull eCF haf hacf hpaid hlambda hF0 (trace.length + 1) (by omega) hnextRetained).1
      exact ⟨initial, trace, terminal, rfl, rfl, rfl, hlengthBound, hsteps, hreserve,
        hsub, hshade, hpay, hlast, hterminal⟩
    · let nextState : Fin (trace.length + 1 + 1) -> RetainedStateW94 B V := Fin.snoc trace.state next
      have hnextStep : ∀ n : Fin (trace.length + 1),
          PaidDropTransitionW94 U0 (nextState (Fin.castSucc n)) (nextState (Fin.succ n))
            CM Cpass (sourceFlatDropW95 p) := by
        intro n
        refine Fin.lastCases ?_ (fun i => ?_) n
        · simpa [nextState] using drop.step
        · simpa only [nextState, Fin.succ_castSucc, Fin.snoc_castSucc] using trace.step i
      let newTrace : ActualDropTraceW94 U0 initial CM Cpass (sourceFlatDropW95 p) := {
        length := trace.length + 1
        state := nextState
        head := by simpa [nextState] using trace.head
        step := hnextStep }
      have hnewGood : goodTrace newTrace := by
        constructor
        · intro n
          refine Fin.lastCases ?_ (fun i => ?_) n
          · simpa [newTrace, nextState] using (show Nonempty (SourcePaidDropW95 U0
              (trace.state (Fin.last trace.length)) next p CM Kmax Cpass Cwork Ctw Ccell BF) from ⟨drop⟩)
          · simpa only [newTrace, nextState, Fin.succ_castSucc, Fin.snoc_castSucc] using hsteps i
        · intro n
          refine Fin.lastCases ?_ (fun i => ?_) n
          · simp only [newTrace, nextState, Fin.snoc_last, Fin.val_last]
            calc
              (D ^ (trace.length + 1))⁻¹ = (D ^ trace.length)⁻¹ / D := by
                rw [pow_succ, ENNReal.mul_inv (Or.inr hDfinite) (Or.inr hDzero), div_eq_mul_inv]
              _ <= (trace.state (Fin.last trace.length)).retained / D :=
                ENNReal.div_le_div_right (hretained (Fin.last trace.length)) D
              _ <= next.retained := drop.uniform_paid
          · simpa [newTrace, nextState] using hretained i
      have hnewBound : newTrace.length <= sourceRestartFuelW95 p M :=
        (actual_drop_trace_budget_w95 U0 initial newTrace hd hd1 hflat hcard).2
      have hnewPossible : possible (trace.length + 1) := ⟨newTrace, rfl, hnewGood⟩
      have hcontr := Nat.le_findGreatest hnewBound hnewPossible
      change trace.length + 1 <= maxLength at hcontr
      omega
  have hinput_card {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (T : iota -> Tube delta E)
      (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
      (hline : lineEssentiallyDistinctW94 F T Csource) :
      (F.card : Real) <= (5 : Real) ^ (6 : Nat) * (Csource : Real) *
        (delta : Real) ^ (-(6 : Real)) := by
    have hd : (0 : Real) < delta := by exact_mod_cast hdelta
    have hd1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
    obtain ⟨P, hPF, hsep, hcover⟩ := exists_maximal_separated_finset F
      (fun i j => ‖(T i).midpoint - (T j).midpoint‖ + ‖(T i).direction - (T j).direction‖)
      (ε := (delta : Real)) (fun i => by simpa using hd)
      (fun i j => by rw [norm_sub_rev (T i).midpoint, norm_sub_rev (T i).direction])
    let assign : iota -> iota := fun i => if hi : i ∈ F then (hcover i hi).choose else i
    have hass : ∀ i ∈ F, assign i ∈ P ∧
        ‖(T i).midpoint - (T (assign i)).midpoint‖ +
          ‖(T i).direction - (T (assign i)).direction‖ < (delta : Real) := by
      intro i hi
      simpa only [assign, dif_pos hi] using (hcover i hi).choose_spec
    have hcluster : ∀ i ∈ F,
        liesInFiveDeltaLineTubeW94 (T i) (T (assign i)).midpoint (T (assign i)).direction := by
      intro i hi x hx
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp ((T i).carrier_eq ▸ hx)
      rw [segment_eq_image'] at hz
      obtain ⟨theta, htheta, hthetaZ⟩ := hz
      let t : Real := theta - 1 / 2
      have ht : |t| <= 1 / 2 := by
        rw [abs_le]
        dsimp [t]
        constructor <;> linarith [htheta.1, htheta.2]
      have hzt : z = (T i).midpoint + t • (T i).direction := by
        rw [← hthetaZ]
        dsimp [t, Tube.midpoint, Tube.direction]
        module
      let j := assign i
      have hzclose : dist z ((T j).midpoint + t • (T j).direction) <= (delta : Real) := by
        rw [hzt, dist_eq_norm]
        have heq : (T i).midpoint + t • (T i).direction -
            ((T j).midpoint + t • (T j).direction) =
            ((T i).midpoint - (T j).midpoint) + t • ((T i).direction - (T j).direction) := by module
        rw [heq]
        calc
          _ <= ‖(T i).midpoint - (T j).midpoint‖ +
              |t| * ‖(T i).direction - (T j).direction‖ := by
            simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
              ((T i).midpoint - (T j).midpoint) (t • ((T i).direction - (T j).direction))
          _ <= (delta : Real) := by
            have hdist := (hass i hi).2
            change ‖(T i).midpoint - (T j).midpoint‖ +
              ‖(T i).direction - (T j).direction‖ < (delta : Real) at hdist
            nlinarith [norm_nonneg ((T i).direction - (T j).direction)]
      refine ⟨t, ?_⟩
      have htri := dist_triangle x z ((T j).midpoint + t • (T j).direction)
      have hxz' := Metric.mem_closedBall.mp hxz
      change dist x ((T j).midpoint + t • (T j).direction) <= 5 * (delta : Real)
      linarith
    have hfibrecard : ∀ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) <= Csource := by
      intro j hj
      have hsub : F.filter (fun i => assign i = j) ⊆
          F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T j).midpoint (T j).direction) := by
        intro i hi
        obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hiF, hij ▸ hcluster i hiF⟩
      have hcap := hline (T j).midpoint (T j).direction (T j).norm_direction
      have hcapR : ((F.filter (fun i => liesInFiveDeltaLineTubeW94
          (T i) (T j).midpoint (T j).direction)).card : Real) <= Csource := by exact_mod_cast hcap
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcapR
    have hcardFP : (F.card : Real) <= (P.card : Real) * Csource := by
      calc
        (F.card : Real) = ∑ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to (fun i hi => (hass i hi).1) (fun _ => (1 : Real))).symm
        _ <= ∑ j ∈ P, (Csource : Real) := Finset.sum_le_sum hfibrecard
        _ = (P.card : Real) * Csource := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcardP : (P.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) := by
      have hpack := Tube.card_le_of_L1_separated_in_box P
        (fun i => (T i).midpoint) (fun i => (T i).direction) (0 : E) (0 : E)
        (R := (1 : Real)) hd hsep
        (fun i hi => by simpa using Tube.norm_midpoint_le_of_subset_ball hdelta (T i) (hball i (hPF hi)))
        (fun i hi => by simpa using (T i).norm_direction.le)
      rw [hdim] at hpack
      have hratio : ((1 : Real) + (delta : Real) / 4) / ((delta : Real) / 4) <= 5 / (delta : Real) := by
        apply (div_le_div_iff₀ (by positivity) hd).mpr
        nlinarith
      exact hpack.trans (pow_le_pow_left₀ (by positivity) hratio 6)
    calc
      (F.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) * Csource :=
        hcardFP.trans (mul_le_mul_of_nonneg_right hcardP Csource.coe_nonneg)
      _ = (5 : Real) ^ (6 : Nat) * (Csource : Real) * (delta : Real) ^ (-(6 : Real)) := by
        rw [div_pow, Real.rpow_neg hd.le]
        norm_num only [Real.rpow_ofNat]
        ring
  let e : Real := min (p.η 0 / 1000) (min eFull (min eCF bLoss)) / 20
  have he : 0 < e := by
    apply div_pos (lt_min (div_pos (hp.zeta_pos 0 (Nat.zero_le _)) (by norm_num))
      (lt_min heFull (lt_min heCF hbLoss)))
    norm_num
  have heTop : 20 * e <= p.η 0 / 1000 := by
    dsimp [e]
    linarith [min_le_left (p.η 0 / 1000) (min eFull (min eCF bLoss))]
  have heFullBound : 20 * e <= eFull := by
    have h := (min_le_right (p.η 0 / 1000) (min eFull (min eCF bLoss))).trans
      (min_le_left eFull (min eCF bLoss))
    dsimp [e]
    linarith
  have heCFBound : 20 * e <= eCF := by
    have h := ((min_le_right (p.η 0 / 1000) (min eFull (min eCF bLoss))).trans
      (min_le_right eFull (min eCF bLoss))).trans (min_le_left eCF bLoss)
    dsimp [e]
    linarith
  have heLoss : 20 * e <= bLoss := by
    have h := ((min_le_right (p.η 0 / 1000) (min eFull (min eCF bLoss))).trans
      (min_le_right eFull (min eCF bLoss))).trans (min_le_right eCF bLoss)
    dsimp [e]
    linarith
  have hprepPay : Filter.Eventually (fun delta : NNReal => (delta : ENNReal) ^ e <=
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
  have hsmall := ((hcost CM Kmax Cpass e he).and hprepPay).and
    (eventually_finite_const_le_rpow_neg (c := (5 : ENNReal) ^ (6 : Nat) * Csource)
      (by finiteness) (by norm_num : (0 : Real) < 1))
  obtain ⟨deltaCut, hdeltaCut, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  let delta0 : NNReal := min deltaPrep (min deltaPass deltaCut)
  have hdelta0 : 0 < delta0 := lt_min hdeltaPrep (lt_min hdeltaPass hdeltaCut)
  have hdelta01 : delta0 < 1 := (min_le_left _ _).trans_lt hdeltaPrep1
  refine ⟨Ccan, CbaseTw, CbaseCell, Cwork, Ctw, Ccell, BF, Cgood, Cpass,
    CM, Kmax, e, eFull, eCF, 2 * e, e, 3 * e, e, delta0,
    hCcan, hCbaseTw, hCbaseCell, hCwork, hCtw, hCcell, hBF, hCgood, hCpass,
    hCM, hKmax, he, by linarith, heFull, heCF, by positivity, he, by positivity, he,
    by linarith, by linarith, by linarith, hdelta0, hdelta01, hthresholds, ?_⟩
  intro delta hd hdsmall
  have hdPrep : delta < deltaPrep := hdsmall.trans_le (min_le_left _ _)
  have hdPass : delta < deltaPass := hdsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdCut : delta < deltaCut := hdsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨⟨hpaid, hprep⟩, hcoeff⟩ := hcut ⟨hd, hdCut⟩
  refine ⟨hpaid, ?_⟩
  intro iota inst F Y hF hball hcentred hline hfull hCF
  have hd1 : delta < 1 := hdsmall.trans hdelta01
  have hdE : (0 : ENNReal) < delta := ENNReal.coe_pos.mpr hd
  have hdR : (0 : Real) < delta := hd
  have hdE1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd1.le
  have hmass : 0 < ∑ i ∈ F, volume (Y i).shade := by
    have hfullpos : 0 < fullness' F (fun i => (Y i).toShadedBody) :=
      (ENNReal.rpow_pos hdE ENNReal.coe_ne_top).trans_le hfull
    by_contra h
    have hz : (∑ i ∈ F, volume (Y i).shade) = 0 := le_antisymm (not_lt.mp h) bot_le
    simp only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] at hfullpos
  obtain ⟨B, U0, hB, hBFsub, hprepared, ⟨hregular⟩⟩ :=
    htower hd hdPrep F Y hball hcentred hline hmass
  have hmassB : (delta : ENNReal) ^ e * (∑ i ∈ F, volume (Y i).shade) <=
      ∑ i ∈ B, volume (Y i).shade := (mul_le_mul' hprep le_rfl).trans hprepared
  obtain ⟨i0, hi0⟩ := hF
  obtain ⟨hvpos, hvfin⟩ := Tube.volume_pos_and_lt_top hd hd1.le (Y i0).toTube
  obtain ⟨_, hfullB, _, hCFB⟩ := retained_state_fullness_card_frostman_w94
    F B (fun i => (Y i).toShadedBody) (fun i => (Y i).toShadedBody)
    ConvexSpaceBody.closedUnitBall (volume (Y i0).carrier) ((delta : ENNReal) ^ e)
    ((delta : ENNReal) ^ (-e)) ((delta : ENNReal) ^ e)
    ⟨i0, hi0⟩ hBFsub hvpos hvfin
    (fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube)
    (fun i hi => hball i hi) ConvexSpaceBody.closedUnitBall_volume_pos
    ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
    (fun i hi => rfl) (fun i hi => Set.Subset.refl _)
    (ENNReal.rpow_pos hdE ENNReal.coe_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg he.le ENNReal.coe_ne_top) hfull hCF
    ((ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top).lt_top)
    (ENNReal.rpow_pos hdE ENNReal.coe_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg he.le ENNReal.coe_ne_top) hmassB
  have hfullBpaid : (delta : ENNReal) ^ (2 * e) <= fullness' B (fun i => (Y i).toShadedBody) := by
    convert hfullB using 1
    rw [← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
    congr 1
    ring
  have hCFBpaid : frostmanConstIn B (fun i => (Y i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-(3 * e)) := by
    calc
      frostmanConstIn B (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          ((delta : ENNReal) ^ e * (delta : ENNReal) ^ e)⁻¹ * (delta : ENNReal) ^ (-e) := hCFB
      _ = (delta : ENNReal) ^ (-(3 * e)) := by
        rw [← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
        congr 1
        ring
  let base : FixedBaseReserveW94 B Y := {
    nonempty := hB
    delta_pos := hd
    delta_lt_one := hd1
    carrierVolume := volume (Y i0).carrier
    carrierVolume_pos := hvpos
    carrierVolume_finite := hvfin
    common_volume := fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
    ball := fun i hi => hball i (hBFsub hi)
    lambda0 := (delta : ENNReal) ^ (2 * e)
    lambda0_pos := ENNReal.rpow_pos hdE ENNReal.coe_ne_top
    lambda0_finite := (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top).lt_top
    fullness := hfullBpaid
    F0 := (delta : ENNReal) ^ (-(3 * e))
    F0_finite := (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top).lt_top
    frostman := hCFBpaid }
  have hcoeffR : (5 : Real) ^ (6 : Nat) * (Csource : Real) <= (delta : Real) ^ (-(1 : Real)) := by
    have h := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_ne_zero hdE.ne' ENNReal.coe_ne_top) hcoeff
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using h
  have hcardF : (F.card : Real) <= (delta : Real) ^ (-7 : Real) := calc
    (F.card : Real) <= (5 : Real) ^ (6 : Nat) * Csource * (delta : Real) ^ (-(6 : Real)) :=
      hinput_card hd hd1.le F (fun i => (Y i).toTube) hball hline
    _ <= (delta : Real) ^ (-(1 : Real)) * (delta : Real) ^ (-(6 : Real)) :=
      mul_le_mul_of_nonneg_right hcoeffR (Real.rpow_nonneg delta.coe_nonneg _)
    _ = (delta : Real) ^ (-7 : Real) := by rw [← Real.rpow_add hdR]; norm_num
  have hcardB : (B.card : Real) <= (delta : Real) ^ (-7 : Real) :=
    (Nat.cast_le.mpr (Finset.card_le_card hBFsub)).trans hcardF
  have hlineB : lineEssentiallyDistinctW94 B (fun i => (Y i).toTube) Csource := by
    intro o v hv
    exact (show ((B.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v)).card : NNReal) <=
      (F.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v)).card by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hBFsub)).trans (hline o v hv)
  obtain ⟨initial, trace, terminal, hia, his, hir, hlength, hsteps, hres,
    hsub, hshade, hpay, hret, hterminal⟩ :=
    hrun (2 * e) e (3 * e) (by linarith) (by linarith) hd hdPass hpaid B Y base U0
      hregular (fun i hi => hcentred i (hBFsub hi)) hlineB hcardB le_rfl le_rfl
  refine ⟨B, base, U0, initial, trace, terminal, hBFsub, ⟨hregular⟩, hcardB, hmassB,
    le_rfl, le_rfl, hia, his, hir, hlength, hsteps, hres, hsub, hshade, hpay, ?_, hterminal⟩
  calc
    (delta : ENNReal) ^ bLoss * (∑ i ∈ F, volume (Y i).shade) <=
        (delta : ENNReal) ^ (2 * e) * (∑ i ∈ F, volume (Y i).shade) :=
      mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)) le_rfl
    _ = (delta : ENNReal) ^ e * ((delta : ENNReal) ^ e * (∑ i ∈ F, volume (Y i).shade)) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hdE.ne' ENNReal.coe_ne_top]
      congr 2
      ring
    _ <= (delta : ENNReal) ^ e * (∑ i ∈ B, volume (Y i).shade) := mul_le_mul' le_rfl hmassB
    _ <= terminal.retained * (∑ i ∈ B, volume (Y i).shade) := mul_le_mul' hret le_rfl
    _ <= ∑ i ∈ terminal.active, volume (terminal.shading i).shade := terminal.mass_retention

end

end Kakeya.ml1Boot.TrialRestartW94

