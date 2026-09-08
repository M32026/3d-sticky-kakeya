module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualSourceTerminalCentredW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourcePassNumericsConstructionW104
public import Kakeya.DimensionThree.MainLemma1.MassRetention

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.TrialRestartW94

open RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

universe uE uI
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem actual_every_scale_node_w104
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube delta E} {M N : Nat} {Ccan BF : NNReal}
    {eps : Real} (U : CanonicalProfileNetW87 F (fun i => (Y i).toTube) M Ccan)
    (h : actualEveryScaleW95 U eps N BF) :
    U.IsFrostmanAtEveryScale ((BF : ENNReal) ^ (N + 1) * (delta : ENNReal) ^ (-3 * eps)) := by
  intro k hk R hR
  apply ConvexSpaceBody.frostmanConstant_le_iff.mp
  convert h k hk R hR using 1
  simp [frostmanConstIn_eq_frostmanConstant, completeFibreW94, Tube.coverClass]
  congr 1
  ext i
  simp

theorem exists_source_input_alternative_w104
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero gamma xiMin : Real}
    {xi : Fin (p.N + 1) -> Real} {M : Nat}
    (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma)
    (Csource : NNReal) (hCsource : 1 <= Csource)
    (bLoss : Real) (hbLoss : 0 < bLoss) :
    ∃ (Cgood Cwork Ctw Ccell BF : NNReal) (eInput : Real) (delta0 : NNReal),
      1 <= Cgood ∧ 1 <= Cwork ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧
      0 < eInput ∧ eInput < p.η 0 / 1000 ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E),
        F.Nonempty -> (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
        lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Csource ->
        (delta : ENNReal) ^ eInput <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (delta : ENNReal) ^ (-eInput) ->
        (ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
          (Cgood : ENNReal) * (delta : ENNReal) ^ (18 * xiMin - bLoss) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((F.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2)) ∨
        (∃ (A : Finset iota) (Z : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Z i).toTube) M Cwork),
          A.Nonempty ∧ A ⊆ F ∧
          (∀ i ∈ A, (Z i).toTube = (Y i).toTube) ∧
          (∀ i ∈ A, (Z i).shade ⊆ (Y i).shade) ∧
          (delta : ENNReal) ^ bLoss * (∑ i ∈ F, volume (Y i).shade) <=
            ∑ i ∈ A, volume (Z i).shade ∧
          Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
          U.IsFrostmanAtEveryScale ((BF : ENNReal) ^ (p.N + 1) * (delta : ENNReal) ^ (-3 * p.ε))) := by
  obtain ⟨Ccan, CbaseTw, CbaseCell, Cwork, Ctw, Ccell, BF, Cgood, Cpass, CM, Kmax,
    eInput, eFull, eCF, aInitial, bInitial, fInitial, bReserve, delta0,
    hCcan, hCbaseTw, hCbaseCell, hCwork, hCtw, hCcell, hBF, hCgood, hCpass,
    hCM, hKmax, heInput, heInputSmall, heFull, heCF, haInitial, hbInitial,
    hfInitial, hbReserve, hbsum, hasum, hfsum, hdelta0, hdelta1, hThresh, hRun⟩ :=
    exists_actual_source_terminal_run_w95 hdim hp hgamma hKT hKF Csource hCsource bLoss hbLoss
  refine ⟨Cgood, Cwork, Ctw, Ccell, BF, eInput, delta0,
    hCgood, hCwork, hCtw, hCcell, hBF, heInput, heInputSmall, hdelta0, hdelta1, ?_⟩
  intro delta hd hdsmall iota _ F Y hF hball hcentred hline hfull hCF
  obtain ⟨B, base, U0, initial, trace, terminal, hBFset, hreg, hcard,
    hmassB, hbaseLambda, hbaseFrostman, hinitA, hinitY, hinitR, htrace,
    hDrop, hstates, htermSubset, htermShade, htermret, hmassTerminal, hterminal⟩ :=
    (hRun hd hdsmall).2 F Y hF hball hcentred hline hfull hCF
  have hAF : terminal.active ⊆ F := terminal.active_subset.trans hBFset
  rcases hterminal with hgood | ⟨U, hregular, hevery⟩
  · left
    have hde0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
    have hp0 : (delta : ENNReal) ^ bLoss ≠ 0 := by
      simp only [ne_eq, ENNReal.rpow_eq_zero_iff, hde0, ENNReal.coe_ne_top, false_and, or_self, not_false_eq_true]
    have hpTop : (delta : ENNReal) ^ bLoss ≠ ⊤ := by finiteness
    have hmass : (∑ i ∈ F, volume (Y i).shade) <=
        (delta : ENNReal) ^ (-bLoss) * (∑ i ∈ terminal.active, volume (terminal.shading i).shade) := by
      rw [ENNReal.rpow_neg]
      calc
        (∑ i ∈ F, volume (Y i).shade) = ((delta : ENNReal) ^ bLoss)⁻¹ *
            ((delta : ENNReal) ^ bLoss * (∑ i ∈ F, volume (Y i).shade)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpTop, one_mul]
        _ <= _ := mul_le_mul_right hmassTerminal _
    have hunion : (⋃ i ∈ terminal.active, (terminal.shading i).shade) ⊆ ⋃ i ∈ F, (Y i).shade := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨i, hAF hi, terminal.subshade i hi hxi⟩
    have hmu := Kakeya.ml1Boot.multiplicity_le_mul_of_shade_mass
      (fun i => (Y i).toShadedBody) (fun i => (terminal.shading i).toShadedBody) hunion hmass
    have hq : 0 <= 1 - gamma / 2 := by linarith [hgamma.2]
    have hcard' : (terminal.active.card : ENNReal) <= (F.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hAF
    have hpow : (delta : ENNReal) ^ (-bLoss) * (delta : ENNReal) ^ (18 * xiMin) =
        (delta : ENNReal) ^ (18 * xiMin - bLoss) := by
      rw [← ENNReal.rpow_add _ _ hde0 ENNReal.coe_ne_top]
      congr 1
      ring
    calc
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
          (delta : ENNReal) ^ (-bLoss) * ShadedBody.multiplicity terminal.active
            (fun i => (terminal.shading i).toShadedBody) := hmu
      _ <= (delta : ENNReal) ^ (-bLoss) * ((Cgood : ENNReal) * (delta : ENNReal) ^ (18 * xiMin) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((delta : ENNReal) ^ (2 : Nat) * (terminal.active.card : ENNReal)) ^ (1 - gamma / 2)) :=
        mul_le_mul_right hgood _
      _ <= (delta : ENNReal) ^ (-bLoss) * ((Cgood : ENNReal) * (delta : ENNReal) ^ (18 * xiMin) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((delta : ENNReal) ^ (2 : Nat) * (F.card : ENNReal)) ^ (1 - gamma / 2)) := by gcongr
      _ = (Cgood : ENNReal) * ((delta : ENNReal) ^ (-bLoss) * (delta : ENNReal) ^ (18 * xiMin)) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((F.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        rw [mul_comm ((delta : ENNReal) ^ (2 : Nat)) (F.card : ENNReal)]
        ring
      _ = _ := by rw [hpow]
  · exact Or.inr ⟨terminal.active, terminal.shading, U, terminal.active_nonempty, hAF,
      terminal.same_tube, terminal.subshade, hmassTerminal, hregular, actual_every_scale_node_w104 U hevery⟩

end
end Kakeya.ml1Boot.TrialRestartW94
