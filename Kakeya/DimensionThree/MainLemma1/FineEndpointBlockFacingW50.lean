module

public import Kakeya.DimensionThree.MainLemma1.LossLedger

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- The fine field of an endpoint factor is automatic.  This narrow-import
version is suitable for use before `CaseTwo`: it depends only on the factor
structure and the parameter numerics. -/
theorem endpoint_fine_bound_narrow_w50 [Nontrivial E]
    {p : Params} {gamma : Real} {m : Nat} {delta theta : NNReal}
    {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {tTheta tc : Finset iota} {TTheta : iota -> Tube theta E}
    {pTheta : iota -> iota} {kF lM : iota}
    {Yf Ym : iota -> ShadedTube delta E}
    {Yc : iota -> ShadedTube theta E}
    {beta gammaZero : Real} (hp : p.Spec beta gammaZero)
    (hm : m < p.N) (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {Lfact Lcard : ENNReal}
    (hfac : IsTwoScaleFactors Lfact Lcard
      s T s (fun i => (T i).toTube) id tTheta TTheta pTheta
      kF Yf 0 lM Ym 0 tc Yc 0) :
    ShadedBody.multiplicity (fibre s id kF)
        (fun i => (Yf i).toShadedBody) <=
      (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) *
        ((delta / delta : NNReal) : ENNReal) ^ (-2 * gamma) *
        (((fibre s id kF).card : ENNReal) *
          ((delta / delta : NNReal) : ENNReal) ^ (2 : Nat)) ^
            (1 - gamma / 2) := by
  have hfibre : fibre s id kF = {kF} := by
    ext i
    simp only [fibre, Finset.mem_filter, id_eq, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro hi
      subst i
      exact ⟨hfac.fine_mem, rfl⟩
  have hmult : ShadedBody.multiplicity (fibre s id kF)
      (fun i => (Yf i).toShadedBody) <= (1 : ENNReal) := by
    rw [hfibre]
    simpa using ShadedBody.multiplicity_le_card ({kF} : Finset iota)
      (fun i => (Yf i).toShadedBody)
  have hetaMono : p.η 0 <= p.η m :=
    hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _))
      (Set.mem_Iic.mpr hm.le) (Nat.zero_le _)
  have heps : 0 <= p.ε' := by
    rw [hp.epsPrimeEq]
    linarith [hp.etaZeroPos]
  have hdeltaPow : (1 : ENNReal) <=
      (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) := by
    apply ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
    · exact_mod_cast hdelta0
    · exact_mod_cast hdelta1
    · linarith [hp.etaZeroPos]
  have hratio : (delta / delta : NNReal) = 1 :=
    div_self (ne_of_gt hdelta0)
  rw [hratio]
  simpa [hfibre] using hmult.trans hdeltaPow

/-- Raw CaseTwo data produce an endpoint factor, its exact loss certificate,
and its fine analytic field on one witness.  No flatness threshold or analytic
callback occurs in this interface. -/
theorem eventually_exists_caseTwo_endpoint_exact_fine_w50 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {gamma : Real}
    (Cd : NNReal) (Kd cd : Nat) (hCd1 : 1 <= Cd)
    (C0 : NNReal) (hC0 : 1 <= C0) :
    ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ∀ {iota : Type u} [DecidableEq iota],
      ∀ (s s2 s' : Finset iota) (T : iota -> ShadedTube delta E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ->
        (s : Set iota).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ->
        s2 ⊆ s -> s2.Nonempty -> s' ⊆ s2 ->
        (∀ t ⊆ s2, t.Nonempty ->
          (delta : ENNReal) ^ p.η 0 <=
            (ShadedBody.fullness t (fun i => (T i).toShadedBody) : ENNReal)) ->
        ConvexSpaceBody.frostmanConstant s2
            (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall <=
          ENNReal.ofReal ((delta : Real) ^ (-p.η 0)) ->
        (s2.card : ENNReal) <=
          StickyKakeya.totalLoss Cd Kd cd delta * (s'.card : ENNReal) ->
        ∀ (U : Tube.UniformTubeSet s'
          (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cd), U.Nice ->
        ∀ a b m : Nat,
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
          ∃ (tm tTheta tThetaAct : Finset iota)
            (TTheta : iota ->
              Tube (Tube.gridScale delta (Tube.ssfGridLen delta) a) E)
            (pTheta : iota -> iota) (kF lM : iota)
            (Yf : iota -> ShadedTube delta E)
            (Ym : iota -> ShadedTube delta E)
            (Yc : iota ->
              ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) a) E),
            delta <= Tube.gridScale delta (Tube.ssfGridLen delta) a ∧
            Tube.gridScale delta (Tube.ssfGridLen delta) a <= 1 ∧
            0 < s.card ∧ tm.Nonempty ∧ tThetaAct.Nonempty ∧
            (s.card : Real) <= (delta : Real) ^ (-(7 : Real)) ∧
            (tm.card : Real) <= (delta : Real) ^ (-(7 : Real)) ∧
            tm ⊆ s ∧ tThetaAct ⊆ tTheta ∧
            IsParentFamily s (fun i => (T i).toTube)
              tTheta TTheta pTheta ∧
            IsTwoScaleFactors
              (factorTwoScales.C s.card delta tm.card delta : ENNReal)
              ((((Cd ^ 2 : NNReal) : ENNReal)) ^ 4)
              s T s (fun i => (T i).toTube) id tTheta TTheta pTheta
              kF Yf 0 lM Ym 0 tThetaAct Yc 0 ∧
            (factorTwoScales.C s.card delta tm.card delta : ENNReal) <=
              (((C0 * factorTwoScales.C s.card delta tm.card delta : NNReal) :
                  ENNReal)) *
                (delta : ENNReal) ^ (-p.ε') ∧
            ShadedBody.multiplicity (fibre s id kF)
                (fun i => (Yf i).toShadedBody) <=
              (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) *
                ((delta / delta : NNReal) : ENNReal) ^ (-2 * gamma) *
                (((fibre s id kF).card : ENNReal) *
                  ((delta / delta : NNReal) : ENNReal) ^ (2 : Nat)) ^
                    (1 - gamma / 2) := by
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_one_nhdsGT, self_mem_nhdsWithin]
    with delta hpack hdelta1 hdelta0
  intro iota _ s s2 s' T hball hED hs2s hs2ne hs's2 hhered hFrost
    hcard U hNice a b m hblock
  obtain ⟨_hs'ne, _hs's, tm, tTheta, tThetaAct, TTheta, pTheta,
      kF, lM, Yf, Ym, Yc, htmne, htcne, htms, htctTheta, hparent,
      hfactor, hLfact⟩ :=
    exists_caseTwo_ambient_fineEndpoint_productOnly_with_loss
      (E := E) hdim hp hdelta0 hdelta1 T hball hED hs2s hs2ne hs's2
      hhered hFrost Cd Kd cd hCd1 hcard U hNice a b m hblock C0 hC0
  have hgrid := gridScale_block_bracket hdelta0 hdelta1
    hblock.coarse_lt_fine hblock.fine_le
  have hcardS : (s.card : Real) <= (delta : Real) ^ (-(7 : Real)) :=
    hpack delta le_rfl s (fun i => (T i).toTube) hball hED
  have hcardMid : (tm.card : Real) <=
      (delta : Real) ^ (-(7 : Real)) := by
    have hsub : (tm.card : Real) <= (s.card : Real) := by
      exact_mod_cast Finset.card_le_card htms
    exact hsub.trans hcardS
  have hmN : m < p.N := hblock.exponent_lt
  have hFine := endpoint_fine_bound_narrow_w50
    (E := E) (p := p) (gamma := gamma) (m := m)
    (delta := delta)
    (theta := Tube.gridScale delta (Tube.ssfGridLen delta) a)
    (s := s) (T := T) (tTheta := tTheta) (tc := tThetaAct)
    (TTheta := TTheta) (pTheta := pTheta) (kF := kF) (lM := lM) (Yf := Yf)
    (Ym := Ym) (Yc := Yc) hp hmN hdelta0 hdelta1 hfactor
  refine ⟨tm, tTheta, tThetaAct, TTheta, pTheta, kF, lM, Yf, Ym,
    Yc, hgrid.1.trans hgrid.2.1, hgrid.2.2,
    Finset.card_pos.mpr (hs2ne.mono hs2s), htmne, htcne,
    hcardS, hcardMid, htms, htctTheta, hparent, hfactor, hLfact, hFine⟩

end
end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.endpoint_fine_bound_narrow_w50
#print axioms Kakeya.ml1Boot.eventually_exists_caseTwo_endpoint_exact_fine_w50

end
