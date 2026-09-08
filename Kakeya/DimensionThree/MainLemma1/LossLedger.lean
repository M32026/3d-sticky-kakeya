module

public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame
public import Kakeya.DimensionThree.MainLemma1.BlockSkeleton
public import Kakeya.DimensionThree.MainLemma1.TwoScaleProductOnly

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u

/-!
The scalar loss expected by the exact B3 certificate is already the loss of the
product-only producer, provided that producer is run on the ambient family `s`.
No cardinality-retention or fullness loss belongs in `Lfact` at this interface.
-/

/-- The product-only loss on the ambient family has exactly the loss shape required by
`eventually_b3_exact_tail_consumer`.  This is deliberately pointwise: the only scale fact
needed is `delta <= 1`, and the parameter package supplies positivity of `epsilon'`. -/
theorem productOnly_ambient_loss_le_exact
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta tau : NNReal} (hdelta1 : delta <= 1)
    (M : Nat) (sCard midCard : Nat) :
    (4 * (M : ENNReal)) *
          (factorTwoScales.C sCard delta midCard tau : ENNReal)
      <= ((((4 * M : Nat) : NNReal) *
          factorTwoScales.C sCard delta midCard tau : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-p.ε') := by
  have heps : 0 <= p.ε' := by
    rw [hp.epsPrimeEq]
    nlinarith [hp.etaZeroPos]
  have hdeltaE : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hone : (1 : ENNReal) <= (delta : ENNReal) ^ (-p.ε') := by
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one hdeltaE heps
  calc
    (4 * (M : ENNReal)) *
          (factorTwoScales.C sCard delta midCard tau : ENNReal)
        = ((((4 * M : Nat) : NNReal) *
            factorTwoScales.C sCard delta midCard tau : NNReal) : ENNReal) * 1 := by
          push_cast
          ring
    _ <= ((((4 * M : Nat) : NNReal) *
            factorTwoScales.C sCard delta midCard tau : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-p.ε') := by gcongr

/-- Exact specialization for the `hcert` loss field.  It exposes the fixed constant as
`C0 = 4*M` and keeps the two cardinalities in precisely the order used by
`factorTwoScales.C` in the master analytic endgame. -/
theorem exists_C0_productOnly_ambient_loss_le_exact
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta tau : NNReal} (hdelta1 : delta <= 1)
    (M : Nat) (sCard midCard : Nat) :
    exists C0 : NNReal,
      C0 = (4 * M : Nat) /\
      (4 * (M : ENNReal)) *
            (factorTwoScales.C sCard delta midCard tau : ENNReal)
        <= (((C0 * factorTwoScales.C sCard delta midCard tau : NNReal) : ENNReal)) *
          (delta : ENNReal) ^ (-p.ε') := by
  refine ⟨((4 * M : Nat) : NNReal), rfl, ?_⟩
  exact productOnly_ambient_loss_le_exact hp hdelta1 M sCard midCard

/-! The factorization constant itself (without the fixed-ball `4*M` cell price) has the
same exact ledger shape.  This is the form used by the normalized ambient producer
`exists_twoScaleProductOnly`; the fixed-ball port uses the preceding theorem instead. -/

theorem factorTwoScales_C_le_exact
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta tau : NNReal} (hdelta1 : delta <= 1)
    (C0 : NNReal) (hC0 : 1 <= C0) (sCard midCard : Nat) :
    (factorTwoScales.C sCard delta midCard tau : ENNReal)
      <= (((C0 * factorTwoScales.C sCard delta midCard tau : NNReal) : ENNReal)) *
        (delta : ENNReal) ^ (-p.ε') := by
  have heps : 0 <= p.ε' := by
    rw [hp.epsPrimeEq]
    nlinarith [hp.etaZeroPos]
  have hdeltaE : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hone : (1 : ENNReal) <= (delta : ENNReal) ^ (-p.ε') := by
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one hdeltaE heps
  have hC0E : (1 : ENNReal) <= (C0 : ENNReal) := by exact_mod_cast hC0
  calc
    (factorTwoScales.C sCard delta midCard tau : ENNReal)
        = (factorTwoScales.C sCard delta midCard tau : ENNReal) * 1 := by ring
    _ <= (factorTwoScales.C sCard delta midCard tau : ENNReal) * (C0 : ENNReal) := by
      exact mul_le_mul_of_nonneg_left hC0E (by positivity)
    _ = ((factorTwoScales.C sCard delta midCard tau : ENNReal) * (C0 : ENNReal)) * 1 := by
      ring
    _ <= ((factorTwoScales.C sCard delta midCard tau : ENNReal) * (C0 : ENNReal)) *
          (delta : ENNReal) ^ (-p.ε') := by
      exact mul_le_mul_left' hone _
    _ = (((C0 * factorTwoScales.C sCard delta midCard tau : NNReal) : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-p.ε') := by
      rw [ENNReal.coe_mul]
      ring

/-! ### Ambient producer interface

The normalized product-only producer can be run on the *same* ambient family that appears in
the Case-II consumer.  The theorem below retains the selected-fibre and tube fields that the
short public `exists_twoScaleProductOnly` projection omits, and records the one scalar ledger
needed by `AnalyticEndgameW27`.  The branch/cardinality comparison is intentionally an explicit
input: it is a hierarchy fact, not a consequence of the scalar product estimate. -/

section AmbientProducer

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]

theorem exists_ambient_twoScaleFactors_productOnly_with_loss
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta tau theta : NNReal} (hdelta0 : 0 < delta) (hdeltaTau : delta <= tau)
    (htauTheta : tau <= theta) (htheta1 : theta <= 1)
    {s : Finset ι} {tTau tTheta : Finset κ}
    (T : ι → ShadedTube delta E) (TTau : κ → Tube tau E) (pTau : ι → κ)
    (TTheta : κ → Tube theta E) (pTheta : κ → κ)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparentFine : IsParentFamily s (fun i => (T i).toTube) tTau TTau pTau)
    (hmass : 0 < ∑ i ∈ s, volume (T i).shade)
    (hballTau : ∀ k ∈ tTau, (TTau k).carrier ⊆ Metric.closedBall 0 1)
    (hparentCoarse : IsParentFamily tTau TTau tTheta TTheta pTheta)
    {Lcard : ENNReal}
    (hbranch : ∀ {kF lM : κ} {tThetaAct : Finset κ},
      ((fibre s pTau kF).card : ENNReal) *
          ((fibre tTau pTheta lM).card : ENNReal) * (tThetaAct.card : ENNReal)
        ≤ Lcard * (s.card : ENNReal))
    (C0 : NNReal) (hC0 : 1 ≤ C0) :
    ∃ (tm tc : Finset κ) (kF lM : κ)
      (Yf : ι → ShadedTube delta E) (Ym : κ → ShadedTube tau E)
      (Yc : κ → ShadedTube theta E),
      tm.Nonempty ∧ tc.Nonempty ∧ tm ⊆ tTau ∧ tc ⊆ tTheta ∧
      IsTwoScaleFactors
        (factorTwoScales.C s.card delta tm.card tau : ENNReal) Lcard
        s T tTau TTau pTau tTheta TTheta pTheta
        kF Yf 0 lM Ym 0 tc Yc 0 ∧
      (factorTwoScales.C s.card delta tm.card tau : ENNReal)
        ≤ (((C0 * factorTwoScales.C s.card delta tm.card tau : NNReal) : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-p.ε') := by
  classical
  have hthetaPos : 0 < theta := lt_of_lt_of_le (lt_of_lt_of_le hdelta0 hdeltaTau) htauTheta
  obtain ⟨tm, htm, Ztau, Zf, htmne, hmassTau, hZtauTube, hZfTube, hprodFine⟩ :=
    exists_oneScaleProductOnly hdim hdelta0 hdeltaTau (htauTheta.trans htheta1)
      T TTau pTau hball hparentFine hmass
  have hparentMid : IsParentFamily tm (fun k => (Ztau k).toTube) tTheta TTheta pTheta := by
    refine ⟨?_, hparentCoarse.injOn, ?_⟩
    · intro k hk
      exact hparentCoarse.mapsTo k (htm hk)
    · intro k hk
      rw [hZtauTube k hk]
      exact hparentCoarse.le_parent k (htm hk)
  have hballMid : ∀ k ∈ tm, (Ztau k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk
    change (Ztau k).toTube.carrier ⊆ Metric.closedBall 0 1
    rw [hZtauTube k hk]
    exact hballTau k (htm hk)
  obtain ⟨tc, htc, Zc, Zm, htcne, hmassTheta, hZcTube, hZmTube, hprodMid⟩ :=
    exists_oneScaleProductOnly hdim (lt_of_lt_of_le hdelta0 hdeltaTau) htauTheta htheta1
      Ztau TTheta pTheta hballMid hparentMid hmassTau
  obtain ⟨kF, hkFtm⟩ := htmne
  obtain ⟨lM, hlMtc⟩ := htcne
  have hmuS : 0 < ShadedBody.multiplicity s (fun i => (T i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div]
    exact ENNReal.div_pos hmass.ne' (ShadedBody.volume_iUnion_shade_ne_top _ _)
  have hmuTau : 0 < ShadedBody.multiplicity tm (fun k => (Ztau k).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div]
    exact ENNReal.div_pos hmassTau.ne' (ShadedBody.volume_iUnion_shade_ne_top _ _)
  have hfineFiltered :
      (fibre (s.filter fun i => pTau i ∈ tm) pTau kF).Nonempty := by
    by_contra hne
    have hzero : fibre (s.filter fun i => pTau i ∈ tm) pTau kF = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hle : ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤ 0 := by
      simpa [hzero] using hprodFine kF hkFtm
    exact (not_le_of_gt hmuS) hle
  have hmidFiltered :
      (fibre (tm.filter fun k => pTheta k ∈ tc) pTheta lM).Nonempty := by
    by_contra hne
    have hzero : fibre (tm.filter fun k => pTheta k ∈ tc) pTheta lM = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hle : ShadedBody.multiplicity tm (fun k => (Ztau k).toShadedBody) ≤ 0 := by
      simpa [hzero] using hprodMid lM hlMtc
    exact (not_le_of_gt hmuTau) hle
  have hfineEq : fibre (s.filter fun i => pTau i ∈ tm) pTau kF = fibre s pTau kF :=
    fibre_filter_mem s pTau tm hkFtm
  have hmidEq : fibre (tm.filter fun k => pTheta k ∈ tc) pTheta lM =
      fibre tm pTheta lM := fibre_filter_mem tm pTheta tc hlMtc
  have hfineNonempty : (fibre s pTau kF).Nonempty := by
    rw [← hfineEq]
    exact hfineFiltered
  have hmidNonempty : (fibre tm pTheta lM).Nonempty := by
    rw [← hmidEq]
    exact hmidFiltered
  let sm : Finset κ := fibre (tm.filter fun k => pTheta k ∈ tc) pTheta lM
  have hsmSub : sm ⊆ fibre tTau pTheta lM := by
    intro k hk
    have hk' : k ∈ tm.filter (fun j => pTheta j ∈ tc) ∧ pTheta k = lM := by
      simpa [sm, fibre, Finset.mem_filter] using hk
    exact Finset.mem_filter.mpr ⟨htm (Finset.mem_filter.mp hk'.1).1, hk'.2⟩
  have hZmActiveTube : ∀ k ∈ sm, (Zm k).toTube = TTau k := by
    intro k hk
    have hk' : k ∈ tm ∧ pTheta k = lM := by
      have := (Finset.mem_filter.mp hk)
      exact ⟨(Finset.mem_filter.mp this.1).1, this.2⟩
    have hpk : pTheta k ∈ tc := by simpa [hk'.2] using hlMtc
    rw [hZmTube k hk'.1 hpk, hZtauTube k hk'.1]
  let YmAmbient : κ → ShadedTube tau E := zeroExtend sm TTau Zm
  have hYmTube : ∀ k, (YmAmbient k).toTube = TTau k := by
    intro k
    exact zeroExtend_toTube hZmActiveTube k
  have hYmMult :
      ShadedBody.multiplicity (fibre tTau pTheta lM)
          (fun k => (YmAmbient k).toShadedBody) =
        ShadedBody.multiplicity sm (fun k => (Zm k).toShadedBody) := by
    exact multiplicity_zeroExtend_of_subset hsmSub TTau Zm
  have hYmMult' :
      ShadedBody.multiplicity (fibre tm pTheta lM)
          (fun k => (Zm k).toShadedBody) =
        ShadedBody.multiplicity (fibre tTau pTheta lM)
          (fun k => (YmAmbient k).toShadedBody) := by
    calc
      ShadedBody.multiplicity (fibre tm pTheta lM)
          (fun k => (Zm k).toShadedBody) =
          ShadedBody.multiplicity sm (fun k => (Zm k).toShadedBody) := by
            rw [← hmidEq]
      _ = ShadedBody.multiplicity (fibre tTau pTheta lM)
          (fun k => (YmAmbient k).toShadedBody) := hYmMult.symm
  have htmFibSub : fibre tm pTheta lM ⊆ fibre tTau pTheta lM := by
    intro k hk
    have hk' : k ∈ tm ∧ pTheta k = lM := by
      simpa [fibre, Finset.mem_filter] using hk
    exact Finset.mem_filter.mpr ⟨htm hk'.1, hk'.2⟩
  have hmidAmbientNonempty : (fibre tTau pTheta lM).Nonempty :=
    hmidNonempty.mono htmFibSub
  have hproduct :
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤
        (factorTwoScales.C s.card delta tm.card tau : ENNReal) *
          ShadedBody.multiplicity (fibre s pTau kF)
            (fun i => (Zf i).toShadedBody) *
          ShadedBody.multiplicity (fibre tTau pTheta lM)
            (fun k => (YmAmbient k).toShadedBody) *
          ShadedBody.multiplicity tc (fun l => (Zc l).toShadedBody) := by
    calc
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ (factorOneScale.C s.card delta : ENNReal) *
              ShadedBody.multiplicity tm (fun k => (Ztau k).toShadedBody) *
              ShadedBody.multiplicity (fibre (s.filter fun i => pTau i ∈ tm) pTau kF)
                (fun i => (Zf i).toShadedBody) := hprodFine kF hkFtm
      _ ≤ (factorOneScale.C s.card delta : ENNReal) *
            ((factorOneScale.C tm.card tau : ENNReal) *
              ShadedBody.multiplicity tc (fun l => (Zc l).toShadedBody) *
              ShadedBody.multiplicity (fibre (tm.filter fun k => pTheta k ∈ tc) pTheta lM)
                (fun k => (Zm k).toShadedBody)) *
            ShadedBody.multiplicity (fibre (s.filter fun i => pTau i ∈ tm) pTau kF)
              (fun i => (Zf i).toShadedBody) := by
        exact mul_le_mul_right' (mul_le_mul_left' (hprodMid lM hlMtc) _) _
      _ = (factorTwoScales.C s.card delta tm.card tau : ENNReal) *
            ShadedBody.multiplicity (fibre s pTau kF)
              (fun i => (Zf i).toShadedBody) *
            ShadedBody.multiplicity (fibre tTau pTheta lM)
              (fun k => (YmAmbient k).toShadedBody) *
            ShadedBody.multiplicity tc (fun l => (Zc l).toShadedBody) := by
        rw [hfineEq, hmidEq, ← hYmMult', factorTwoScales.C, ENNReal.coe_mul]
        ring_nf
  let hfac : IsTwoScaleFactors
      (factorTwoScales.C s.card delta tm.card tau : ENNReal) Lcard
        s T tTau TTau pTau tTheta TTheta pTheta
        kF Zf 0 lM YmAmbient 0 tc Zc 0 :=
    { skeleton_fine := hparentFine.mapsTo
      skeleton_mid := hparentCoarse.mapsTo
      fine_mem := htm hkFtm
      fine_nonempty := hfineNonempty
      fine_tube := by
        intro i hi
        have hi' : i ∈ s ∧ pTau i = kF := by
          simpa [fibre, Finset.mem_filter] using hi
        exact hZfTube i hi'.1 (by simpa [hi'.2] using hkFtm)
      fine_fullness := bot_le
      mid_mem := htc hlMtc
      mid_nonempty := hmidAmbientNonempty
      mid_tube := by
        intro k hk
        exact hYmTube k
      mid_fullness := bot_le
      coarse_subset := htc
      coarse_nonempty := ⟨lM, hlMtc⟩
      coarse_tube := hZcTube
      coarse_fullness := bot_le
      branch_card := hbranch
      product := hproduct }
  refine ⟨tm, tc, kF, lM, Zf, YmAmbient, Zc,
    ⟨kF, hkFtm⟩, ⟨lM, hlMtc⟩, htm, htc, hfac, ?_⟩
  exact factorTwoScales_C_le_exact hp
    (hdeltaTau.trans (htauTheta.trans htheta1)) C0 hC0 s.card tm.card

end AmbientProducer

/-! ### Fine-endpoint ambient producer

The ambient transport loss disappears completely if the first factoring scale is chosen at
the endpoint `tau = delta`.  The first parent family is then the ambient family itself along
`id`.  Its selected fine fibre is a singleton.  At the second scale, choose among the active
coarse outputs a parent with minimal *ambient* fibre.  Fibrewise counting then gives
`#middle * #coarse <= #s`, so the full branch count costs only `1` (and hence any `Cu^4` with
`1 <= Cu`).  This is the endpoint case singled out by the capacity ledger, and it never runs a
producer on the retained family `s'`.
-/

section FineEndpoint

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {ι : Type u} [DecidableEq ι]

/-- A pairwise essentially distinct positive-radius tube family is its own parent family. -/
theorem isParentFamily_self_of_pairwiseEssentiallyDistinct
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {s : Finset ι} (T : ι -> ShadedTube delta E)
    (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)) :
    IsParentFamily s (fun i => (T i).toTube) s (fun i => (T i).toTube) id := by
  classical
  refine { mapsTo := ?_, injOn := ?_, le_parent := ?_ }
  · intro i hi
    simpa using hi
  · intro i hi j hj hbody
    by_contra hij
    have hed := hED hi hj hij
    change IsEssentiallyDistinct (T i).carrier (T j).carrier at hed
    have hcarrier : (T i).carrier = (T j).carrier :=
      congrArg (fun K : ConvexSpaceBody E => K.carrier) hbody
    rw [hcarrier] at hed
    have hvol := Tube.volume_pos_and_lt_top hdelta0 hdelta1 (T j).toTube
    exact (not_isEssentiallyDistinct_self hvol.1.ne' hvol.2.ne) hed
  · intro i hi
    exact le_rfl

/-- Product-only B3 directly on the ambient family at the endpoint `tau = delta`.

The theorem returns the exact `IsTwoScaleFactors` and loss fields consumed by
`AnalyticEndgameW27`.  Its branch budget is `Cu^4`, but the proof establishes the sharper
constant-one count.  In particular there is no `s' -> s` multiplicity bridge and no
`delta^(-(eta+7))` loss. -/
theorem exists_ambient_fineEndpoint_twoScaleFactors_productOnly_with_loss
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta theta : NNReal} (hdelta0 : 0 < delta) (hdeltaTheta : delta <= theta)
    (htheta1 : theta <= 1)
    {s : Finset ι} (T : ι -> ShadedTube delta E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (hmass : 0 < ∑ i ∈ s, volume (T i).shade)
    (C0 Cu : NNReal) (hC0 : 1 <= C0) (hCu : 1 <= Cu) :
    ∃ (tm tTheta tc : Finset ι) (TTheta : ι -> Tube theta E) (pTheta : ι -> ι)
      (kF lM : ι) (Yf Ym : ι -> ShadedTube delta E)
      (Yc : ι -> ShadedTube theta E),
      tm.Nonempty ∧ tc.Nonempty ∧ tm ⊆ s ∧ tc ⊆ tTheta ∧
      IsParentFamily s (fun i => (T i).toTube) tTheta TTheta pTheta ∧
      IsTwoScaleFactors
        (factorTwoScales.C s.card delta tm.card delta : ENNReal)
        ((Cu : ENNReal) ^ 4)
        s T s (fun i => (T i).toTube) id tTheta TTheta pTheta
        kF Yf 0 lM Ym 0 tc Yc 0 ∧
      (factorTwoScales.C s.card delta tm.card delta : ENNReal)
        <= (((C0 * factorTwoScales.C s.card delta tm.card delta : NNReal) : ENNReal)) *
          (delta : ENNReal) ^ (-p.ε') := by
  classical
  have hdelta1 : delta <= 1 := hdeltaTheta.trans htheta1
  have hparentSelf :
      IsParentFamily s (fun i => (T i).toTube) s (fun i => (T i).toTube) id :=
    isParentFamily_self_of_pairwiseEssentiallyDistinct hdelta0 hdelta1 T hED
  obtain ⟨tTheta, TTheta, pTheta, htThetaSub, hparentTheta, _hsurj, _hballTheta⟩ :=
    exists_parentFamily hdelta0 hdeltaTheta htheta1 (fun i => (T i).toTube) hball
  obtain ⟨tm, htm, Zm0, Zf, htmne, hmassTm, hZm0Tube, hZfTube, hprodFine⟩ :=
    exists_oneScaleProductOnly hdim hdelta0 le_rfl hdelta1
      T (fun i => (T i).toTube) id hball hparentSelf hmass
  have hparentTm :
      IsParentFamily tm (fun i => (Zm0 i).toTube) tTheta TTheta pTheta := by
    refine { mapsTo := ?_, injOn := hparentTheta.injOn, le_parent := ?_ }
    · intro i hi
      exact hparentTheta.mapsTo i (htm hi)
    · intro i hi
      rw [hZm0Tube i hi]
      exact hparentTheta.le_parent i (htm hi)
  have hballTm : ∀ i ∈ tm, (Zm0 i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    rw [hZm0Tube i hi]
    exact hball i (htm hi)
  obtain ⟨tc, htc, Zc, Zm0', htcne, _hmassTc, hZcTube, hZm0'Tube, hprodMid⟩ :=
    exists_oneScaleProductOnly hdim hdelta0 hdeltaTheta htheta1
      Zm0 TTheta pTheta hballTm hparentTm hmassTm
  obtain ⟨kF, hkFtm⟩ := htmne
  obtain ⟨lM, hlMtc, hlMmin⟩ :=
    Finset.exists_min_image tc (fun l => (fibre s pTheta l).card) htcne
  have hkFs : kF ∈ s := htm hkFtm
  have hsumAll : s.card = ∑ l ∈ tTheta, (fibre s pTheta l).card := by
    simpa [fibre] using
      (Finset.card_eq_sum_card_fiberwise (s := s) (f := pTheta) (t := tTheta)
        (H := hparentTheta.mapsTo))
  have hsumTc : (∑ l ∈ tc, (fibre s pTheta l).card) <= s.card := by
    calc
      (∑ l ∈ tc, (fibre s pTheta l).card)
          <= ∑ l ∈ tTheta, (fibre s pTheta l).card :=
        Finset.sum_le_sum_of_subset htc
      _ = s.card := hsumAll.symm
  have hminCount : (fibre s pTheta lM).card * tc.card <= s.card := by
    calc
      (fibre s pTheta lM).card * tc.card =
          ∑ _l ∈ tc, (fibre s pTheta lM).card := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp [Nat.mul_comm]
      _ <= ∑ l ∈ tc, (fibre s pTheta l).card := by
        exact Finset.sum_le_sum (fun l hl => hlMmin l hl)
      _ <= s.card := hsumTc
  have hfineFiltered :
      (fibre (s.filter fun i => id i ∈ tm) id kF).Nonempty := by
    have hmuS : 0 < ShadedBody.multiplicity s (fun i => (T i).toShadedBody) := by
      rw [ShadedBody.multiplicity_eq_div]
      exact ENNReal.div_pos hmass.ne' (ShadedBody.volume_iUnion_shade_ne_top _ _)
    by_contra hne
    have hzero : fibre (s.filter fun i => id i ∈ tm) id kF = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hle : ShadedBody.multiplicity s (fun i => (T i).toShadedBody) <= 0 := by
      calc
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody) <=
            (factorOneScale.C s.card delta : ENNReal) *
              ShadedBody.multiplicity tm (fun i => (Zm0 i).toShadedBody) *
              ShadedBody.multiplicity (fibre (s.filter fun i => id i ∈ tm) id kF)
                (fun i => (Zf i).toShadedBody) := hprodFine kF hkFtm
        _ = 0 := by rw [hzero, ShadedBody.multiplicity_empty, mul_zero]
    exact (not_le_of_gt hmuS) hle
  have hmidFiltered :
      (fibre (tm.filter fun i => pTheta i ∈ tc) pTheta lM).Nonempty := by
    have hmuTm : 0 < ShadedBody.multiplicity tm (fun i => (Zm0 i).toShadedBody) := by
      rw [ShadedBody.multiplicity_eq_div]
      exact ENNReal.div_pos hmassTm.ne' (ShadedBody.volume_iUnion_shade_ne_top _ _)
    by_contra hne
    have hzero : fibre (tm.filter fun i => pTheta i ∈ tc) pTheta lM = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hle : ShadedBody.multiplicity tm (fun i => (Zm0 i).toShadedBody) <= 0 := by
      calc
        ShadedBody.multiplicity tm (fun i => (Zm0 i).toShadedBody) <=
            (factorOneScale.C tm.card delta : ENNReal) *
              ShadedBody.multiplicity tc (fun i => (Zc i).toShadedBody) *
              ShadedBody.multiplicity
                (fibre (tm.filter fun i => pTheta i ∈ tc) pTheta lM)
                (fun i => (Zm0' i).toShadedBody) := hprodMid lM hlMtc
        _ = 0 := by rw [hzero, ShadedBody.multiplicity_empty, mul_zero]
    exact (not_le_of_gt hmuTm) hle
  have hfineEq : fibre (s.filter fun i => id i ∈ tm) id kF = fibre s id kF :=
    fibre_filter_mem s id tm hkFtm
  have hfineSingleton : fibre s id kF = {kF} := by
    ext i
    simp only [fibre, Finset.mem_filter, id_eq, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro h
      subst i
      exact ⟨hkFs, rfl⟩
  let sm : Finset ι := fibre (tm.filter fun i => pTheta i ∈ tc) pTheta lM
  have hsmSub : sm ⊆ fibre s pTheta lM := by
    intro i hi
    have hi' : i ∈ tm.filter (fun j => pTheta j ∈ tc) ∧ pTheta i = lM := by
      simpa [sm, fibre, Finset.mem_filter] using hi
    exact Finset.mem_filter.mpr ⟨htm (Finset.mem_filter.mp hi'.1).1, hi'.2⟩
  have hZmActiveTube : ∀ i ∈ sm, (Zm0' i).toTube = (T i).toTube := by
    intro i hi
    have hi' : i ∈ tm ∧ pTheta i ∈ tc := by
      have hfilter := (Finset.mem_filter.mp hi).1
      exact ⟨(Finset.mem_filter.mp hfilter).1, (Finset.mem_filter.mp hfilter).2⟩
    rw [hZm0'Tube i hi'.1 hi'.2, hZm0Tube i hi'.1]
  let Ym : ι -> ShadedTube delta E := zeroExtend sm (fun i => (T i).toTube) Zm0'
  have hYmTube : ∀ i, (Ym i).toTube = (T i).toTube := by
    intro i
    exact zeroExtend_toTube hZmActiveTube i
  have hYmMult :
      ShadedBody.multiplicity (fibre s pTheta lM)
          (fun i => (Ym i).toShadedBody) =
        ShadedBody.multiplicity sm (fun i => (Zm0' i).toShadedBody) :=
    multiplicity_zeroExtend_of_subset hsmSub (fun i => (T i).toTube) Zm0'
  have hmidNonempty : (fibre s pTheta lM).Nonempty := hmidFiltered.mono hsmSub
  have hfineNonempty : (fibre s id kF).Nonempty := by
    rw [← hfineEq]
    exact hfineFiltered
  have hproduct :
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody) <=
        (factorTwoScales.C s.card delta tm.card delta : ENNReal) *
          ShadedBody.multiplicity (fibre s id kF) (fun i => (Zf i).toShadedBody) *
          ShadedBody.multiplicity (fibre s pTheta lM) (fun i => (Ym i).toShadedBody) *
          ShadedBody.multiplicity tc (fun i => (Zc i).toShadedBody) := by
    calc
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          <= (factorOneScale.C s.card delta : ENNReal) *
              ShadedBody.multiplicity tm (fun i => (Zm0 i).toShadedBody) *
              ShadedBody.multiplicity (fibre (s.filter fun i => id i ∈ tm) id kF)
                (fun i => (Zf i).toShadedBody) := hprodFine kF hkFtm
      _ <= (factorOneScale.C s.card delta : ENNReal) *
            ((factorOneScale.C tm.card delta : ENNReal) *
              ShadedBody.multiplicity tc (fun i => (Zc i).toShadedBody) *
              ShadedBody.multiplicity
                (fibre (tm.filter fun i => pTheta i ∈ tc) pTheta lM)
                (fun i => (Zm0' i).toShadedBody)) *
            ShadedBody.multiplicity (fibre (s.filter fun i => id i ∈ tm) id kF)
              (fun i => (Zf i).toShadedBody) := by
        exact mul_le_mul_right' (mul_le_mul_left' (hprodMid lM hlMtc) _) _
      _ = (factorTwoScales.C s.card delta tm.card delta : ENNReal) *
            ShadedBody.multiplicity (fibre s id kF) (fun i => (Zf i).toShadedBody) *
            ShadedBody.multiplicity (fibre s pTheta lM) (fun i => (Ym i).toShadedBody) *
            ShadedBody.multiplicity tc (fun i => (Zc i).toShadedBody) := by
        rw [hfineEq, hYmMult, factorTwoScales.C, ENNReal.coe_mul]
        ring
  have hbranch :
      ((fibre s id kF).card : ENNReal) *
          ((fibre s pTheta lM).card : ENNReal) * (tc.card : ENNReal)
        <= (Cu : ENNReal) ^ 4 * (s.card : ENNReal) := by
    have hminCountE :
        ((fibre s pTheta lM).card : ENNReal) * (tc.card : ENNReal) <=
          (s.card : ENNReal) := by
      exact_mod_cast hminCount
    have hCuE : (1 : ENNReal) <= (Cu : ENNReal) := by exact_mod_cast hCu
    rw [hfineSingleton, Finset.card_singleton, Nat.cast_one, one_mul]
    calc
      ((fibre s pTheta lM).card : ENNReal) * (tc.card : ENNReal)
          <= (s.card : ENNReal) := hminCountE
      _ = 1 * (s.card : ENNReal) := by rw [one_mul]
      _ <= (Cu : ENNReal) ^ 4 * (s.card : ENNReal) := by
        gcongr
        exact one_le_pow₀ hCuE
  have hfac : IsTwoScaleFactors
      (factorTwoScales.C s.card delta tm.card delta : ENNReal)
      ((Cu : ENNReal) ^ 4)
      s T s (fun i => (T i).toTube) id tTheta TTheta pTheta
      kF Zf 0 lM Ym 0 tc Zc 0 :=
    { skeleton_fine := fun i hi => by simpa using hi
      skeleton_mid := hparentTheta.mapsTo
      fine_mem := hkFs
      fine_nonempty := hfineNonempty
      fine_tube := by
        intro i hi
        have hi' : i ∈ s ∧ id i = kF := by
          simpa [fibre, Finset.mem_filter] using hi
        have hi_eq : i = kF := by simpa only [id_eq] using hi'.2
        subst i
        exact hZfTube kF hi'.1 (by simpa using hkFtm)
      fine_fullness := bot_le
      mid_mem := htc hlMtc
      mid_nonempty := hmidNonempty
      mid_tube := fun i _ => hYmTube i
      mid_fullness := bot_le
      coarse_subset := htc
      coarse_nonempty := htcne
      coarse_tube := hZcTube
      coarse_fullness := bot_le
      branch_card := hbranch
      product := hproduct }
  refine ⟨tm, tTheta, tc, TTheta, pTheta, kF, lM, Zf, Ym, Zc,
    ⟨kF, hkFtm⟩, htcne, htm, htc, hparentTheta, hfac, ?_⟩
  exact factorTwoScales_C_le_exact hp hdelta1 C0 hC0 s.card tm.card

/-! ### Raw CaseTwo adapter

The endpoint producer needs positive ambient shade mass.  The raw CaseTwo hereditary-fullness
clause gives this already: take a singleton in the nonempty retained family `s₂`, use positivity
of the tube volume, and then enlarge the finite sum to `s`. -/

theorem ambient_shade_mass_pos_of_hereditary_fullness
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {s s₂ : Finset ι} (T : ι -> ShadedTube delta E)
    (hs₂s : s₂ ⊆ s) (hs₂ne : s₂.Nonempty) (eta : Real)
    (hhered : ∀ t ⊆ s₂, t.Nonempty ->
      (delta : ENNReal) ^ eta <=
        (ShadedBody.fullness t (fun i => (T i).toShadedBody) : ENNReal)) :
    0 < ∑ i ∈ s, volume (T i).shade := by
  obtain ⟨i, hi⟩ := hs₂ne
  have hsingle := hhered ({i} : Finset ι)
    (Finset.singleton_subset_iff.mpr hi) (by simp)
  have hpow : (0 : ENNReal) < (delta : ENNReal) ^ eta := by
    rw [ennreal_coe_nnreal_rpow (by exact_mod_cast hdelta0)]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hdelta0) _)
  have hfullpos : (0 : ENNReal) < ShadedBody.fullness ({i} : Finset ι)
      (fun j => (T j).toShadedBody) := lt_of_lt_of_le hpow hsingle
  have hvol := Tube.volume_pos_and_lt_top hdelta0 hdelta1 (T i).toTube
  have hmassSingle : 0 < ∑ j ∈ ({i} : Finset ι), volume (T j).shade := by
    change 0 < ∑ j ∈ ({i} : Finset ι), volume ((T j).toShadedBody).shade
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul]
    have hcarrier : 0 < ∑ j ∈ ({i} : Finset ι),
        volume ((T j).toShadedBody).carrier := by
      simpa using hvol.1
    exact ENNReal.mul_pos hfullpos.ne' hcarrier.ne'
  have hmono : (∑ j ∈ ({i} : Finset ι), volume (T j).shade) <=
      ∑ j ∈ s, volume (T j).shade :=
    Finset.sum_le_sum_of_subset (s := ({i} : Finset ι))
      (Finset.singleton_subset_iff.mpr (hs₂s hi))
  exact lt_of_lt_of_le hmassSingle hmono

/-- The ambient endpoint producer in the literal raw CaseTwo context.

The first scale is `delta`; the coarse scale is the block's coarse endpoint
`gridScale delta (ssfGridLen delta) a`.  Hence the scalar loss is read on `s.card`, with no
retained-to-ambient transport factor.  The parent family at the coarse endpoint is constructed
by `exists_parentFamily`; this theorem does not identify it with `U.cover.assign a`. -/
theorem exists_caseTwo_ambient_fineEndpoint_productOnly_with_loss
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {s s₂ s' : Finset ι} (T : ι -> ShadedTube delta E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (hs₂s : s₂ ⊆ s) (hs₂ne : s₂.Nonempty) (hs's₂ : s' ⊆ s₂)
    (hhered : ∀ t ⊆ s₂, t.Nonempty ->
      (delta : ENNReal) ^ p.η 0 <=
        (ShadedBody.fullness t (fun i => (T i).toShadedBody) : ENNReal))
    (_hFrost : ConvexSpaceBody.frostmanConstant s₂
        (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      ENNReal.ofReal ((delta : Real) ^ (-p.η 0)))
    (Cd : NNReal) (Kd cd : Nat) (hCd1 : 1 <= Cd)
    (hcard : (s₂.card : ENNReal) <=
      StickyKakeya.totalLoss Cd Kd cd delta * (s'.card : ENNReal))
    (U : Tube.UniformTubeSet s' (fun i => (T i).toTube)
      (Tube.ssfGridLen delta) Cd)
    (_hNice : U.Nice) (a b m : Nat)
    (hblock : StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
      p.η p.ε a b m p.N)
    (C0 : NNReal) (hC0 : 1 <= C0) :
    s'.Nonempty ∧ s' ⊆ s ∧
    ∃ (tm tTheta tc : Finset ι)
      (TTheta : ι -> Tube (Tube.gridScale delta (Tube.ssfGridLen delta) a) E)
      (pTheta : ι -> ι) (kF lM : ι)
      (Yf Ym : ι -> ShadedTube delta E)
      (Yc : ι -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) a) E),
      tm.Nonempty ∧ tc.Nonempty ∧ tm ⊆ s ∧ tc ⊆ tTheta ∧
      IsParentFamily s (fun i => (T i).toTube) tTheta TTheta pTheta ∧
      IsTwoScaleFactors
        (factorTwoScales.C s.card delta tm.card delta : ENNReal)
        ((((Cd ^ 2 : NNReal) : ENNReal)) ^ 4)
        s T s (fun i => (T i).toTube) id tTheta TTheta pTheta
        kF Yf 0 lM Ym 0 tc Yc 0 ∧
      (factorTwoScales.C s.card delta tm.card delta : ENNReal) <=
        (((C0 * factorTwoScales.C s.card delta tm.card delta : NNReal) : ENNReal)) *
          (delta : ENNReal) ^ (-p.ε') := by
  have hs'ne : s'.Nonempty := by
    by_contra hs'
    rw [Finset.not_nonempty_iff_eq_empty] at hs'
    rw [hs'] at hcard
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hcard
    have hs₂pos : (0 : ENNReal) < (s₂.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr hs₂ne
    exact (not_le_of_gt hs₂pos) hcard
  have hmass : 0 < ∑ i ∈ s, volume (T i).shade :=
    ambient_shade_mass_pos_of_hereditary_fullness hdelta0 hdelta1 T
      hs₂s hs₂ne (p.η 0) hhered
  have hgrid := gridScale_block_bracket hdelta0 hdelta1
    hblock.coarse_lt_fine hblock.fine_le
  refine ⟨hs'ne, hs's₂.trans hs₂s, ?_⟩
  exact exists_ambient_fineEndpoint_twoScaleFactors_productOnly_with_loss
    (E := E) (theta := Tube.gridScale delta (Tube.ssfGridLen delta) a)
    hdim hp hdelta0 (hgrid.1.trans hgrid.2.1) hgrid.2.2 T hball hED hmass
      C0 (Cd ^ 2) hC0 (one_le_pow₀ hCd1)

/-- Exact eventual structural-and-loss payload for the live certificate callback.

All fields through the loss comparison are constructed from the raw CaseTwo prefix.  The only
field intentionally not returned is `AnalyticEndgameW27.IsTwoScaleAnalyticBounds`.
In particular, `Nmid` is the selected ambient intermediate cardinality and both standard
dimension-three cardinality bounds are included. -/
theorem eventually_exists_caseTwo_ambient_fineEndpoint_exact_loss_certificate
    (hdim : Module.finrank ℝ E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    (Cd : NNReal) (Kd cd : Nat) (hCd1 : 1 <= Cd)
    (C0 : NNReal) (hC0 : 1 <= C0) :
    ∀ᶠ (delta : NNReal) in 𝓝[>] 0,
      ∀ {κ : Type u} [DecidableEq κ] (s s₂ s' : Finset κ)
        (T : κ -> ShadedTube delta E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ->
        (s : Set κ).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ->
        s₂ ⊆ s -> s₂.Nonempty -> s' ⊆ s₂ ->
        (∀ t ⊆ s₂, t.Nonempty ->
          (delta : ENNReal) ^ p.η 0 <=
            (ShadedBody.fullness t (fun i => (T i).toShadedBody) : ENNReal)) ->
        ConvexSpaceBody.frostmanConstant s₂
            (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          ENNReal.ofReal ((delta : Real) ^ (-p.η 0)) ->
        (s₂.card : ENNReal) <=
          StickyKakeya.totalLoss Cd Kd cd delta * (s'.card : ENNReal) ->
        ∀ (U : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen delta) Cd), U.Nice ->
        ∀ a b m : Nat,
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
          ∃ (tau theta : NNReal) (Ttau : κ -> Tube tau E) (ptau : κ -> κ)
            (Ttheta : κ -> Tube theta E) (ptheta : κ -> κ)
            (tTauAmb tThetaAmb tThetaAct : Finset κ) (kF lM : κ)
            (Yf : κ -> ShadedTube delta E) (Ym : κ -> ShadedTube tau E)
            (Yc : κ -> ShadedTube theta E) (Lfact : ENNReal) (Nmid : Nat)
            (lamF lamM lamC : NNReal),
            delta <= tau ∧ tau <= theta ∧ theta <= 1 ∧
            0 < s.card ∧ 0 < Nmid ∧
            (s.card : Real) <= (delta : Real) ^ (-(7 : Real)) ∧
            (Nmid : Real) <= (delta : Real) ^ (-(7 : Real)) ∧
            IsTwoScaleFactors Lfact ((((Cd ^ 2 : NNReal) : ENNReal)) ^ 4)
              s T tTauAmb Ttau ptau tThetaAmb Ttheta ptheta
              kF Yf lamF lM Ym lamM tThetaAct Yc lamC ∧
            Lfact <=
              (((C0 * factorTwoScales.C s.card delta Nmid tau : NNReal) : ENNReal)) *
                (delta : ENNReal) ^ (-p.ε') := by
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
    eventually_le_one_nhdsGT, self_mem_nhdsWithin] with
    delta hpack hdelta1 hdelta0
  intro κ _ s s₂ s' T hball hED hs₂s hs₂ne hs's₂ hhered hFrost
    hcard U hNice a b m hblock
  obtain ⟨_hs'ne, _hs's, tm, tTheta, tc, TTheta, pTheta, kF, lM,
      Yf, Ym, Yc, htmne, _htcne, _htm, _htc, _hparent, hfactor, hloss⟩ :=
    exists_caseTwo_ambient_fineEndpoint_productOnly_with_loss
      (E := E) hdim hp hdelta0 hdelta1 T hball hED hs₂s hs₂ne hs's₂ hhered
        hFrost Cd Kd cd hCd1 hcard U hNice a b m hblock C0 hC0
  have hgrid := gridScale_block_bracket hdelta0 hdelta1
    hblock.coarse_lt_fine hblock.fine_le
  have hcardS : (s.card : Real) <= (delta : Real) ^ (-(7 : Real)) :=
    hpack delta le_rfl s (fun i => (T i).toTube) hball hED
  have hcardMid : (tm.card : Real) <= (delta : Real) ^ (-(7 : Real)) := by
    have hsub : (tm.card : Real) <= (s.card : Real) := by
      exact_mod_cast Finset.card_le_card _htm
    exact hsub.trans hcardS
  refine ⟨delta, Tube.gridScale delta (Tube.ssfGridLen delta) a,
    (fun i => (T i).toTube), id, TTheta, pTheta, s, tTheta, tc, kF, lM,
    Yf, Ym, Yc,
    (factorTwoScales.C s.card delta tm.card delta : ENNReal), tm.card,
    0, 0, 0, le_rfl, hgrid.1.trans hgrid.2.1, hgrid.2.2,
    Finset.card_pos.mpr (hs₂ne.mono hs₂s), Finset.card_pos.mpr htmne,
    hcardS, hcardMid, hfactor, hloss⟩

end FineEndpoint

#print axioms Kakeya.ml1Boot.productOnly_ambient_loss_le_exact
#print axioms Kakeya.ml1Boot.exists_C0_productOnly_ambient_loss_le_exact
#print axioms Kakeya.ml1Boot.factorTwoScales_C_le_exact
#print axioms Kakeya.ml1Boot.exists_ambient_twoScaleFactors_productOnly_with_loss
#print axioms Kakeya.ml1Boot.isParentFamily_self_of_pairwiseEssentiallyDistinct
#print axioms Kakeya.ml1Boot.exists_ambient_fineEndpoint_twoScaleFactors_productOnly_with_loss
#print axioms Kakeya.ml1Boot.ambient_shade_mass_pos_of_hereditary_fullness
#print axioms Kakeya.ml1Boot.exists_caseTwo_ambient_fineEndpoint_productOnly_with_loss
#print axioms Kakeya.ml1Boot.eventually_exists_caseTwo_ambient_fineEndpoint_exact_loss_certificate

end Kakeya.ml1Boot

end
