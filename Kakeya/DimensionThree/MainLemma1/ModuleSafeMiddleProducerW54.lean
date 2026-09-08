module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddleFrostmanW50
public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddlePaymentsW50
public import Kakeya.DimensionThree.MainLemma1.RawMiddleBlockModuleW51

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W54ModuleSafeMiddleProducer

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- A global retained share localizes to the actual selected middle fibre. -/
theorem selected_middle_fibre_share_of_global_w54
    {iota : Type u} [DecidableEq iota]
    {source sm tc : Finset iota} {pTheta : iota -> iota} {lM : iota}
    {r : ENNReal}
    (hmaps : ∀ k ∈ sm, pTheta k ∈ tc)
    (hband : ∀ l ∈ tc, ∀ l' ∈ tc,
      ((fibre sm pTheta l).card : ENNReal) <=
        2 * ((fibre sm pTheta l').card : ENNReal))
    (hlM : lM ∈ tc)
    (hglobal : r * (source.card : ENNReal) <= (sm.card : ENNReal)) :
    (r * (2 * (tc.card : ENNReal))⁻¹) * (source.card : ENNReal) <=
      ((fibre sm pTheta lM).card : ENNReal) := by
  classical
  let selected : ENNReal := ((fibre sm pTheta lM).card : ENNReal)
  let D : ENNReal := 2 * (tc.card : ENNReal)
  have hsum : (sm.card : ENNReal) =
      ∑ l ∈ tc, ((fibre sm pTheta l).card : ENNReal) := by
    have hnat : sm.card = ∑ l ∈ tc, (fibre sm pTheta l).card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hmaps
    exact_mod_cast hnat
  have hupper : (sm.card : ENNReal) <= D * selected := by
    rw [hsum]
    calc
      (∑ l ∈ tc, ((fibre sm pTheta l).card : ENNReal)) <=
          ∑ _l ∈ tc, 2 * selected := by
            exact Finset.sum_le_sum fun l hl => by
              simpa [selected] using hband l hl lM hlM
      _ = D * selected := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp only [D]
        ring
  have htc0 : (tc.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨lM, hlM⟩
  have hD0 : D ≠ 0 := by
    exact mul_ne_zero (by norm_num) htc0
  have hDtop : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top tc.card)
  calc
    (r * (2 * (tc.card : ENNReal))⁻¹) * (source.card : ENNReal) =
        D⁻¹ * (r * (source.card : ENNReal)) := by
          simp only [D]
          ring
    _ <= D⁻¹ * (sm.card : ENNReal) := by gcongr
    _ <= D⁻¹ * (D * selected) := by gcongr
    _ = selected := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]

/-- Simultaneously translating the family and ambient body preserves the
Frostman constant.  This proof uses only the module-safe Frostman API. -/
theorem frostmanConstIn_translate_w54
    {iota : Type u} {s : Finset iota} {W : iota -> ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (v0 : E) :
    frostmanConstIn s (fun i => ConvexSpaceBody.translate (W i) v0)
      (ConvexSpaceBody.translate K v0) = frostmanConstIn s W K := by
  apply le_antisymm
  · apply frostmanConstIn_le
    exact (isFrostmanIn_frostmanConstIn s W K).translate v0
  · apply frostmanConstIn_le
    have h := (isFrostmanIn_frostmanConstIn s
      (fun i => ConvexSpaceBody.translate (W i) v0)
      (ConvexSpaceBody.translate K v0)).translate (-v0)
    simpa [ConvexSpaceBody.neg_translate_cancel] using h

/-- The module-safe counted packet inherits the dividing-block Frostman bound
on its actual selected and translated middle fibre. -/
theorem middle_frostman_of_counted_global_share_upstream_w54 [Nontrivial E]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} (T : iota -> ShadedTube delta E)
    {N a b : Nat} {C : NNReal} (hC : 1 <= C)
    (U : Tube.UniformTubeSet s (fun i => (T i).toTube) N C) (hb : b <= N)
    {tTau tTheta : Finset iota} {pTau pTheta repTau : iota -> iota}
    (htTau : tTau ⊆ U.cover.indexSet b)
    (hpTauRep : ∀ i ∈ s, pTau i = repTau (U.cover.assign b i))
    (hrepTau : ∀ j ∈ U.cover.indexSet b,
      repTau j ∈ tTau /\
        (U.cover.tube b (repTau j)).toConvexSpaceBody =
          (U.cover.tube b j).toConvexSpaceBody)
    (hparent : IsParentFamily tTau (U.cover.tube b)
      tTheta (U.cover.tube a) pTheta)
    {M : Nat} (hM : 0 < M) {tm sf : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N b) E}
    {Zf : iota -> ShadedTube delta E} {uCell : Finset iota} {v0 : E}
    {tc sm : Finset iota}
    {Zc : iota -> ShadedTube (Tube.gridScale delta N a) E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N b) E} {kF lM : iota}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hfulls : 0 < ShadedBody.fullness s (fun i => (T i).toShadedBody))
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 s T
      tTau (U.cover.tube b) pTau tTheta (U.cover.tube a) pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM)
    {A : ENNReal}
    (hraw : frostmanConstIn
        (familyIn (U.cover.indexSet b)
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a lM).toConvexSpaceBody)
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a lM).toConvexSpaceBody <= A) :
    frostmanConstIn (fibre sm pTheta lM)
        (fun k => (Zm k).toConvexSpaceBody)
        ((U.cover.tube a lM).translate v0).toConvexSpaceBody <=
      (((((((factorOneScale.C uCell.card (Tube.gridScale delta N b))⁻¹ : NNReal) :
              ENNReal) * (4 * (M : ENNReal))⁻¹) *
            ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)) *
          ((C : ENNReal) ^ 3)⁻¹ *
          ((((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
            ShadedBody.fullness s (fun i => (T i).toShadedBody))) *
        (2 * (tc.card : ENNReal))⁻¹)⁻¹ * A := by
  classical
  let source : Finset iota :=
    familyIn (U.cover.indexSet b)
      (fun k => (U.cover.tube b k).toConvexSpaceBody)
      (U.cover.tube a lM).toConvexSpaceBody
  let selected : Finset iota := fibre sm pTheta lM
  let r : ENNReal :=
    (((((factorOneScale.C uCell.card (Tube.gridScale delta N b))⁻¹ : NNReal) :
          ENNReal) * (4 * (M : ENNReal))⁻¹) *
        ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)) *
      ((C : ENNReal) ^ 3)⁻¹ *
      ((((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
        ShadedBody.fullness s (fun i => (T i).toShadedBody))
  let D : ENNReal := 2 * (tc.card : ENNReal)
  have hglobal : r * ((U.cover.indexSet b).card : ENNReal) <=
      (sm.card : ENNReal) := by
    simpa [r, mul_assoc] using
      W50UpstreamMiddleFrostman.middle_fixed_global_card_share_upstream_w50
        hdelta0 hdelta1 T hC U hb htTau hpTauRep hrepTau hM hfac
  have hsourceSub : source ⊆ U.cover.indexSet b := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hglobalSource : r * (source.card : ENNReal) <=
      (sm.card : ENNReal) := by
    calc
      r * (source.card : ENNReal) <=
          r * ((U.cover.indexSet b).card : ENNReal) := by
            gcongr
      _ <= (sm.card : ENNReal) := hglobal
  have hshare := selected_middle_fibre_share_of_global_w54
    (source := source) hfac.middle_maps hfac.middle_card_band
    hfac.middle_mem hglobalSource
  have hcFine : 0 < (factorOneScale.C s.card delta)⁻¹ :=
    inv_pos.mpr (zero_lt_one.trans_le (one_le_factorOneScale_C s.card delta))
  have hfulltm : 0 < ShadedBody.fullness tm
      (fun k => (ZTau k).toShadedBody) :=
    (mul_pos hcFine hfulls).trans_le hfac.outer_fullness
  have hcMiddle : 0 <
      (factorOneScale.C uCell.card (Tube.gridScale delta N b))⁻¹ :=
    inv_pos.mpr (zero_lt_one.trans_le
      (one_le_factorOneScale_C uCell.card (Tube.gridScale delta N b)))
  have hr : r ≠ 0 := by
    dsimp [r]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · exact ENNReal.coe_ne_zero.mpr hcMiddle.ne'
    · exact ENNReal.inv_ne_zero.mpr
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top M))
    · exact ENNReal.coe_ne_zero.mpr hfulltm.ne'
    · exact ENNReal.inv_ne_zero.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact mul_ne_zero (ENNReal.coe_ne_zero.mpr hcFine.ne')
        (ENNReal.coe_ne_zero.mpr hfulls.ne')
  have hDtop : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top tc.card)
  have hkappa : r * D⁻¹ ≠ 0 :=
    mul_ne_zero hr (ENNReal.inv_ne_zero.mpr hDtop)
  have hshare' : (r * D⁻¹) * (source.card : ENNReal) <=
      (selected.card : ENNReal) := by
    simpa [D, selected] using hshare
  have hselectedSub : selected ⊆ source := by
    intro k hk
    have hk' : k ∈ sm /\ pTheta k = lM := by
      simpa [selected, fibre, Finset.mem_filter] using hk
    have hktau : k ∈ tTau :=
      hfac.mid_subset (hfac.cell_subset (hfac.middle_subset hk'.1))
    have hkb : k ∈ U.cover.indexSet b := htTau hktau
    have hle := hparent.le_parent k hktau
    rw [hk'.2] at hle
    exact Finset.mem_filter.mpr ⟨hkb, hle⟩
  have hsourceNe : source.Nonempty := by
    exact hfac.middle_nonempty.mono hselectedSub
  have hsourceNe' : source.Nonempty := hsourceNe
  obtain ⟨k0, hk0⟩ := hsourceNe
  have hvol : ∀ k ∈ source,
      volume (U.cover.tube b k).carrier =
        volume (U.cover.tube b k0).carrier := by
    intro k hk
    exact Tube.volume_carrier_eq_volume_carrier
      (U.cover.tube b k) (U.cover.tube b k0)
  have hWK : ∀ k ∈ source,
      (U.cover.tube b k).toConvexSpaceBody <=
        (U.cover.tube a lM).toConvexSpaceBody := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have htransport : frostmanConstIn selected
      (fun k => (U.cover.tube b k).toConvexSpaceBody)
      (U.cover.tube a lM).toConvexSpaceBody <= (r * D⁻¹)⁻¹ * A := by
    calc
      frostmanConstIn selected
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a lM).toConvexSpaceBody <=
          (r * D⁻¹)⁻¹ * frostmanConstIn source
            (fun k => (U.cover.tube b k).toConvexSpaceBody)
            (U.cover.tube a lM).toConvexSpaceBody := by
        exact ConvexSpaceBody.frostmanConstIn_subfamily_le
          hsourceNe' hvol hWK hselectedSub hkappa hshare'
      _ <= (r * D⁻¹)⁻¹ * A := by
        exact mul_le_mul_left' (by simpa [source] using hraw) _
  have hbody : ∀ k ∈ selected,
      (Zm k).toConvexSpaceBody =
        ConvexSpaceBody.translate
          (U.cover.tube b k).toConvexSpaceBody v0 := by
    intro k hk
    exact congrArg
      (fun W : Tube (Tube.gridScale delta N b) E => W.toConvexSpaceBody)
      (hfac.middle_tube k)
  rw [frostmanConstIn_congr selected hbody
    ((U.cover.tube a lM).translate v0).toConvexSpaceBody]
  rw [show ((U.cover.tube a lM).translate v0).toConvexSpaceBody =
      ConvexSpaceBody.translate (U.cover.tube a lM).toConvexSpaceBody v0 from rfl]
  rw [frostmanConstIn_translate_w54]
  simpa [r, D, mul_assoc] using htransport

/-- The raw dividing-block producer and the module-safe middle transport joined
on exactly the same counted factor witness.  Besides the producer fields, the
result retains both the selected-fibre Frostman estimate and the literal
fullness lower bound needed by a downstream WZ call. -/
theorem exists_counted_raw_middle_fields_module_safe_w54 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gamma0 : Real} {p : Params} (hspec : p.Spec beta gamma0)
    (Cd : NNReal) (hCd : 1 <= Cd) (Kd cd : Nat) :
    ∃ M : Nat, 0 < M /\
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {iota : Type u} [DecidableEq iota]
          (s s2 sPrime : Finset iota) (V : iota -> ShadedTube delta E)
          (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
            (Tube.ssfGridLen delta) Cd)
          (a b m : Nat),
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) ->
          s2 ⊆ s -> sPrime ⊆ s2 -> sPrime.Nonempty ->
          (∀ t ⊆ s2, t.Nonempty ->
            (delta : ENNReal) ^ p.η 0 <=
              (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) ->
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
          ∃ (tTau tTheta : Finset iota)
            (pTau pTheta repTau repTheta pTheta0 : iota -> iota)
            (tm sf : Finset iota)
            (ZTau : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) b) E)
            (Zf : iota -> ShadedTube delta E)
            (uCell : Finset iota) (v0 : E) (tc sm : Finset iota)
            (Zc : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) a) E)
            (Zm : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) b) E)
            (kF lM : iota),
            tTau ⊆ U.cover.indexSet b /\
            tTheta ⊆ U.cover.indexSet a /\
            (∀ i, pTau i ∈ tTau) /\
            (∀ k, pTheta k ∈ tTheta) /\
            (∀ i ∈ sPrime,
              pTau i = repTau (U.cover.assign b i)) /\
            (∀ j ∈ U.cover.indexSet b,
              repTau j ∈ tTau /\
                (U.cover.tube b (repTau j)).toConvexSpaceBody =
                  (U.cover.tube b j).toConvexSpaceBody) /\
            (∀ j' ∈ tTau,
              ∃ j ∈ U.cover.indexSet b, repTau j = j') /\
            (∀ i ∈ sPrime,
              (U.cover.tube b (pTau i)).toConvexSpaceBody =
                (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody) /\
            (∀ i ∈ sPrime,
              pTheta0 (U.cover.assign b i) = U.cover.assign a i) /\
            (∀ k ∈ U.cover.indexSet b,
              pTheta0 k ∈ U.cover.indexSet a) /\
            (∀ k ∈ U.cover.indexSet b,
              (U.cover.tube b k).toConvexSpaceBody <=
                (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) /\
            (∀ k ∈ tTau, pTheta k = repTheta (pTheta0 k)) /\
            (∀ l ∈ U.cover.indexSet a,
              repTheta l ∈ tTheta /\
                (U.cover.tube a (repTheta l)).toConvexSpaceBody =
                  (U.cover.tube a l).toConvexSpaceBody) /\
            (∀ l' ∈ tTheta,
              ∃ l ∈ U.cover.indexSet a, repTheta l = l') /\
            (∀ k ∈ tTau,
              (U.cover.tube a (pTheta k)).toConvexSpaceBody =
                (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) /\
            IsParentFamily sPrime (fun i => (V i).toTube)
              tTau (U.cover.tube b) pTau /\
            IsParentFamily tTau (U.cover.tube b)
              tTheta (U.cover.tube a) pTheta /\
            W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 sPrime V
              tTau (U.cover.tube b) pTau
              tTheta (U.cover.tube a) pTheta
              M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM /\
            (frostmanConstIn (fibre sm pTheta lM)
                (fun k => (Zm k).toConvexSpaceBody)
                ((U.cover.tube a lM).translate v0).toConvexSpaceBody <=
              ((((((((factorOneScale.C uCell.card
                    (Tube.gridScale delta (Tube.ssfGridLen delta) b))⁻¹ : NNReal) :
                  ENNReal) * (4 * (M : ENNReal))⁻¹) *
                ShadedBody.fullness tm
                  (fun k => (ZTau k).toShadedBody)) *
              ((Cd : ENNReal) ^ 3)⁻¹ *
                ((((factorOneScale.C sPrime.card delta)⁻¹ : NNReal) : ENNReal) *
                  ShadedBody.fullness sPrime
                    (fun i => (V i).toShadedBody))) *
            (2 * (tc.card : ENNReal))⁻¹)⁻¹ *
            ((delta : ENNReal) ^ (-p.ε) *
              ((Tube.gridScale delta (Tube.ssfGridLen delta) a /
                Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : ENNReal) ^
                p.η m)) /\
            (((factorOneScale.C uCell.card
                  (Tube.gridScale delta (Tube.ssfGridLen delta) b))⁻¹ : NNReal) :
                ENNReal) *
                (((1 / 2 : NNReal) : ENNReal) *
                  ((((factorOneScale.C sPrime.card delta)⁻¹ : NNReal) : ENNReal) *
                    ShadedBody.fullness sPrime
                      (fun i => (V i).toShadedBody))) <=
              ShadedBody.fullness (fibre sm pTheta lM)
                (fun k => (Zm k).toShadedBody)) := by
  obtain ⟨M, hM, hproducer⟩ :=
    W50Upstream.exists_caseTwoDirectFactors_counted_raw_block_upstream_w50
      (E := E) hdim hspec Cd Kd cd
  refine ⟨M, hM, ?_⟩
  filter_upwards [hproducer,
      W51RawMiddleBlock.caseTwoRawMid_of_block_upstream_w51
        (E := E) (p := p) hspec.epsPos Cd Kd cd,
      self_mem_nhdsWithin, eventually_le_one_nhdsGT]
    with delta hproducerDelta hrawDelta hdelta0 hdelta1
  intro iota _ s s2 sPrime V U a b m hball hs2s hsPrimeSub hsPrimeNe
    hhered hblock
  obtain ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
      tm, sf, ZTau, Zf, uCell, v0, tc, sm, Zc, Zm, kF, lM,
      htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
      hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
      hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta,
      hfac⟩ :=
    hproducerDelta s s2 sPrime V U a b m hball hs2s hsPrimeSub
      hsPrimeNe hhered hblock
  have hfullLower : (delta : ENNReal) ^ p.η 0 <=
      (ShadedBody.fullness sPrime
        (fun i => (V i).toShadedBody) : ENNReal) :=
    hhered sPrime hsPrimeSub hsPrimeNe
  have hdeltaPow : 0 < (delta : ENNReal) ^ p.η 0 :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta0) ENNReal.coe_ne_top
  have hfullPrime : 0 < ShadedBody.fullness sPrime
      (fun i => (V i).toShadedBody) :=
    ENNReal.coe_pos.mp (lt_of_lt_of_le hdeltaPow hfullLower)
  have hlM : lM ∈ U.cover.indexSet a :=
    htTheta (hfac.coarse_subset hfac.middle_mem)
  have hrawLm := hrawDelta V U a b m hblock lM hlM
  have hmiddle := middle_frostman_of_counted_global_share_upstream_w54
    V hCd U hblock.fine_le htTau hpTauRep hrepTau hparentTheta
    hM hdelta0 hdelta1 hfullPrime hfac hrawLm
  have hfullness :=
    W50UpstreamMiddlePayments.middle_factor_fullness_upstream_w50 hfac
  exact ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
    tm, sf, ZTau, Zf, uCell, v0, tc, sm, Zc, Zm, kF, lM,
    htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
    hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
    hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta,
    hfac, hmiddle, hfullness⟩

end
end Kakeya.ml1Boot.W54ModuleSafeMiddleProducer

end

#print axioms Kakeya.ml1Boot.W54ModuleSafeMiddleProducer.middle_frostman_of_counted_global_share_upstream_w54
#print axioms Kakeya.ml1Boot.W54ModuleSafeMiddleProducer.exists_counted_raw_middle_fields_module_safe_w54
