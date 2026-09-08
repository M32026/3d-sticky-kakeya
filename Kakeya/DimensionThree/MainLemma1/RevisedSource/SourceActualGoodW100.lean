module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalTransportW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceSameMassFullnessW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionRawCutsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionArrayW97
public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseBallPrefix
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95

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

/-- The actual fixed-polylog selection and its SAME old-coarse fullness
fund the two outer KF applications. Input exponents are chosen before delta. -/
theorem actual_polylog_eligible_good_implies_source_good_w98
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (gamma : Real) (hgammaZero : gammaZero <= gamma) (hgamma : gamma <= 1)
    (Ctw Ccell BF Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell) (hBF : 1 <= BF)
    (Cselect : NNReal) (Kselect : Nat) (hCselect : 1 <= Cselect) (hKselect : 1 <= Kselect)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (Cgood : NNReal) (eFull eCF : Real) (delta0 : NNReal),
      1 <= Cgood ∧ 0 < eFull ∧ eFull < p.η 0 / 100 ∧
      0 < eCF ∧ eCF < p.η 0 / 100 ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty -> (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (delta : ENNReal) ^ eFull <= fullness' A (fun i => (Y i).toShadedBody) ->
        frostmanConstIn A (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (delta : ENNReal) ^ (-eCF) ->
      ∀ (block : ActualSourceDividingBlockW95 U p BF)
        (selections : ActualSameMassSelectionsW95 block loss)
        (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
        (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
          Rnorm Cext Cnorm CtwNorm CcellNorm aux),
        (loss : ENNReal) <= (towerPreparationRetainedW95 delta Cselect Kselect)⁻¹ ->
        ((loss : ENNReal) ^ (14 : Nat))⁻¹ *
            (fullness' A (fun i => (Y i).toShadedBody)) ^ (4 : Nat) <=
          fullness' (U.cover.indexSet block.a.val)
            (fun R => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
              selections.coarseShading R).toShadedBody) ->
      ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
        detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
          (calls.normalization R hR).normalized gamma p.ε (xi block.label) ->
        ShadedBody.multiplicity A (fun i => (Y i).toShadedBody) <=
          (Cgood : ENNReal) * (delta : ENNReal) ^ (18 * xiMin) * (delta : ENNReal) ^ (-2 * gamma) *
            ((delta : ENNReal) ^ (2 : Nat) * (A.card : ENNReal)) ^ (1 - gamma / 2) := by
  have hmassBandPaid {iota : Type uI} {delta : NNReal} (hd : 0 < delta)
      (F : Finset iota) (V : iota -> ShadedTube delta E)
      (K : ConvexSpaceBody E) (hK : ∀ i ∈ F, (V i).toConvexSpaceBody <= K)
      (hmass : 0 < ∑ i ∈ F, volume (V i).shade) :
      ∃ G : Finset iota, G ⊆ F ∧ ∃ lam : NNReal, 0 < lam ∧ G.Nonempty ∧
        (∀ i ∈ G, (lam : ENNReal) * volume (V i).carrier <= volume (V i).shade ∧
          volume (V i).shade <= 2 * (lam : ENNReal) * volume (V i).carrier) ∧
        fullness' F (fun i => (V i).toShadedBody) <=
          bandLoss F.card * fullness' G (fun i => (V i).toShadedBody) ∧
        (fullness' F (fun i => (V i).toShadedBody) / bandLoss F.card) *
          (F.card : ENNReal) <= (G.card : ENNReal) ∧
        frostmanConstIn G (fun i => (V i).toConvexSpaceBody) K <=
          (fullness' F (fun i => (V i).toShadedBody) / bandLoss F.card)⁻¹ *
            frostmanConstIn F (fun i => (V i).toConvexSpaceBody) K ∧
        ShadedBody.multiplicity F (fun i => (V i).toShadedBody) <=
          bandLoss F.card * ShadedBody.multiplicity G (fun i => (V i).toShadedBody) := by
    classical
    obtain ⟨G, hGF, lam, hlam, hG, hdensity, hretain, _⟩ := exists_massBand hd F V hmass
    have hF : F.Nonempty := hG.mono hGF
    obtain ⟨i0, hi0⟩ := hF
    let v := volume (V i0).carrier
    have hvpos : 0 < v := by
      apply lt_of_lt_of_le _ (V i0).toTube.le_volume
      exact ENNReal.mul_pos (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)).ne'
        (pow_ne_zero _ (ENNReal.coe_pos.mpr hd).ne')
    have hvtop : v ≠ ⊤ := (V i0).toTube.isCompact.measure_ne_top
    have hvol (i : iota) : volume (V i).carrier = v :=
      Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i0).toTube
    have hsum (H : Finset iota) : (∑ i ∈ H, volume (V i).carrier) = (H.card : ENNReal) * v := by
      simp only [hvol, Finset.sum_const, nsmul_eq_mul]
    have hdenpos : (0 : ENNReal) < (F.card : ENNReal) * v :=
      ENNReal.mul_pos (by exact_mod_cast (Finset.card_ne_zero.mpr ⟨i0, hi0⟩)) hvpos.ne'
    have hdentop : (F.card : ENNReal) * v ≠ ⊤ := by finiteness
    have hfullpos : 0 < fullness' F (fun i => (V i).toShadedBody) := by
      unfold fullness'
      rw [hsum]
      exact ENNReal.div_pos hmass.ne' hdentop
    have hJtop : bandLoss F.card ≠ ⊤ := by unfold bandLoss; finiteness
    have hJpos : 0 < bandLoss F.card := by
      by_contra hn
      have hzero : bandLoss F.card = 0 := le_antisymm (not_lt.mp hn) bot_le
      rw [hzero, zero_mul] at hretain
      exact (not_lt_of_ge hretain) hmass
    have hfull : fullness' F (fun i => (V i).toShadedBody) <=
        bandLoss F.card * fullness' G (fun i => (V i).toShadedBody) := by
      unfold fullness'
      rw [← mul_div_assoc]
      exact ENNReal.div_le_div hretain (Finset.sum_le_sum_of_subset hGF)
    have hcard : (fullness' F (fun i => (V i).toShadedBody) / bandLoss F.card) *
        (F.card : ENNReal) <= (G.card : ENNReal) := by
      apply (ENNReal.mul_le_mul_iff_left hvpos.ne' hvtop).mp
      calc
        (fullness' F (fun i => (V i).toShadedBody) / bandLoss F.card * (F.card : ENNReal)) * v =
            (fullness' F (fun i => (V i).toShadedBody) * ((F.card : ENNReal) * v)) / bandLoss F.card := by
          simp only [div_eq_mul_inv]
          ring
        _ = (∑ i ∈ F, volume (V i).shade) / bandLoss F.card := by
          unfold fullness'
          rw [hsum, ENNReal.div_mul_cancel hdenpos.ne' hdentop]
        _ <= ∑ i ∈ G, volume (V i).shade := by
          apply (ENNReal.div_le_iff hJpos.ne' hJtop).mpr
          simpa only [mul_comm] using hretain
        _ <= (G.card : ENNReal) * v := by
          rw [← hsum]
          exact Finset.sum_le_sum (fun i hi => measure_mono (V i).shade_subset)
    refine ⟨G, hGF, lam, hlam, hG, hdensity, hfull, hcard, ?_, ?_⟩
    · exact frostmanConstIn_subfamily_le ⟨i0, hi0⟩ (fun i hi => hvol i) hK hGF
        (ENNReal.div_pos hfullpos.ne' hJtop).ne' hcard
    · apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset F
        (fun i => (V i).toShadedBody) G (fun i => (V i).toShadedBody) (bandLoss F.card) _ hretain
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨i, hGF hi, hxi⟩
  have hcoarseAmbientCF {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (hd : 0 < delta) {A : Finset iota} {Y : iota -> ShadedTube delta E}
      {Ccan Ctw Ccell : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (hA : A.Nonempty) (hball : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (C : ENNReal)
      (hCF : frostmanConstIn A (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <= C)
      (k : Nat) (hk : k < M) :
      let K2 : ConvexSpaceBody E := ConvexSpaceBody.closedBall 0 2 (by norm_num)
      frostmanConstIn (U.cover.indexSet k) (fun R => (U.cover.tube k R).toConvexSpaceBody) K2 <=
        2 * (volume K2.carrier / volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier) * C := by
    let K2 : ConvexSpaceBody E := ConvexSpaceBody.closedBall 0 2 (by norm_num)
    have hB1 (i : iota) (hi : i ∈ A) :
        (Y i).toConvexSpaceBody <= ConvexSpaceBody.closedUnitBall := hball i hi
    have hB2 (i : iota) (hi : i ∈ A) : (Y i).toConvexSpaceBody <= K2 :=
      (hball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
    have hK2pos : volume K2.carrier ≠ 0 :=
      (Metric.measure_closedBall_pos volume (0 : E) (by norm_num : (0 : Real) < 2)).ne'
    have hFr := (isFrostmanIn_of_frostmanConstIn_le hCF).change_ambient
      hB1 hB2 ConvexSpaceBody.closedUnitBall_volume_pos.ne' hK2pos
    obtain ⟨i0, hi0⟩ := hA
    let v := volume (Y i0).carrier
    let R0 := U.cover.assign k i0
    have hR0 : R0 ∈ U.cover.indexSet k := U.cover.assign_mem k hk.le i0 hi0
    let w := volume (U.cover.tube k R0).carrier
    have hvol (i : iota) : volume (Y i).carrier = v :=
      Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
    have hparentVol (R : iota) : volume (U.cover.tube k R).carrier = w :=
      Tube.volume_carrier_eq_volume_carrier (U.cover.tube k R) (U.cover.tube k R0)
    have hfibreBottom (R : iota) : actualDescendantsW95 A U.cover.assign k M R =
        completeFibreW94 A (U.cover.assign k) R := by
      unfold actualDescendantsW95
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        rwa [reg.bottom_assign j (Finset.mem_filter.mp hj).1]
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, reg.bottom_assign i (Finset.mem_filter.mp hi).1⟩
    have hfibreNonempty (R : iota) (hR : R ∈ U.cover.indexSet k) :
        (completeFibreW94 A (U.cover.assign k) R).Nonempty := by
      rw [← reg.surjective k hk.le] at hR
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
    have hdensity (R : iota) :
        Kakeya.densityIn (completeFibreW94 A (U.cover.assign k) R)
          (fun i => (Y i).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody =
        ((completeFibreW94 A (U.cover.assign k) R).card : ENNReal) * v / w := by
      rw [Kakeya.densityIn_of_all_le]
      · simp only [hvol, hparentVol, Finset.sum_const, nsmul_eq_mul]
      · intro i hi
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        simpa only [hiR] using U.cover.le_tube_assign k hk.le i hiA
    have hparents : IsFrostmanIn (U.cover.indexSet k)
        (fun R => (U.cover.tube k R).toConvexSpaceBody) K2
        (2 * (C * (volume K2.carrier / volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier))) := by
      apply ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres hFr
        (fib := completeFibreW94 A (U.cover.assign k))
      · intro i hi
        apply lt_of_lt_of_le _ (Y i).toTube.le_volume
        exact ENNReal.mul_pos (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)).ne'
          (pow_ne_zero _ (ENNReal.coe_pos.mpr hd).ne')
      · exact U.cover.assign_mem k hk.le
      · exact U.cover.le_tube_assign k hk.le
      · exact reg.parent_ball k hk.le
      · intro R
        rfl
      · exact hfibreNonempty
      · intro R hR R' hR'
        have hcard : ((completeFibreW94 A (U.cover.assign k) R).card : ENNReal) <=
            2 * ((completeFibreW94 A (U.cover.assign k) R').card : ENNReal) := by
          have h := (reg.count_upper k M hk le_rfl R hR).le.trans
            (mul_le_mul' le_rfl (reg.count_lower k M hk le_rfl R' hR'))
          simp only [hfibreBottom] at h
          exact_mod_cast h
        rw [hdensity, hdensity, ← mul_div_assoc]
        exact ENNReal.div_le_div_right (by simpa only [mul_assoc] using mul_le_mul' hcard (le_rfl : v <= v)) _
    simpa only [mul_left_comm, mul_assoc, mul_comm] using frostmanConstIn_le hparents
  have hfineDilateInput {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (k : Nat) (hk : k <= M) (R : iota) (hR : R ∈ U.cover.indexSet k)
      (G : Finset iota) (V : iota -> ShadedTube delta E)
      (hG : G.Nonempty) (hGF : G ⊆ completeFibreW94 A (U.cover.assign k) R)
      (htube : ∀ i ∈ G, (V i).toTube = (Y i).toTube)
      (hED : (G : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier))
      (lam : NNReal) (hlam : 0 < lam)
      (hdensity : ∀ i ∈ G, (lam : ENNReal) * volume (V i).carrier <= volume (V i).shade ∧
        volume (V i).shade <= 2 * (lam : ENNReal) * volume (V i).carrier)
      (eta : Real)
      (hfull : 4 * (fineNormalizeDilate.C 1 : ENNReal) * (delta : ENNReal) ^ eta <=
        fullness' G (fun i => (V i).toShadedBody)) :
      IsFineFibreDilate 1 2 (U.cover.tube k R).toConvexSpaceBody 1 2 (lam : ENNReal)
        eta G (U.cover.tube k R) V := by
    have hdilate : Tube.dilate (U.cover.tube k R) (1 : Real) = (U.cover.tube k R).toConvexSpaceBody := by
      apply ConvexSpaceBody.ext
      change (Tube.dilate (U.cover.tube k R) (1 : Real)).carrier = (U.cover.tube k R).carrier
      rw [Tube.dilate_carrier]
      simp
    refine
      { density_pos := ENNReal.coe_pos.mpr hlam
        nonempty := hG
        parent_ball := reg.parent_ball k hk R hR
        ambient_le_parent_dilate := by simp only [NNReal.coe_one, hdilate, le_refl]
        ambient_fat := by simp only [NNReal.coe_one, hdilate, ENNReal.coe_one, one_mul, le_refl]
        subset_ambient := ?_
        essDistinct := hED
        shade_comparable := ?_
        fullness := ?_ }
    · intro i hi
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp (hGF hi)
      change (V i).toTube.toConvexSpaceBody <= _
      rw [htube i hi]
      simpa only [hiR] using U.cover.le_tube_assign k hk i hiA
    · intro i hi
      refine ⟨?_, (hdensity i hi).2⟩
      apply le_trans _ (hdensity i hi).1
      have hhalf : (2 : ENNReal)⁻¹ <= 1 := ENNReal.inv_le_one.mpr (by norm_num)
      simpa only [ENNReal.coe_ofNat, one_mul] using
        mul_le_mul' (mul_le_mul' hhalf (le_rfl : (lam : ENNReal) <= lam))
          (le_rfl : volume (V i).carrier <= volume (V i).carrier)
    · simp only [ENNReal.coe_one, ENNReal.coe_ofNat, ShadedBody.coe_fullness,
        show (2 : ENNReal) ^ (2 : Nat) = 4 by norm_num]
      rw [mul_comm (fineNormalizeDilate.C 1 : ENNReal) 4]
      exact hfull
  have hfineKFActual (epsKF : Real) (hepsKF : 0 < epsKF) :
      ∃ eta : Real, 0 < eta ∧
        Filter.Eventually (fun delta : NNReal => ∀ Cf : ENNReal, 1 <= Cf -> Cf ≠ ⊤ ->
          ∀ {iota : Type uI} [DecidableEq iota]
            {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell : NNReal}
            (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
            (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
            (k : Nat), k <= M -> delta <= Tube.gridScale delta M k -> Tube.gridScale delta M k <= 1 ->
          ∀ (R : iota), R ∈ U.cover.indexSet k ->
          ∀ (G : Finset iota) (V : iota -> ShadedTube delta E), G.Nonempty ->
            G ⊆ completeFibreW94 A (U.cover.assign k) R ->
            (∀ i ∈ G, (V i).toTube = (Y i).toTube) ->
            (G : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ->
          ∀ lam : NNReal, 0 < lam ->
            (∀ i ∈ G, (lam : ENNReal) * volume (V i).carrier <= volume (V i).shade ∧
              volume (V i).shade <= 2 * (lam : ENNReal) * volume (V i).carrier) ->
            4 * (fineNormalizeDilate.C 1 : ENNReal) * (delta : ENNReal) ^ eta <=
              fullness' G (fun i => (V i).toShadedBody) ->
            frostmanConstIn G (fun i => (V i).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody <=
              Cf / (fineNormalizeDilate.C 1 : ENNReal) ->
            ShadedBody.multiplicity G (fun i => (V i).toShadedBody) <=
              4 * (fineNormalizeDilate.C 1 : ENNReal) * (delta : ENNReal) ^ (-epsKF) *
                Cf ^ (1 - gamma / 2) *
                ((delta / Tube.gridScale delta M k : NNReal) : ENNReal) ^ (-2 * gamma) *
                ((G.card : ENNReal) * ((delta / Tube.gridScale delta M k : NNReal) : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2)) (nhdsWithin 0 (Set.Ioi 0)) := by
    obtain ⟨eta, heta, hKFeta⟩ := fine_genKF_dilate hdim 1
      ((hp.beta_pos.trans hp.gammaZero_gt).le.trans hgammaZero) hgamma hKF epsKF hepsKF
    refine ⟨eta, heta, ?_⟩
    filter_upwards [hKFeta 2 (by norm_num)] with delta hdeltaKF
    intro Cf hCf hCftop iota inst A Y Ccan Ctw Ccell U reg k hk hdt ht1 R hR G V hG hGF
      htube hED lam hlam hdensity hfull hCF
    have hfibre := hfineDilateInput U reg k hk R hR G V hG hGF htube hED lam hlam hdensity eta hfull
    have h := hdeltaKF Cf hCf hCftop (Tube.gridScale delta M k) hdt ht1
      (U.cover.tube k R) V (U.cover.tube k R).toConvexSpaceBody 1 (by norm_num) hfibre
      (by simpa only [ENNReal.coe_one, one_mul] using hCF)
    change (ShadedBody.multiplicity G fun i => (V i).toShadedBody) <= _ at h
    simpa only [ENNReal.coe_ofNat, show (2 : ENNReal) ^ (2 : Nat) = 4 by norm_num,
      mul_comm (fineNormalizeDilate.C 1 : ENNReal) 4] using h
  have hlineEDTransfer {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (F G : Finset iota) (T V : iota -> Tube delta E) (C : NNReal)
      (hGF : G ⊆ F) (hcar : ∀ i ∈ G, (V i).carrier = (T i).carrier)
      (hline : lineEssentiallyDistinctW94 F T C) : lineEssentiallyDistinctW94 G V C := by
    intro o v hv
    have hsub : G.filter (fun i => liesInFiveDeltaLineTubeW94 (V i) o v) ⊆
        F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v) := by
      intro i hi
      obtain ⟨hiG, hpred⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hGF hiG, ?_⟩
      unfold liesInFiveDeltaLineTubeW94 at hpred ⊢
      rwa [hcar i hiG] at hpred
    exact (show ((G.filter (fun i => liesInFiveDeltaLineTubeW94 (V i) o v)).card : NNReal) <=
      ((F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v)).card : NNReal) by
        exact_mod_cast Finset.card_le_card hsub).trans (hline o v hv)
  have hbottomLine {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell) :
      lineEssentiallyDistinctW94 A (fun i => (Y i).toTube) Ctw := by
    intro o v hv
    have h := reg.parent_line_ed M le_rfl o v hv
    rw [reg.bottom_index] at h
    have hfilter : A.filter (fun i => liesInFiveDeltaLineTubeW94 (U.cover.tube M i) o v) =
        A.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v) := by
      apply Finset.filter_congr
      intro i hi
      unfold liesInFiveDeltaLineTubeW94
      rw [congrArg ConvexSpaceBody.carrier (reg.bottom_tube i hi)]
      rw [Tube.gridScale_self delta hp.M_pos]
    rwa [hfilter] at h
  have hlineEDInputCard {Ctw : NNReal} {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (T : iota -> Tube delta E)
      (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
      (hline : lineEssentiallyDistinctW94 F T Ctw) :
      (F.card : Real) <= (5 : Real) ^ (6 : Nat) * (Ctw : Real) *
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
    have hfibrecard : ∀ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) <= Ctw := by
      intro j hj
      have hsub : F.filter (fun i => assign i = j) ⊆
          F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T j).midpoint (T j).direction) := by
        intro i hi
        obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hiF, hij ▸ hcluster i hiF⟩
      have hcap := hline (T j).midpoint (T j).direction (T j).norm_direction
      have hcapR : ((F.filter (fun i => liesInFiveDeltaLineTubeW94
          (T i) (T j).midpoint (T j).direction)).card : Real) <= Ctw := by exact_mod_cast hcap
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcapR
    have hcardFP : (F.card : Real) <= (P.card : Real) * Ctw := by
      calc
        (F.card : Real) = ∑ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to (fun i hi => (hass i hi).1) (fun _ => (1 : Real))).symm
        _ <= ∑ j ∈ P, (Ctw : Real) := Finset.sum_le_sum hfibrecard
        _ = (P.card : Real) * Ctw := by rw [Finset.sum_const, nsmul_eq_mul]
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
      (F.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) * Ctw :=
        hcardFP.trans (mul_le_mul_of_nonneg_right hcardP Ctw.coe_nonneg)
      _ = (5 : Real) ^ (6 : Nat) * (Ctw : Real) * (delta : Real) ^ (-(6 : Real)) := by
        rw [div_pow, Real.rpow_neg hd.le]
        norm_num only [Real.rpow_ofNat]
        ring
  have huniformBandPayment (Ctw : NNReal) (e : Real) (he : 0 < e) :
      Filter.Eventually (fun delta : NNReal =>
        ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (T : iota -> Tube delta E),
          (∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) ->
          lineEssentiallyDistinctW94 F T Ctw ->
          bandLoss F.card <= (delta : ENNReal) ^ (-e)) (nhdsWithin 0 (Set.Ioi 0)) := by
    let C : Real := (5 : Real) ^ (6 : Nat) * (Ctw : Real)
    filter_upwards [eventually_finite_const_le_rpow_neg (c := ENNReal.ofReal C)
      ENNReal.ofReal_ne_top (by norm_num : (0 : Real) < 1),
      eventually_bandLoss_le_rpow_neg he,
      eventually_le_nhdsGT (c := (1 : NNReal)) zero_lt_one,
      self_mem_nhdsWithin] with delta hconst hband hd1 hd
    intro iota inst F T hball hline
    apply hband F.card
    have hdR : (0 : Real) < delta := hd
    have hC : C <= (delta : Real) ^ (-1 : Real) := by
      have h := ENNReal.toReal_mono
        (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top) hconst
      simpa only [ENNReal.toReal_ofReal (show 0 <= C by dsimp [C]; positivity),
        ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using h
    calc
      (F.card : Real) <= C * (delta : Real) ^ (-6 : Real) :=
        hlineEDInputCard hd hd1 F T hball hline
      _ <= (delta : Real) ^ (-1 : Real) * (delta : Real) ^ (-6 : Real) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg delta.coe_nonneg _)
      _ = (delta : Real) ^ (-7 : Real) := by
        rw [← Real.rpow_add hdR]
        norm_num
  have hfineEndpoint {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (hd : 0 < delta) (hd1 : delta <= 1)
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell BF loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (block : ActualSourceDividingBlockW95 U p BF)
      (S : ActualSameMassSelectionsW95 block loss) (hb : block.b.val = M) :
      ShadedBody.multiplicity (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel)
        (fun i => (selectedShade S.fineFamily Y S.fineShading i).toShadedBody) <=
          (delta : ENNReal) ^ (-4 * p.η block.label.val) *
          ((delta / Tube.gridScale delta M block.b.val : NNReal) : ENNReal) ^ (-2 * gamma) *
          (((completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel).card : ENNReal) *
            ((delta / Tube.gridScale delta M block.b.val : NNReal) : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
    have hlabel : S.fineLabel ∈ A := by
      have h := S.first.parent_subset S.first.sel_mem
      rwa [hb, reg.bottom_index] at h
    have hfibre : completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel = {S.fineLabel} := by
      ext i
      simp only [completeFibreW94, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hi
        have hii := hi.2
        rwa [hb, reg.bottom_assign i hi.1] at hii
      · intro hi
        subst i
        exact ⟨hlabel, by rw [hb, reg.bottom_assign _ hlabel]⟩
    have hmult : ShadedBody.multiplicity
        (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel)
        (fun i => (selectedShade S.fineFamily Y S.fineShading i).toShadedBody) <= 1 := by
      simpa only [hfibre, Finset.card_singleton, Nat.cast_one] using
        ShadedBody.multiplicity_le_card
          (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel)
          (fun i => (selectedShade S.fineFamily Y S.fineShading i).toShadedBody)
    have hpow : (1 : ENNReal) <= (delta : ENNReal) ^ (-4 * p.η block.label.val) :=
      ENNReal.one_le_rpow_of_pos_of_le_one_of_neg (ENNReal.coe_pos.mpr hd)
        (by exact_mod_cast hd1) (by linarith [hp.zeta_pos block.label.val block.label_active.le])
    have hcardF : ((completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel).card : ENNReal) = 1 := by
      rw [hfibre]
      simp only [Finset.card_singleton, Nat.cast_one]
    rw [hcardF]
    simpa only [hb, Tube.gridScale_self delta hp.M_pos, div_self hd.ne', ENNReal.coe_one,
      ENNReal.one_rpow, Finset.card_singleton, Nat.cast_one, one_pow, one_mul, mul_one] using
      hmult.trans hpow
  have hcoarseEndpoint {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell BF loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell) (hA : A.Nonempty)
      (block : ActualSourceDividingBlockW95 U p BF)
      (S : ActualSameMassSelectionsW95 block loss) (ha : block.a.val = 0)
      (hpaid : (Ctw : ENNReal) <= (delta : ENNReal) ^ (-4 * p.η block.label.val)) :
      ShadedBody.multiplicity (U.cover.indexSet block.a.val)
        (fun R => (zeroExtend S.coarseFamily (U.cover.tube block.a.val) S.coarseShading R).toShadedBody) <=
          (delta : ENNReal) ^ (-4 * p.η block.label.val) *
          (Tube.gridScale delta M block.a.val : ENNReal) ^ (-2 * gamma) *
          (((U.cover.indexSet block.a.val).card : ENNReal) *
            (Tube.gridScale delta M block.a.val : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
    obtain ⟨i0, hi0⟩ := hA
    let R0 := U.cover.assign 0 i0
    have hR0 : R0 ∈ U.cover.indexSet 0 := U.cover.assign_mem 0 (Nat.zero_le _) i0 hi0
    let v := (U.cover.tube 0 R0).direction
    have hv : ‖v‖ = 1 := (U.cover.tube 0 R0).norm_direction
    have hfilter : (U.cover.indexSet 0).filter
        (fun R => liesInFiveDeltaLineTubeW94 (U.cover.tube 0 R) 0 v) = U.cover.indexSet 0 := by
      apply Finset.filter_eq_self.mpr
      intro R hR
      intro x hx
      refine ⟨0, ?_⟩
      have hx2 := Metric.mem_closedBall.mp (reg.parent_ball 0 (Nat.zero_le _) R hR hx)
      rw [Tube.gridScale_zero]
      simpa only [zero_smul, add_zero, NNReal.coe_one, mul_one] using
        hx2.trans (by norm_num : (2 : Real) <= 5)
    have hcard : ((U.cover.indexSet 0).card : NNReal) <= Ctw := by
      have h := reg.parent_line_ed 0 (Nat.zero_le _) (0 : E) v hv
      rwa [hfilter] at h
    have hmult : ShadedBody.multiplicity (U.cover.indexSet block.a.val)
        (fun R => (zeroExtend S.coarseFamily (U.cover.tube block.a.val) S.coarseShading R).toShadedBody) <=
          (delta : ENNReal) ^ (-4 * p.η block.label.val) := by
      apply (ShadedBody.multiplicity_le_card _ _).trans
      rw [ha]
      have hcardE : ((U.cover.indexSet 0).card : ENNReal) <= Ctw := by exact_mod_cast hcard
      exact hcardE.trans hpaid
    have hcardOne : (1 : ENNReal) <= (U.cover.indexSet 0).card := by
      exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨R0, hR0⟩)
    have hcardPow : (1 : ENNReal) <= ((U.cover.indexSet 0).card : ENNReal) ^ (1 - gamma / 2) := by
      simpa only [ENNReal.one_rpow] using
        ENNReal.rpow_le_rpow hcardOne (by linarith [hgamma] : 0 <= 1 - gamma / 2)
    simpa only [ha, Tube.gridScale_zero, ENNReal.coe_one, ENNReal.one_rpow,
      one_pow, mul_one] using hmult.trans (le_mul_of_one_le_right zero_le hcardPow)
  have hfineOriginalData {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell BF loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (block : ActualSourceDividingBlockW95 U p BF)
      (S : ActualSameMassSelectionsW95 block loss) (hb : block.b.val < M) :
      (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel).Nonempty ∧
      (∀ i ∈ completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel,
        (selectedShade S.fineFamily Y S.fineShading i).toConvexSpaceBody <=
          (U.cover.tube block.b.val S.fineLabel).toConvexSpaceBody) ∧
      frostmanConstIn (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel)
        (fun i => (selectedShade S.fineFamily Y S.fineShading i).toConvexSpaceBody)
        (U.cover.tube block.b.val S.fineLabel).toConvexSpaceBody <=
          (BF : ENNReal) ^ p.N *
            ((Tube.gridScale delta M block.b.val : ENNReal) / (delta : ENNReal)) ^
              p.η block.label.val := by
    have hlabel : S.fineLabel ∈ U.cover.indexSet block.b.val :=
      S.first.parent_subset S.first.sel_mem
    have htube (i : iota) : (selectedShade S.fineFamily Y S.fineShading i).toTube =
        (Y i).toTube := selectedShade_toTube S.fine_same_tube i
    refine ⟨?_, ?_, ?_⟩
    · rw [← reg.surjective block.b.val (by omega)] at hlabel
      obtain ⟨i, hi, hassign⟩ := Finset.mem_image.mp hlabel
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hassign⟩⟩
    · intro i hi
      obtain ⟨hiA, hassign⟩ := Finset.mem_filter.mp hi
      change (selectedShade S.fineFamily Y S.fineShading i).toTube.toConvexSpaceBody <= _
      rw [htube i, ← hassign]
      exact U.cover.le_tube_assign block.b.val (by omega) i hiA
    · rw [frostmanConstIn_congr _ (fun i _ => congrArg Tube.toConvexSpaceBody (htube i)) _]
      exact block.tail_upper hb S.fineLabel hlabel
  have hpowerReserve {delta : NNReal} (hd : 0 < delta) (e : Real)
      (loss : NNReal) (lambda : ENNReal)
      (hfull : (delta : ENNReal) ^ (2 * e) <= lambda)
      (hloss : (loss : ENNReal) <= (delta : ENNReal) ^ (-e)) (n k : Nat) :
      (delta : ENNReal) ^ (((n : Real) + 2 * (k : Real)) * e) <=
        ((loss : ENNReal) ^ n)⁻¹ * lambda ^ k := by
    have hd0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hd).ne'
    have hinv : (delta : ENNReal) ^ ((n : Real) * e) <= ((loss : ENNReal) ^ n)⁻¹ := by
      have h := ENNReal.inv_le_inv.mpr (pow_le_pow_left' hloss n)
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_neg] at h
      convert h using 1 <;> congr 1 <;> ring
    have hpow : (delta : ENNReal) ^ (2 * e * (k : Real)) <= lambda ^ k := by
      simpa only [ENNReal.rpow_mul, ENNReal.rpow_natCast] using pow_le_pow_left' hfull k
    calc
      (delta : ENNReal) ^ (((n : Real) + 2 * (k : Real)) * e) =
          (delta : ENNReal) ^ ((n : Real) * e) * (delta : ENNReal) ^ (2 * e * (k : Real)) := by
        rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1
        ring
      _ <= _ := mul_le_mul' hinv hpow
  have hpaidFullnessReserve {delta : NNReal} (hd : 0 < delta) (e a : Real)
      (L lambda lambdaPaid : ENNReal)
      (hL : L <= (delta : ENNReal) ^ (-e))
      (hlambda : (delta : ENNReal) ^ a <= lambda)
      (hpaid : lambda <= L * lambdaPaid) :
      (delta : ENNReal) ^ (a + e) <= lambdaPaid := by
    have hscale : (delta : ENNReal) ^ a <=
        (delta : ENNReal) ^ (-e) * lambdaPaid :=
      hlambda.trans (hpaid.trans (mul_le_mul' hL le_rfl))
    have hd0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hd).ne'
    apply (ENNReal.mul_le_mul_iff_right (a := (delta : ENNReal) ^ (-e))
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hd) ENNReal.coe_ne_top).ne'
      (ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top)).mp
    simpa only [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
      show -e + (a + e) = a by ring] using hscale
  have hnormalizationFullnessPayment {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      (C : ENNReal) (e a eta : Real)
      (hC : C <= (delta : ENNReal) ^ (-e)) (heta : a + e <= eta) :
      C * (delta : ENNReal) ^ eta <= (delta : ENNReal) ^ a := by
    calc
      C * (delta : ENNReal) ^ eta <=
          (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ eta := mul_le_mul' hC le_rfl
      _ = (delta : ENNReal) ^ (-e + eta) :=
        (ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top).symm
      _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) (by linarith)
  have hfineCFPayment {delta tau : NNReal} (hd : 0 < delta) (ht1 : tau <= 1)
      (e eta : Real) (heta : 0 <= eta) (Cfine MED J BFpower lambdaF : ENNReal)
      (hC : Cfine * BFpower <= (delta : ENNReal) ^ (-e))
      (hMED : MED <= (delta : ENNReal) ^ (-e))
      (hJ : J <= (delta : ENNReal) ^ (-e)) (hJtop : J ≠ ⊤)
      (hfull : (delta : ENNReal) ^ (4 * e) <= lambdaF) :
      Cfine * (MED * ((lambdaF / J)⁻¹ *
        (BFpower * ((tau : ENNReal) / (delta : ENNReal)) ^ eta))) <=
          (delta : ENNReal) ^ (-(eta + 7 * e)) := by
    have hd0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hd).ne'
    have hfull0 : lambdaF ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hd) ENNReal.coe_ne_top) hfull).ne'
    have hinv : lambdaF⁻¹ <= (delta : ENNReal) ^ (-4 * e) := by
      simpa only [← ENNReal.rpow_neg, neg_mul] using ENNReal.inv_le_inv.mpr hfull
    have hratio : ((tau : ENNReal) / (delta : ENNReal)) ^ eta <=
        (delta : ENNReal) ^ (-eta) := by
      calc
        ((tau : ENNReal) / (delta : ENNReal)) ^ eta <=
            (1 / (delta : ENNReal)) ^ eta :=
          ENNReal.rpow_le_rpow (ENNReal.div_le_div_right (by exact_mod_cast ht1) _) heta
        _ = (delta : ENNReal) ^ (-eta) := by
          rw [one_div, ENNReal.inv_rpow, ENNReal.rpow_neg]
    rw [ENNReal.inv_div (Or.inl hJtop) (Or.inr hfull0), div_eq_mul_inv]
    calc
      Cfine * (MED * (J * lambdaF⁻¹ *
          (BFpower * ((tau : ENNReal) / (delta : ENNReal)) ^ eta))) =
          (Cfine * BFpower) * MED * J * lambdaF⁻¹ *
            ((tau : ENNReal) / (delta : ENNReal)) ^ eta := by ring
      _ <= (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ (-e) *
          (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ (-4 * e) *
          (delta : ENNReal) ^ (-eta) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hC hMED) hJ) hinv) hratio
      _ = (delta : ENNReal) ^ (-(eta + 7 * e)) := by
        rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1
        ring
  have hfineCoefficientPayment {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      (e eta epsKF : Real) (JMED Cnorm Cf : ENNReal)
      (hJM : JMED <= (delta : ENNReal) ^ (-2 * e))
      (hCnorm : Cnorm <= (delta : ENNReal) ^ (-e))
      (hCf1 : 1 <= Cf) (hCf : Cf <= (delta : ENNReal) ^ (-(eta + 7 * e)))
      (hdebt : epsKF + 10 * e <= 3 * eta) :
      JMED * (Cnorm * (delta : ENNReal) ^ (-epsKF) * Cf ^ (1 - gamma / 2)) <=
        (delta : ENNReal) ^ (-4 * eta) := by
    have hgamma0 : 0 <= gamma := (hp.beta_pos.trans hp.gammaZero_gt).le.trans hgammaZero
    have hCfPower : Cf ^ (1 - gamma / 2) <= Cf := by
      simpa only [ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow_of_exponent_le hCf1 (by linarith : 1 - gamma / 2 <= 1)
    calc
      JMED * (Cnorm * (delta : ENNReal) ^ (-epsKF) * Cf ^ (1 - gamma / 2)) <=
          (delta : ENNReal) ^ (-2 * e) *
            ((delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ (-epsKF) *
              (delta : ENNReal) ^ (-(eta + 7 * e))) :=
        mul_le_mul' hJM (mul_le_mul' (mul_le_mul' hCnorm le_rfl) (hCfPower.trans hCf))
      _ = (delta : ENNReal) ^ (-(eta + epsKF + 10 * e)) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top]
        congr 1
        ring
      _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) (by linarith)
  have hcoarseCoefficientPayment {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      (e eta epsKF n0 : Real) (MED Nball L : ENNReal)
      (hMED : MED <= (delta : ENNReal) ^ (-e))
      (hconst : 2 * Nball * L <= (delta : ENNReal) ^ (-e))
      (hdebt : n0 + epsKF + e <= 2 * eta) (hpay : e <= 2 * eta) :
      (2 * Nball * L) * (delta : ENNReal) ^ (-n0 - epsKF) <=
        (delta : ENNReal) ^ (-4 * (eta / 2)) ∧
      MED * (delta : ENNReal) ^ (-4 * (eta / 2)) <= (delta : ENNReal) ^ (-4 * eta) := by
    constructor
    · calc
        (2 * Nball * L) * (delta : ENNReal) ^ (-n0 - epsKF) <=
            (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ (-n0 - epsKF) :=
          mul_le_mul' hconst le_rfl
        _ = (delta : ENNReal) ^ (-e + (-n0 - epsKF)) :=
          (ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top).symm
        _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) (by linarith)
    · calc
        MED * (delta : ENNReal) ^ (-4 * (eta / 2)) <=
            (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ (-4 * (eta / 2)) :=
          mul_le_mul' hMED le_rfl
        _ = (delta : ENNReal) ^ (-e + (-4 * (eta / 2))) :=
          (ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top).symm
        _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) (by linarith)
  let MEDfine := lineSelectionMultiplicityW95 3 1 (Nat.floor (Ctw : Real))
  let MEDcoarse := lineSelectionMultiplicityW95 3 2 (Nat.floor (Ctw : Real))
  have hfloor : 1 <= Nat.floor (Ctw : Real) :=
    (Nat.le_floor_iff Ctw.coe_nonneg).mpr (by exact_mod_cast hCtw)
  have hbandAndLine {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (hd : 0 < delta) (hd1 : delta <= 1)
      (F : Finset iota) (V : iota -> ShadedTube delta E)
      (hball : ∀ i ∈ F, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
      (hline : lineEssentiallyDistinctW94 F (fun i => (V i).toTube) Ctw)
      (K0 : ConvexSpaceBody E) (hK0 : ∀ i ∈ F, (V i).toConvexSpaceBody <= K0)
      (hfull : 0 < fullness' F (fun i => (V i).toShadedBody)) :
      ∃ (Q : Finset iota) (lam : NNReal), Q ⊆ F ∧ Q.Nonempty ∧ 0 < lam ∧
        (Q : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ Q, (lam : ENNReal) * volume (V i).carrier <= volume (V i).shade ∧
          volume (V i).shade <= 2 * (lam : ENNReal) * volume (V i).carrier) ∧
        fullness' F (fun i => (V i).toShadedBody) <=
          (bandLoss F.card * (MEDfine : ENNReal)) * fullness' Q (fun i => (V i).toShadedBody) ∧
        frostmanConstIn Q (fun i => (V i).toConvexSpaceBody) K0 <=
          (MEDfine : ENNReal) *
            ((fullness' F (fun i => (V i).toShadedBody) / bandLoss F.card)⁻¹ *
              frostmanConstIn F (fun i => (V i).toConvexSpaceBody) K0) ∧
        ShadedBody.multiplicity F (fun i => (V i).toShadedBody) <=
          (bandLoss F.card * (MEDfine : ENNReal)) *
            ShadedBody.multiplicity Q (fun i => (V i).toShadedBody) := by
    have hmass : 0 < ∑ i ∈ F, volume (V i).shade := by
      by_contra hn
      have hz := le_antisymm (not_lt.mp hn) bot_le
      simp only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] at hfull
    obtain ⟨G, hGF, lam, hlam, hG, hdensity, hbandFull, hbandCard, hbandCF, hbandMu⟩ :=
      hmassBandPaid hd F V K0 hK0 hmass
    have hGmass : 0 < ∑ i ∈ G, volume (V i).shade := by
      obtain ⟨i, hi⟩ := hG
      have hvol := (Tube.volume_pos_and_lt_top hd hd1 (V i).toTube).1
      have hsum : volume (V i).shade <= ∑ j ∈ G, volume (V j).shade := by
        exact Finset.single_le_sum (f := fun j => volume (V j).shade) (fun _ _ => zero_le) hi
      exact ((ENNReal.mul_pos (ENNReal.coe_pos.mpr hlam).ne' hvol.ne').trans_le
        (hdensity i hi).1).trans_le hsum
    have hcenter (i : iota) (hi : i ∈ G) : ‖(V i).center‖ <= (1 : Real) := by
      have heq : (V i).center = (V i).toTube.midpoint := by
        change midpoint Real (V i).x (V i).y = (1 / 2 : Real) • ((V i).x + (V i).y)
        rw [midpoint_eq_smul_add]
        norm_num
      rw [heq]
      exact Tube.norm_midpoint_le_of_subset_ball hd (V i).toTube (hball i (hGF hi))
    have hGline := hlineEDTransfer F G (fun i => (V i).toTube) (fun i => (V i).toTube)
      Ctw hGF (fun _ _ => rfl) hline
    obtain ⟨Q, hQG, hQ, hED, hQmass, hQcard, hQfull, hQCF, hQmax, hQmu⟩ :=
      exists_pairwise_lineED_paid_w95 hd hd1 G V hG 1 (by norm_num) hcenter
        (Nat.floor (Ctw : Real)) hfloor
        ((pointwise_lineED_iff_library_floor_w95 G (fun i => (V i).toTube) Ctw).mp hGline)
        K0 (fun i hi => hK0 i (hGF hi)) hGmass
    rw [hdim] at hQfull hQCF hQmu
    refine ⟨Q, lam, hQG.trans hGF, hQ, hlam, hED, fun i hi => hdensity i (hQG hi), ?_, ?_, ?_⟩
    · exact hbandFull.trans (by simpa only [mul_assoc] using mul_le_mul' le_rfl hQfull)
    · exact hQCF.trans (mul_le_mul' le_rfl hbandCF)
    · exact hbandMu.trans (by simpa only [mul_assoc] using mul_le_mul' le_rfl hQmu)
  have hcoarseLine {iota : Type uI} [DecidableEq iota] {delta : NNReal}
      (hd : 0 < delta) (hd1 : delta <= 1)
      (F : Finset iota) (V : iota -> ShadedTube delta E)
      (hball : ∀ i ∈ F, (V i).carrier ⊆ Metric.closedBall (0 : E) 2)
      (hline : lineEssentiallyDistinctW94 F (fun i => (V i).toTube) Ctw)
      (hfull : 0 < fullness' F (fun i => (V i).toShadedBody)) :
      ∃ Q ⊆ F, Q.Nonempty ∧
        (Q : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        fullness' F (fun i => (V i).toShadedBody) <=
          (MEDcoarse : ENNReal) * fullness' Q (fun i => (V i).toShadedBody) ∧
        frostmanConstIn Q (fun i => (V i).toConvexSpaceBody)
          (ConvexSpaceBody.closedBall (0 : E) 2 (by norm_num)) <=
          (MEDcoarse : ENNReal) * frostmanConstIn F (fun i => (V i).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) 2 (by norm_num)) ∧
        ShadedBody.multiplicity F (fun i => (V i).toShadedBody) <=
          (MEDcoarse : ENNReal) * ShadedBody.multiplicity Q (fun i => (V i).toShadedBody) := by
    have hmass : 0 < ∑ i ∈ F, volume (V i).shade := by
      by_contra hn
      have hz := le_antisymm (not_lt.mp hn) bot_le
      simp only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] at hfull
    have hF : F.Nonempty := by
      by_contra hn
      simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, lt_self_iff_false] at hmass
    have hcenter (i : iota) (hi : i ∈ F) : ‖(V i).center‖ <= (2 : Real) := by
      have heq : (V i).center = (V i).toTube.midpoint := by
        change midpoint Real (V i).x (V i).y = (1 / 2 : Real) • ((V i).x + (V i).y)
        rw [midpoint_eq_smul_add]
        norm_num
      rw [heq]
      exact Tube.norm_midpoint_le_of_subset_ball hd (V i).toTube (hball i hi)
    obtain ⟨Q, hQF, hQ, hED, hQmass, hQcard, hQfull, hQCF, hQmax, hQmu⟩ :=
      exists_pairwise_lineED_paid_w95 hd hd1 F V hF 2 (by norm_num) hcenter
        (Nat.floor (Ctw : Real)) hfloor
        ((pointwise_lineED_iff_library_floor_w95 F (fun i => (V i).toTube) Ctw).mp hline)
        (ConvexSpaceBody.closedBall (0 : E) 2 (by norm_num)) hball hmass
    rw [hdim] at hQfull hQCF hQmu
    exact ⟨Q, hQF, hQ, hED, hQfull, hQCF, hQmu⟩
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
  have hgeometricProduct {delta : NNReal}
      {iota : Type uI} [DecidableEq iota]
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
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
  have hactualScalar {delta : NNReal}
      {iota : Type uI} [DecidableEq iota]
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (block : ActualSourceDividingBlockW95 U p BF)
      (selections : ActualSameMassSelectionsW95 block loss)
      (R : iota) (hR : R ∈ selections.coarseFamily) :
      ShadedBody.multiplicity A (fun i => (Y i).toShadedBody) <=
        (loss : ENNReal) ^ (4 : Nat) *
          ShadedBody.multiplicity (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
            (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody) *
          ShadedBody.multiplicity (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
            (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) *
          ShadedBody.multiplicity (U.cover.indexSet block.a.val)
            (fun R' => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
              selections.coarseShading R').toShadedBody) := by
    have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
    have hloss : loss ≠ 0 := (lt_of_lt_of_le (by norm_num) selections.loss_one).ne'
    have hmiddleSub : selections.middle ⊆ U.cover.indexSet block.b.val :=
      selections.middle_subset.trans selections.first.parent_subset
    have hnormalization : ShadedBody.multiplicity selections.firstParents
        (fun Q => (selections.firstParentShading Q).toShadedBody) <=
        (loss : ENNReal) * ShadedBody.multiplicity selections.middle
          (fun Q => (selections.middleShading Q).toShadedBody) := by
      simpa only [ENNReal.coe_inv hloss, inv_inv] using ShadedBody.multiplicity_le_of_isCRefinement
        selections.firstParents (fun Q => (selections.firstParentShading Q).toShadedBody)
        (inv_ne_zero hloss) selections.normalization
    have hfineCut : ShadedBody.multiplicity
        (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
        (fun i => (selectedShade selections.firstFamily Y selections.firstShading i).toShadedBody) <=
        (loss : ENNReal) * ShadedBody.multiplicity
          (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
          (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody) := by
      simpa only [ENNReal.coe_inv hloss, inv_inv] using ShadedBody.multiplicity_le_of_isCRefinement
        (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
        (fun i => (selectedShade selections.firstFamily Y selections.firstShading i).toShadedBody)
        (inv_ne_zero hloss) selections.selected_fine_refinement
    have hmiddleInput : ShadedBody.multiplicity (U.cover.indexSet block.b.val)
        (fun Q => (zeroExtend selections.middle (U.cover.tube block.b.val) selections.middleShading Q).toShadedBody) =
        ShadedBody.multiplicity selections.middle (fun Q => (selections.middleShading Q).toShadedBody) :=
      multiplicity_zeroExtend_of_subset hmiddleSub _ _
    have hmiddleFibre : (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R) ∩
        selections.secondFamily = fibre selections.secondFamily selections.coarseAssign R := by
      ext Q
      simp only [Finset.mem_inter, fibre, Finset.mem_filter]
      constructor
      · intro hQ
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ.1
        obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
        exact ⟨hQ.2, (selections.parent_compatibility i hiA).trans hiR⟩
      · intro hQ
        have hQb : Q ∈ U.cover.indexSet block.b.val := selections.second.child_subset_amb hQ.1
        rw [← reg.surjective block.b.val hb] at hQb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQb
        exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
          ⟨hi, (selections.parent_compatibility i hi).symm.trans hQ.2⟩, rfl⟩, hQ.1⟩
    have hmiddleOutput : ShadedBody.multiplicity
        (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
        (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) =
        ShadedBody.multiplicity (fibre selections.secondFamily selections.coarseAssign R)
          (fun Q => (selections.secondShading Q).toShadedBody) := by
      rw [actualSecondAmbientW97, multiplicity_zeroExtend, hmiddleFibre]
    have hsecond := selections.second.scalar R hR
    rw [hmiddleInput, ← hmiddleOutput,
      ← multiplicity_zeroExtend_of_subset selections.second.parent_subset
        (U.cover.tube block.a.val) selections.coarseShading] at hsecond
    calc
      _ <= (loss : ENNReal) *
          ShadedBody.multiplicity selections.firstParents (fun Q => (selections.firstParentShading Q).toShadedBody) *
          ShadedBody.multiplicity (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
            (fun i => (selectedShade selections.firstFamily Y selections.firstShading i).toShadedBody) :=
        selections.first.sel_scalar
      _ <= (loss : ENNReal) * ((loss : ENNReal) *
          ((loss : ENNReal) * ShadedBody.multiplicity (U.cover.indexSet block.a.val)
            (fun R' => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
              selections.coarseShading R').toShadedBody) *
            ShadedBody.multiplicity (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
              (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody))) *
          ((loss : ENNReal) *
            ShadedBody.multiplicity (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
              (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody)) := by
        exact mul_le_mul' (mul_le_mul_left' (hnormalization.trans (mul_le_mul_left' hsecond _)) _)
          hfineCut
      _ = _ := by ring
  have htubeVolume {s : NNReal} (hs : 0 < s) (T : Tube s E) : 0 < volume T.carrier := by
    apply lt_of_lt_of_le _ T.le_volume
    exact ENNReal.mul_pos (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos _)).ne'
      (pow_ne_zero _ (ENNReal.coe_pos.mpr hs).ne')
  have heligibleActive {delta : NNReal} (hd : 0 < delta)
      {iota : Type uI} [DecidableEq iota]
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
      (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (block : ActualSourceDividingBlockW95 U p BF)
      (selections : ActualSameMassSelectionsW95 block loss)
      (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
      (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
        Rnorm Cext Cnorm CtwNorm CcellNorm aux)
      (R : iota) (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)) :
      R ∈ selections.coarseFamily := by
    have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
    have ha : block.a.val <= M := block.a_lt_b.le.trans hb
    have hRparts : R ∈ U.cover.indexSet block.a.val ∧
        (Cext : ENNReal) *
          (((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^
            aux.inner block.label) *
          (∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
            volume (U.cover.tube block.b.val Q).carrier) <=
          ∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
            volume (actualSecondAmbientW97 selections Q).shade := by
      simpa only [actualEligibleThetaParentsW97, Finset.mem_filter] using hR
    have hRa : R ∈ U.cover.indexSet block.a.val := hRparts.1
    let F := actualDescendantsW95 A U.cover.assign block.a.val block.b.val R
    have hF : F.Nonempty := by
      rw [← reg.surjective block.a.val ha] at hRa
      obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRa
      exact ⟨U.cover.assign block.b.val i,
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
    obtain ⟨Q0, hQ0⟩ := hF
    have hscale : 0 < Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val :=
      div_pos (Tube.gridScale_pos hd M _) (Tube.gridScale_pos hd M _)
    have hCext : (Cext : ENNReal) ≠ 0 := by
      intro hzero
      have hh := ((calls.normalization R hR).carrier_volume Q0 hQ0).2
      rw [hzero, zero_mul, zero_mul] at hh
      exact (not_le_of_gt (htubeVolume hscale ((calls.normalization R hR).normalized Q0).toTube)) hh
    have hcarrier : 0 < ∑ Q ∈ F, volume (U.cover.tube block.b.val Q).carrier :=
      (htubeVolume (Tube.gridScale_pos hd M _) (U.cover.tube block.b.val Q0)).trans_le
        (Finset.single_le_sum (f := fun Q => volume (U.cover.tube block.b.val Q).carrier)
          (fun _ _ => bot_le) hQ0)
    have hthreshold : 0 < (Cext : ENNReal) *
        (((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^
          aux.inner block.label) * ∑ Q ∈ F, volume (U.cover.tube block.b.val Q).carrier := by
      exact ENNReal.mul_pos (mul_ne_zero hCext (ENNReal.rpow_pos
        (ENNReal.coe_pos.mpr hscale) ENNReal.coe_ne_top).ne') hcarrier.ne'
    have hmass : 0 < ∑ Q ∈ F, volume (actualSecondAmbientW97 selections Q).shade :=
      hthreshold.trans_le hRparts.2
    obtain ⟨Q, hQ, hQpos⟩ := Finset.sum_pos_iff.mp hmass
    have hQsecond : Q ∈ selections.secondFamily := by
      by_contra hQnot
      have hzero : (actualSecondAmbientW97 selections Q).shade = ∅ :=
        zeroExtend_shade_of_not_mem hQnot
      simpa only [hzero, measure_empty, lt_self_iff_false] using hQpos
    have hparent := selections.second.parent_mapsTo Q hQsecond
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
    rwa [selections.parent_compatibility i hiA, hiR] at hparent
  have hfineFullness {delta : NNReal} (hd : 0 < delta)
      {iota : Type uI} [DecidableEq iota]
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (block : ActualSourceDividingBlockW95 U p BF)
      (selections : ActualSameMassSelectionsW95 block loss) :
      ((loss : ENNReal) ^ (2 : Nat))⁻¹ * fullness' A (fun i => (Y i).toShadedBody) <=
        fullness' (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
          (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody) := by
    have hloss : loss ≠ 0 := (lt_of_lt_of_le (by norm_num) selections.loss_one).ne'
    let F := completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel
    let Z := selectedShade selections.firstFamily Y selections.firstShading
    have hF : F.Nonempty := selections.first.sel_nonempty
    obtain ⟨i0, hi0⟩ := hF
    have hcarrier : 0 < ∑ i ∈ F, volume (Z i).carrier :=
      (htubeVolume hd (Z i0).toTube).trans_le
        (Finset.single_le_sum (f := fun i => volume (Z i).carrier) (fun _ _ => bot_le) hi0)
    have href := ShadedBody.IsCRefinement.mul_fullness_le F
      (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody)
      F (fun i => (Z i).toShadedBody) hcarrier selections.selected_fine_refinement
    have hrefE : (loss : ENNReal)⁻¹ * fullness' F (fun i => (Z i).toShadedBody) <=
        fullness' F (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody) := by
      have hh := ENNReal.coe_le_coe.mpr href
      simpa only [ENNReal.coe_mul, ENNReal.coe_inv hloss, ShadedBody.coe_fullness] using hh
    have hfirst : (loss : ENNReal)⁻¹ * fullness' A (fun i => (Y i).toShadedBody) <=
        fullness' F (fun i => (Z i).toShadedBody) := by
      simpa only [F, Z, completeFibreW94, fibre, ShadedBody.coe_fullness] using
        selections.first.sel_fullness_lb.trans selections.first.sel_fullness
    calc
      _ = (loss : ENNReal)⁻¹ * ((loss : ENNReal)⁻¹ * fullness' A (fun i => (Y i).toShadedBody)) := by
        rw [ENNReal.inv_pow, pow_two, mul_assoc]
      _ <= (loss : ENNReal)⁻¹ * fullness' F (fun i => (Z i).toShadedBody) := mul_le_mul_left' hfirst _
      _ <= _ := hrefE
  have hcollapse {delta tau theta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      (hdt : delta <= tau) (htt : tau <= theta) (ht1 : theta <= 1)
      (m : Fin (p.N + 1)) (hm : m.val < p.N)
      (hlong : tau / theta <= delta ^ p.ε)
      {nFine nMiddle nCoarse nAll : Nat}
      (hfpos : 1 <= nFine) (hmpos : 1 <= nMiddle) (hcpos : 1 <= nCoarse) (hapos : 1 <= nAll)
      (hcount : (nFine : ENNReal) * (nMiddle : ENNReal) * (nCoarse : ENNReal) <= 4 * (nAll : ENNReal))
      {X muf mum muc L : ENNReal}
      (hscalar : X <= L * muf * mum * muc)
      (hL : L <= (delta : ENNReal) ^ (-xi m))
      (hf : muf <= (delta : ENNReal) ^ (-4 * p.η m.val) *
        ((delta / tau : NNReal) : ENNReal) ^ (-2 * gamma) *
        ((nFine : ENNReal) * ((delta / tau : NNReal) : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2))
      (hmiddle : mum <= ((tau / theta : NNReal) : ENNReal) ^ (20 * xi m / p.ε) *
        ((tau / theta : NNReal) : ENNReal) ^ (-2 * gamma) *
        ((nMiddle : ENNReal) * ((tau / theta : NNReal) : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2))
      (hc : muc <= (delta : ENNReal) ^ (-4 * p.η m.val) * (theta : ENNReal) ^ (-2 * gamma) *
        ((nCoarse : ENNReal) * (theta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2)) :
      X <= 4 * (delta : ENNReal) ^ (18 * xiMin) * (delta : ENNReal) ^ (-2 * gamma) *
        ((delta : ENNReal) ^ (2 : Nat) * (nAll : ENNReal)) ^ (1 - gamma / 2) := by
    have ht : 0 < tau := hd.trans_le hdt
    have htheta : 0 < theta := ht.trans_le htt
    have hgamma0 : 0 <= gamma := (hp.beta_pos.trans hp.gammaZero_gt).le.trans hgammaZero
    have hq : 0 <= 1 - gamma / 2 := by linarith
    have hq1 : 1 - gamma / 2 <= 1 := by linarith
    have hxi : 0 < xi m := hp.xi_pos m hm
    have hgoodExponent : 0 <= 20 * xi m / p.ε := (div_pos (by positivity) hp.epsilon_pos).le
    have hlongE : ((tau / theta : NNReal) : ENNReal) <= (delta : ENNReal) ^ p.ε := by
      simpa only [ENNReal.coe_rpow_of_ne_zero hd.ne'] using ENNReal.coe_le_coe.mpr hlong
    have hgoodGain : ((tau / theta : NNReal) : ENNReal) ^ (20 * xi m / p.ε) <=
        (delta : ENNReal) ^ (10 * (2 * xi m)) := by
      calc
        _ <= ((delta : ENNReal) ^ p.ε) ^ (20 * xi m / p.ε) :=
          ENNReal.rpow_le_rpow hlongE hgoodExponent
        _ = _ := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp [hp.epsilon_pos.ne']
          <;> ring
    have hm' : mum <= (delta : ENNReal) ^ (10 * (2 * xi m)) *
        ((tau / theta : NNReal) : ENNReal) ^ (-2 * gamma) *
        ((nMiddle : ENNReal) * ((tau / theta : NNReal) : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) :=
      hmiddle.trans (mul_le_mul_right' (mul_le_mul_right' hgoodGain _) _)
    have hscales : delta / tau * (tau / theta) * theta = delta := by
      field_simp
    have htriple := tripleCollapse_gain hd
      (div_pos hd ht) ((div_le_one ht).mpr hdt)
      (div_pos ht htheta) ((div_le_one htheta).mpr htt) htheta ht1 hscales
      hgamma0 hgamma (by exact_mod_cast hfpos) (by exact_mod_cast hmpos)
      (by exact_mod_cast hcpos) (show (1 : ENNReal) <= 4 * (nAll : ENNReal) by
        exact one_le_mul (by norm_num) (by exact_mod_cast hapos)) hcount
      (hscalar.trans (mul_le_mul' (mul_le_mul' (mul_le_mul_left' hf L) hm') hc))
    have hcost : L * (delta : ENNReal) ^ (10 * (2 * xi m) - 8 * p.η m.val) <=
        (delta : ENNReal) ^ (18 * xiMin) := by
      calc
        _ <= (delta : ENNReal) ^ (-xi m) *
            (delta : ENNReal) ^ (10 * (2 * xi m) - 8 * p.η m.val) := mul_le_mul_right' hL _
        _ = (delta : ENNReal) ^ (-xi m + (10 * (2 * xi m) - 8 * p.η m.val)) :=
          (ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top).symm
        _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1)
          (by linarith [hp.rung_xi m hm, hp.xiMin_lower m hm])
    have hfour : (4 : ENNReal) ^ (1 - gamma / 2) <= 4 := by
      simpa only [ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ENNReal) <= 4) hq1
    calc
      X <= L * (delta : ENNReal) ^ (10 * (2 * xi m) - 8 * p.η m.val) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((4 * (nAll : ENNReal)) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := htriple
      _ <= (delta : ENNReal) ^ (18 * xiMin) * (delta : ENNReal) ^ (-2 * gamma) *
          ((4 * (nAll : ENNReal)) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
        gcongr
      _ = (4 : ENNReal) ^ (1 - gamma / 2) * (delta : ENNReal) ^ (18 * xiMin) *
          (delta : ENNReal) ^ (-2 * gamma) *
          ((delta : ENNReal) ^ (2 : Nat) * (nAll : ENNReal)) ^ (1 - gamma / 2) := by
        rw [mul_assoc 4, ENNReal.mul_rpow_of_nonneg _ _ hq]
        simp only [mul_comm (nAll : ENNReal) ((delta : ENNReal) ^ (2 : Nat))]
        ring
      _ <= _ := by gcongr
  have hassembled {delta : NNReal} (hd : 0 < delta) (hd1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
      (hA : A.Nonempty) (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (block : ActualSourceDividingBlockW95 U p BF)
      (selections : ActualSameMassSelectionsW95 block loss)
      (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
      (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
        Rnorm Cext Cnorm CtwNorm CcellNorm aux)
      (hloss : (loss : ENNReal) <= (delta : ENNReal) ^ (-xi block.label / 100))
      (R : iota) (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label))
      (hgood : detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
        (calls.normalization R hR).normalized gamma p.ε (xi block.label))
      (hf : ShadedBody.multiplicity
        (completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel)
        (fun i => (selectedShade selections.fineFamily Y selections.fineShading i).toShadedBody) <=
          (delta : ENNReal) ^ (-4 * p.η block.label.val) *
          ((delta / Tube.gridScale delta M block.b.val : NNReal) : ENNReal) ^ (-2 * gamma) *
          (((completeFibreW94 A (U.cover.assign block.b.val) selections.fineLabel).card : ENNReal) *
            ((delta / Tube.gridScale delta M block.b.val : NNReal) : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2))
      (hc : ShadedBody.multiplicity (U.cover.indexSet block.a.val)
        (fun R' => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
          selections.coarseShading R').toShadedBody) <=
          (delta : ENNReal) ^ (-4 * p.η block.label.val) *
          (Tube.gridScale delta M block.a.val : ENNReal) ^ (-2 * gamma) *
          (((U.cover.indexSet block.a.val).card : ENNReal) *
            (Tube.gridScale delta M block.a.val : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2)) :
      ShadedBody.multiplicity A (fun i => (Y i).toShadedBody) <=
        4 * (delta : ENNReal) ^ (18 * xiMin) * (delta : ENNReal) ^ (-2 * gamma) *
          ((delta : ENNReal) ^ (2 : Nat) * (A.card : ENNReal)) ^ (1 - gamma / 2) := by
    have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
    have ha : block.a.val <= M := block.a_lt_b.le.trans hb
    have hRcoarse := heligibleActive hd U Uext reg block selections aux calls R hR
    have hRa := selections.second.parent_subset hRcoarse
    have hQ := selections.first.parent_subset selections.first.sel_mem
    have hmiddlePos : 1 <= (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R).card := by
      have hh := (reg.countBand_pos block.a.val block.b.val block.a_lt_b hb).trans_le
        (reg.count_lower block.a.val block.b.val block.a_lt_b hb R hRa)
      exact Nat.succ_le_iff.mpr (by exact_mod_cast hh)
    have hL : (loss : ENNReal) ^ (4 : Nat) <= (delta : ENNReal) ^ (-xi block.label) := by
      calc
        _ <= ((delta : ENNReal) ^ (-xi block.label / 100)) ^ (4 : Nat) := pow_le_pow_left' hloss 4
        _ = (delta : ENNReal) ^ ((-xi block.label / 100) * 4) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1)
          (by linarith [hp.xi_pos block.label block.label_active])
    have hdt : delta <= Tube.gridScale delta M block.b.val := by
      calc
        _ = Tube.gridScale delta M M := (Tube.gridScale_self delta hp.M_pos).symm
        _ <= _ := Tube.gridScale_antitone hd hd1 M hb
    have htt := Tube.gridScale_antitone hd hd1 M block.a_lt_b.le
    have ht1 : Tube.gridScale delta M block.a.val <= 1 := Tube.gridScale_le_one hd1 M block.a.val
    have hmiddle : ShadedBody.multiplicity
        (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
        (fun Q => (actualSecondAmbientW97 selections Q).toShadedBody) <=
        (((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^
          (20 * xi block.label / p.ε)) *
        (((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^
          (-2 * gamma)) *
        (((actualDescendantsW95 A U.cover.assign block.a.val block.b.val R).card : ENNReal) *
          (((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^
            (2 : Nat))) ^ (1 - gamma / 2) := by
      dsimp only [detailedInnerGoodW94] at hgood
      rw [(calls.normalization R hR).multiplicity] at hgood
      simpa only [mul_comm _ ((actualDescendantsW95 A U.cover.assign block.a.val block.b.val R).card : ENNReal)]
        using hgood
    exact hcollapse hd hd1 hdt htt ht1 block.label block.label_active block.block_long
      (Nat.succ_le_iff.mpr selections.first.sel_nonempty.card_pos) hmiddlePos
      (Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨R, hRa⟩))
      (Nat.succ_le_iff.mpr hA.card_pos)
      (hgeometricProduct U reg block selections selections.fineLabel hQ R hRa)
      (hactualScalar U reg block selections R hRcoarse) hL hf hmiddle hc
  let z0 := p.η 0
  have hz0 : 0 < z0 := hp.zeta_pos 0 (Nat.zero_le _)
  let epsKF := z0 / 4
  have hepsKF : 0 < epsKF := div_pos hz0 (by norm_num)
  obtain ⟨etaFine, hetaFine, hFineKF⟩ := hfineKFActual epsKF hepsKF
  obtain ⟨etaCoarse, hetaCoarse, Nball, hNball, hCoarseKF⟩ := multiplicity_le_coarse_ball hdim
    ((hp.beta_pos.trans hp.gammaZero_gt).le.trans hgammaZero) hgamma hKF 2 (by norm_num)
    epsKF hepsKF
  let e := min etaFine (min etaCoarse (min z0 xiMin)) / 10000
  have he : 0 < e := div_pos (lt_min hetaFine (lt_min hetaCoarse (lt_min hz0 hp.xiMin_pos))) (by norm_num)
  have heFine : 10000 * e <= etaFine := by
    dsimp only [e]
    linarith [min_le_left etaFine (min etaCoarse (min z0 xiMin))]
  have heCoarse : 10000 * e <= etaCoarse := by
    dsimp only [e]
    linarith [(min_le_right etaFine (min etaCoarse (min z0 xiMin))).trans
      (min_le_left etaCoarse (min z0 xiMin))]
  have heZeta : 10000 * e <= z0 := by
    dsimp only [e]
    linarith [((min_le_right etaFine (min etaCoarse (min z0 xiMin))).trans
      (min_le_right etaCoarse (min z0 xiMin))).trans (min_le_left z0 xiMin)]
  have heXi : 10000 * e <= xiMin := by
    dsimp only [e]
    linarith [((min_le_right etaFine (min etaCoarse (min z0 xiMin))).trans
      (min_le_right etaCoarse (min z0 xiMin))).trans (min_le_right z0 xiMin)]
  let K2 := ConvexSpaceBody.closedBall (0 : E) 2 (by norm_num)
  let Cvol : ENNReal := volume K2.carrier / volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
  have hCvolTop : Cvol ≠ ⊤ := ENNReal.div_ne_top
    K2.isCompact.measure_ne_top ConvexSpaceBody.closedUnitBall_volume_pos.ne'
  let LC : NNReal := max (1 : NNReal) (((MEDcoarse : ENNReal) * 2 * Cvol).toNNReal)
  have hLC : 1 <= LC := le_max_left _ _
  have hcoarseCFConst : (MEDcoarse : ENNReal) * 2 * Cvol <= (LC : ENNReal) := by
    calc
      _ = ((((MEDcoarse : ENNReal) * 2 * Cvol).toNNReal : NNReal) : ENNReal) :=
        (ENNReal.coe_toNNReal (by finiteness)).symm
      _ <= (LC : ENNReal) := ENNReal.coe_le_coe.mpr (le_max_right _ _)
  have hthetaSmall : Filter.Eventually (fun delta : NNReal =>
      ∀ k : Nat, 1 <= k -> Tube.gridScale delta M k <= (1 / 4 : NNReal))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    have hexp : (0 : Real) < 1 / (M : Real) := div_pos zero_lt_one (by exact_mod_cast hp.M_pos)
    have htend0 : Filter.Tendsto (fun delta : NNReal => delta ^ (1 / (M : Real)))
        (nhds (0 : NNReal)) (nhds 0) := by
      simpa only [NNReal.zero_rpow hexp.ne'] using
        (show ContinuousAt (fun delta : NNReal => delta ^ (1 / (M : Real))) 0 from
          (NNReal.continuous_rpow_const hexp.le).continuousAt).tendsto
    have hsmallN0 : Filter.Eventually (fun y : NNReal => y <= (1 / 4 : NNReal))
        (nhds (0 : NNReal)) := eventually_le_nhds (by norm_num)
    have hsmallN : Filter.Eventually (fun delta : NNReal =>
        delta ^ (1 / (M : Real)) <= (1 / 4 : NNReal)) (nhds (0 : NNReal)) :=
      htend0.eventually hsmallN0
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hsmallN,
      eventually_le_nhdsGT (c := (1 : NNReal)) zero_lt_one,
      self_mem_nhdsWithin] with delta hsmall hd1 hd
    intro k hk
    have hgrid : Tube.gridScale delta M 1 <= (1 / 4 : NNReal) := by
      simpa only [Tube.gridScale, Nat.cast_one] using hsmall
    exact (Tube.gridScale_antitone hd hd1 M hk).trans hgrid
  have hgoodEventually : Filter.Eventually (fun delta : NNReal =>
      ∀ {iota : Type uI} [DecidableEq iota]
        {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan loss : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty -> (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        (delta : ENNReal) ^ (2 * e) <= fullness' A (fun i => (Y i).toShadedBody) ->
        frostmanConstIn A (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (delta : ENNReal) ^ (-(2 * e)) ->
      ∀ (block : ActualSourceDividingBlockW95 U p BF)
        (S : ActualSameMassSelectionsW95 block loss)
        (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
        (calls : ActualEligibleTrialCallsW97 Uext block S xi gamma Rnorm Cext Cnorm CtwNorm CcellNorm aux),
        (loss : ENNReal) <= (towerPreparationRetainedW95 delta Cselect Kselect)⁻¹ ->
        ((loss : ENNReal) ^ (14 : Nat))⁻¹ * (fullness' A (fun i => (Y i).toShadedBody)) ^ (4 : Nat) <=
          fullness' (U.cover.indexSet block.a.val)
            (fun R => (zeroExtend S.coarseFamily (U.cover.tube block.a.val) S.coarseShading R).toShadedBody) ->
      ∀ R (hR : R ∈ actualEligibleThetaParentsW97 S Cext (aux.inner block.label)),
        detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
          (calls.normalization R hR).normalized gamma p.ε (xi block.label) ->
        ShadedBody.multiplicity A (fun i => (Y i).toShadedBody) <=
          4 * (delta : ENNReal) ^ (18 * xiMin) * (delta : ENNReal) ^ (-2 * gamma) *
            ((delta : ENNReal) ^ (2 : Nat) * (A.card : ENNReal)) ^ (1 - gamma / 2))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [hFineKF, hCoarseKF LC hLC (2 * e) (z0 / 2) (by positivity) (by positivity),
      hprepPayment Cselect Kselect e he, huniformBandPayment Ctw e he, hthetaSmall,
      eventually_finite_const_le_rpow_neg (c := (MEDfine : ENNReal)) (by finiteness) he,
      eventually_finite_const_le_rpow_neg (c := (MEDcoarse : ENNReal)) (by finiteness) he,
      eventually_finite_const_le_rpow_neg (c := 4 * (fineNormalizeDilate.C 1 : ENNReal)) (by finiteness) he,
      eventually_finite_const_le_rpow_neg (c := (fineNormalizeDilate.C 1 : ENNReal) * (BF : ENNReal) ^ p.N)
        (by finiteness) he,
      eventually_finite_const_le_rpow_neg (c := 2 * (Nball : ENNReal) * (LC : ENNReal)) (by finiteness) he,
      eventually_finite_const_le_rpow_neg (c := (Ctw : ENNReal)) (by finiteness) he,
      eventually_finite_const_le_rpow_neg (c := (2 : ENNReal)) (by finiteness) he,
      eventually_le_nhdsGT (c := (1 : NNReal)) zero_lt_one, self_mem_nhdsWithin]
      with delta hFine hCoarse hpoly hband htheta hMEDfine hMEDcoarse hNorm hCFnorm hLCpay hTw hTwo hd1 hd
    intro iota inst A Y Ccan loss U Uext hA hball reg hfull hCF block S aux calls hloss houter R hR hgood
    have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
    have ha : block.a.val <= M := block.a_lt_b.le.trans hb
    have haLt : block.a.val < M := block.a_lt_b.trans_le hb
    have hdpow (a b : Real) (hab : a <= b) : (delta : ENNReal) ^ b <= (delta : ENNReal) ^ a :=
      ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1) hab
    have hlossPaid : (loss : ENNReal) <= (delta : ENNReal) ^ (-e) := by
      exact hloss.trans (by simpa only [← ENNReal.rpow_neg] using ENNReal.inv_le_inv.mpr hpoly)
    have hetaLabel : z0 <= p.η block.label.val := hp.zeta_mono 0 _ (Nat.zero_le _) block.label_active.le
    have hetaLabelPos : 0 < p.η block.label.val := hz0.trans_le hetaLabel
    have hlossScalar : (loss : ENNReal) <= (delta : ENNReal) ^ (-(xi block.label) / 100) :=
      hlossPaid.trans (hdpow _ _ (by linarith [hp.xiMin_lower block.label block.label_active]))
    have hfineFull : (delta : ENNReal) ^ (4 * e) <=
        fullness' (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel)
          (fun i => (selectedShade S.fineFamily Y S.fineShading i).toShadedBody) := by
      have h := hpowerReserve hd e loss _ hfull hlossPaid 2 1
      norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one, one_pow, pow_one] at h
      exact h.trans (hfineFullness hd U block S)
    have hcoarseFull : (delta : ENNReal) ^ (22 * e) <=
        fullness' (U.cover.indexSet block.a.val)
          (fun R => (zeroExtend S.coarseFamily (U.cover.tube block.a.val) S.coarseShading R).toShadedBody) := by
      have h := hpowerReserve hd e loss _ hfull hlossPaid 14 4
      norm_num only [Nat.cast_ofNat] at h
      exact h.trans houter
    have hcoarse : ShadedBody.multiplicity (U.cover.indexSet block.a.val)
        (fun R' => (zeroExtend S.coarseFamily (U.cover.tube block.a.val)
          S.coarseShading R').toShadedBody) <=
        (delta : ENNReal) ^ (-4 * p.η block.label.val) *
          (Tube.gridScale delta M block.a.val : ENNReal) ^ (-2 * gamma) *
          (((U.cover.indexSet block.a.val).card : ENNReal) *
            (Tube.gridScale delta M block.a.val : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
      by_cases ha0 : block.a.val = 0
      · apply hcoarseEndpoint U reg hA block S ha0
        exact hTw.trans (hdpow _ _ (by linarith [heZeta, hetaLabel]))
      · have ha1 : 1 <= block.a.val := Nat.one_le_iff_ne_zero.mpr ha0
        have hcoarseTube : ∀ R' ∈ S.coarseFamily,
            (S.coarseShading R').toTube = U.cover.tube block.a.val R' :=
          S.second.parent_tube
        have hline : lineEssentiallyDistinctW94 (U.cover.indexSet block.a.val)
            (fun R' => (zeroExtend S.coarseFamily (U.cover.tube block.a.val)
              S.coarseShading R').toTube) Ctw := by
          intro o v hv
          have hh := reg.parent_line_ed block.a.val ha
          simpa only [zeroExtend_toTube hcoarseTube] using hh o v hv
        have hcoarsePos : 0 < fullness' (U.cover.indexSet block.a.val)
            (fun R' => (zeroExtend S.coarseFamily (U.cover.tube block.a.val)
              S.coarseShading R').toShadedBody) :=
          (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hd) ENNReal.coe_ne_top).trans_le hcoarseFull
        obtain ⟨Q, hQF, hQ, hED, hQfull, hQCF, hQmu⟩ :=
          hcoarseLine (delta := Tube.gridScale delta M block.a.val)
            (Tube.gridScale_pos hd M block.a.val)
            (Tube.gridScale_le_one hd1 M block.a.val)
            (U.cover.indexSet block.a.val)
            (fun R' => zeroExtend S.coarseFamily (U.cover.tube block.a.val)
              S.coarseShading R')
            (fun R' hR' => by
              rw [zeroExtend_toTube hcoarseTube]
              exact reg.parent_ball block.a.val ha R' hR') hline hcoarsePos
        have hCFambient := hcoarseAmbientCF hd U reg hA hball
          ((delta : ENNReal) ^ (-(2 * e))) hCF block.a.val
          haLt
        have hQCF' : frostmanConstIn Q
            (fun R' => (zeroExtend S.coarseFamily (U.cover.tube block.a.val)
              S.coarseShading R').toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) 2 (by norm_num)) <=
              (LC : ENNReal) * (delta : ENNReal) ^ (-(2 * e)) := by
          apply le_trans hQCF
          rw [frostmanConstIn_congr _ (fun i _ =>
            congrArg Tube.toConvexSpaceBody (zeroExtend_toTube hcoarseTube i)) _]
          calc
            _ <= (MEDcoarse : ENNReal) *
                (2 * Cvol * (delta : ENNReal) ^ (-(2 * e))) :=
              mul_le_mul_left' hCFambient _
            _ = ((MEDcoarse : ENNReal) * 2 * Cvol) *
                (delta : ENNReal) ^ (-(2 * e)) := by ring
            _ <= _ := mul_le_mul_right' hcoarseCFConst _
        have hQreserve := hpaidFullnessReserve hd e (22 * e)
          (MEDcoarse : ENNReal) _ _ hMEDcoarse hcoarseFull hQfull
        have hQfullKF : 2 * (delta : ENNReal) ^ etaCoarse <=
            (ShadedBody.fullness Q (fun R' =>
              (zeroExtend S.coarseFamily (U.cover.tube block.a.val)
                S.coarseShading R').toShadedBody) : ENNReal) := by
          rw [ShadedBody.coe_fullness]
          exact (hnormalizationFullnessPayment hd hd1 2 e (22 * e + e)
            etaCoarse hTwo (by linarith)).trans hQreserve
        have hcoeff := hcoarseCoefficientPayment hd hd1 e z0 epsKF (2 * e)
          (MEDcoarse : ENNReal) (Nball : ENNReal) (LC : ENNReal)
          hMEDcoarse hLCpay (by dsimp only [epsKF]; linarith) (by linarith)
        have hdtA : delta <= Tube.gridScale delta M block.a.val := by
          calc
            delta = Tube.gridScale delta M M := (Tube.gridScale_self delta hp.M_pos).symm
            _ <= _ := Tube.gridScale_antitone hd hd1 M ha
        have hQmult := hCoarse
          (Tube.gridScale delta M block.a.val)
          hdtA (by exact_mod_cast htheta block.a.val ha1)
          (fun R' => zeroExtend S.coarseFamily (U.cover.tube block.a.val)
            S.coarseShading R') hQ
          (fun R' hR' => by
            rw [zeroExtend_toTube hcoarseTube]
            exact reg.parent_ball block.a.val ha R' (hQF hR'))
          hED hQCF' hQfullKF hcoeff.1
        have hcoefficient : (MEDcoarse : ENNReal) * (delta : ENNReal) ^ (-4 * (z0 / 2)) <=
            (delta : ENNReal) ^ (-4 * p.η block.label.val) :=
          hcoeff.2.trans (hdpow _ _ (by linarith))
        calc
          _ <= (MEDcoarse : ENNReal) *
              ((delta : ENNReal) ^ (-4 * (z0 / 2)) *
                (Tube.gridScale delta M block.a.val : ENNReal) ^ (-2 * gamma) *
                ((Q.card : ENNReal) *
                  (Tube.gridScale delta M block.a.val : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2)) :=
            hQmu.trans (mul_le_mul_left' hQmult _)
          _ = ((MEDcoarse : ENNReal) * (delta : ENNReal) ^ (-4 * (z0 / 2))) *
              (Tube.gridScale delta M block.a.val : ENNReal) ^ (-2 * gamma) *
              ((Q.card : ENNReal) *
                (Tube.gridScale delta M block.a.val : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by ring
          _ <= _ := mul_le_mul' (mul_le_mul_right' hcoefficient _)
            (ENNReal.rpow_le_rpow (mul_le_mul_right' (by exact_mod_cast Finset.card_le_card hQF) _)
              (by linarith : 0 <= 1 - gamma / 2))
    have hfine : ShadedBody.multiplicity
        (completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel)
        (fun i => (selectedShade S.fineFamily Y S.fineShading i).toShadedBody) <=
        (delta : ENNReal) ^ (-4 * p.η block.label.val) *
          ((delta / Tube.gridScale delta M block.b.val : NNReal) : ENNReal) ^ (-2 * gamma) *
          (((completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel).card : ENNReal) *
            ((delta / Tube.gridScale delta M block.b.val : NNReal) : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
      by_cases hbM : block.b.val = M
      · exact hfineEndpoint hd hd1 U reg block S hbM
      · have hbLt : block.b.val < M := Nat.lt_of_le_of_ne hb hbM
        obtain ⟨hFne, hFbody, hFCF⟩ := hfineOriginalData U reg block S hbLt
        let F := completeFibreW94 A (U.cover.assign block.b.val) S.fineLabel
        let V := fun i => selectedShade S.fineFamily Y S.fineShading i
        let tau := Tube.gridScale delta M block.b.val
        have hGF : F ⊆ A := by
          intro i hi
          exact (Finset.mem_filter.mp hi).1
        have hballF : ∀ i ∈ F, (V i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
          intro i hi
          have hiA := (Finset.mem_filter.mp hi).1
          rw [congrArg (fun t => t.carrier) (selectedShade_toTube S.fine_same_tube i)]
          exact hball i hiA
        have hlineF : lineEssentiallyDistinctW94 F
            (fun i => (V i).toTube) Ctw := by
          apply hlineEDTransfer A F (fun i => (Y i).toTube)
            (fun i => (V i).toTube) Ctw hGF
          · intro i hi
            exact congrArg (fun t => t.carrier) (selectedShade_toTube S.fine_same_tube i)
          · exact hbottomLine U reg
        have hKfine : ∀ i ∈ F, (V i).toConvexSpaceBody <=
            (U.cover.tube block.b.val S.fineLabel).toConvexSpaceBody := by
          intro i hi
          exact hFbody i hi
        have hFpos : 0 < fullness' F (fun i => (V i).toShadedBody) := by
          exact (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hd) ENNReal.coe_ne_top).trans_le
            hfineFull
        obtain ⟨Q, lam, hQF, hQne, hlam, hQED, hQdensity, hQfull, hQCF, hQmu⟩ :=
          hbandAndLine hd hd1 F V hballF hlineF
            (U.cover.tube block.b.val S.fineLabel).toConvexSpaceBody hKfine hFpos
        let Cfine : ENNReal := fineNormalizeDilate.C 1
        let BFpower : ENNReal := (BF : ENNReal) ^ p.N
        let J : ENNReal := bandLoss F.card
        let lambdaF : ENNReal := fullness' F (fun i => (V i).toShadedBody)
        let ratio : ENNReal := ((tau : ENNReal) / (delta : ENNReal))
        let raw : ENNReal := Cfine * ((MEDfine : ENNReal) *
          ((lambdaF / J)⁻¹ * (BFpower * ratio ^ (p.η block.label.val))))
        let Cf : ENNReal := max 1 raw
        have hJtop : J ≠ ⊤ := by
          dsimp [J]
          exact ENNReal.coe_ne_top
        have hrawCF : frostmanConstIn Q
            (fun i => (V i).toConvexSpaceBody)
            (U.cover.tube block.b.val S.fineLabel).toConvexSpaceBody <= raw / Cfine := by
          have hq := hQCF.trans (mul_le_mul_left' (mul_le_mul_left' hFCF _) _)
          calc
            _ <= (MEDfine : ENNReal) *
                ((lambdaF / J)⁻¹ * (BFpower * ratio ^ (p.η block.label.val))) := hq
            _ = raw / Cfine := by
              dsimp only [raw]
              rw [mul_comm Cfine, ENNReal.mul_div_cancel_right
                (ENNReal.coe_ne_zero.mpr (zero_lt_one.trans_le (one_le_fineNormalizeDilate_C 1)).ne')
                ENNReal.coe_ne_top]
        have hCFQ : frostmanConstIn Q
            (fun i => (V i).toConvexSpaceBody)
            (U.cover.tube block.b.val S.fineLabel).toConvexSpaceBody <= Cf / Cfine := by
          exact hrawCF.trans (ENNReal.div_le_div_right (le_max_right _ _) _)
        have hJ : J <= (delta : ENNReal) ^ (-e) :=
          hband F (fun i => (V i).toTube) hballF hlineF
        have hJM : J * (MEDfine : ENNReal) <= (delta : ENNReal) ^ (-2 * e) := by
          dsimp [J]
          calc
            _ <= (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ (-e) :=
              mul_le_mul' hJ hMEDfine
            _ = (delta : ENNReal) ^ (-2 * e) := by
              rw [← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top]
              congr 1 <;> ring
        have hraw : raw <= (delta : ENNReal) ^ (-(p.η block.label.val + 7 * e)) := by
          exact hfineCFPayment hd (Tube.gridScale_le_one hd1 M block.b.val)
            e (p.η block.label.val) hetaLabelPos.le Cfine
            (MEDfine : ENNReal) J BFpower lambdaF
            hCFnorm hMEDfine hJ hJtop hfineFull
        have hCf : Cf <= (delta : ENNReal) ^ (-(p.η block.label.val + 7 * e)) := by
          apply max_le
          · exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
              (ENNReal.coe_pos.mpr hd) (by exact_mod_cast hd1)
              (by linarith [hetaLabelPos, he])
          · exact hraw
        have hCf1 : 1 <= Cf := le_max_left _ _
        have hCftop : Cf ≠ ⊤ := ne_top_of_le_ne_top
          (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top) hCf
        have hcoeff := hfineCoefficientPayment hd hd1 e (p.η block.label.val) epsKF
          (J * (MEDfine : ENNReal)) (4 * Cfine) Cf hJM hNorm hCf1 hCf
          (by dsimp only [epsKF]; linarith)
        have hQreserve := hpaidFullnessReserve hd (2 * e) (4 * e)
          (J * (MEDfine : ENNReal)) _ _ (by simpa only [neg_mul] using hJM) hfineFull hQfull
        have hQfullKF : 4 * Cfine * (delta : ENNReal) ^ etaFine <=
            fullness' Q (fun i => (V i).toShadedBody) :=
          (hnormalizationFullnessPayment hd hd1 (4 * Cfine) e (4 * e + 2 * e)
            etaFine hNorm (by linarith)).trans hQreserve
        have hdt : delta <= tau := by
          calc
            delta = Tube.gridScale delta M M := (Tube.gridScale_self delta hp.M_pos).symm
            _ <= tau := Tube.gridScale_antitone hd hd1 M hb
        have hQmult := hFine Cf hCf1 hCftop U reg block.b.val hb hdt
          (Tube.gridScale_le_one hd1 M block.b.val) S.fineLabel
          (S.first.parent_subset S.first.sel_mem) Q V hQne hQF
          (fun i _ => selectedShade_toTube S.fine_same_tube i)
          hQED lam hlam hQdensity hQfullKF hCFQ
        calc
          _ <= (J * (MEDfine : ENNReal)) *
              (4 * Cfine * (delta : ENNReal) ^ (-epsKF) * Cf ^ (1 - gamma / 2) *
                ((delta / tau : NNReal) : ENNReal) ^ (-2 * gamma) *
                ((Q.card : ENNReal) * ((delta / tau : NNReal) : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2)) := by
            exact hQmu.trans (mul_le_mul_left' hQmult _)
          _ <= (delta : ENNReal) ^ (-4 * p.η block.label.val) *
              ((delta / tau : NNReal) : ENNReal) ^ (-2 * gamma) *
              ((F.card : ENNReal) * ((delta / tau : NNReal) : ENNReal) ^ (2 : Nat)) ^
                (1 - gamma / 2) := by
            calc
              _ = ((J * (MEDfine : ENNReal)) *
                  (4 * Cfine * (delta : ENNReal) ^ (-epsKF) * Cf ^ (1 - gamma / 2))) *
                  ((delta / tau : NNReal) : ENNReal) ^ (-2 * gamma) *
                  ((Q.card : ENNReal) * ((delta / tau : NNReal) : ENNReal) ^ (2 : Nat)) ^
                    (1 - gamma / 2) := by ring
              _ <= _ := mul_le_mul' (mul_le_mul_right' hcoeff _)
                (ENNReal.rpow_le_rpow (mul_le_mul_right' (by exact_mod_cast Finset.card_le_card hQF) _)
                  (by linarith : 0 <= 1 - gamma / 2))
    exact hassembled hd hd1 U Uext hA reg block S aux calls hlossScalar R hR hgood hfine hcoarse
  obtain ⟨deltaCut, hdeltaCut, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgoodEventually
  let delta0 : NNReal := min deltaCut (1 / 2)
  refine ⟨4, 2 * e, 2 * e, delta0, by norm_num, by positivity, ?_, by positivity, ?_,
    lt_min hdeltaCut (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  · change 2 * e < z0 / 100
    linarith
  · change 2 * e < z0 / 100
    linarith
  · intro delta hd hdSmall iota inst A Y Ccan loss
    simpa only [ENNReal.coe_ofNat] using
      (hcut ⟨hd, hdSmall.trans_le (min_le_left _ _)⟩
        (iota := iota) (A := A) (Y := Y) (Ccan := Ccan) (loss := loss))


end

end Kakeya.ml1Boot.TrialRestartW94
