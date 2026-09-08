module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionRawCutsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionArrayW97

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

/-- The raw B8 object kept alive by the actual second selection.  The public
selection record intentionally forgets these construction fields, so the estimate
retains them in a separate certificate. -/
structure ActualSecondRawWitnessW99
    {iota : Type uI} [DecidableEq iota] {rho theta : NNReal}
    (H : Finset iota) (Z : iota -> ShadedTube rho E)
    (J : Finset iota) (Ttheta : iota -> Tube theta E)
    (parent : iota -> iota) (m : iota -> ENNReal) (c : NNReal) where
  mid : Finset iota
  z : E
  FF : ShadedBody.FactorFamily E iota iota
  G : ShadedBody.ShadedFactorFamily E iota iota
  Yi : iota -> ShadedTube rho E
  Yo : iota -> ShadedTube theta E
  mid_nonempty : mid.Nonempty
  mid_subset : mid ⊆ H
  FF_inner : FF.innerSet = mid
  FF_outer : FF.outerSet = mid.image parent
  FF_parent : FF.parent = parent
  FF_innerBody : FF.innerBody = (fun i => ((Z i).translate (-z)).toShadedBody)
  FF_outerBody : FF.outerBody =
    (fun Q => ((Ttheta Q).translate (-z)).toConvexSpaceBody)
  raw : ActualRawRhoStatisticsW97 FF (fun i => (Z i).translate (-z))
    (fun Q => (Ttheta Q).translate (-z)) G
  Yi_transport : ∀ i ∈ G.innerSet,
    (Yi i).toTube = (Z i).toTube ∧
      (Yi i).toShadedBody = (G.innerBody i).translate z ∧
      (Yi i).shade ⊆ (Z i).shade
  Yo_transport : ∀ Q ∈ G.outerSet,
    (Yo Q).toTube = Ttheta Q ∧
      (Yo Q).toShadedBody = (G.outerBody Q).translate z
  scalar : ∀ Q ∈ G.outerSet,
    ShadedBody.multiplicity mid (fun i => (Z i).toShadedBody) <=
      (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
        (Module.finrank Real E) mid.card rho 1 : ENNReal) *
        ShadedBody.multiplicity G.outerSet
          (fun Q => (Yo Q).toShadedBody) *
        ShadedBody.multiplicity (G.fiber Q)
          (fun i => (Yi i).toShadedBody)

/-- One actual same-selection certificate.  `raw_witness` and the positive
fullness fields refer to the same selected middle/coarse data. -/
structure ActualSameMassSelectionCertificateW99
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    {p : Params} {BF : NNReal}
    (block : ActualSourceDividingBlockW95 U p BF) (loss : NNReal) where
  selections : ActualSameMassSelectionsW95 block loss
  middleParents : Finset iota
  coarseParents : Finset iota
  commonMass : NNReal
  raw_witness :
    ∃ (H : Finset iota) (c : NNReal) (J : Finset iota)
      (Z : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E)
      (Ttheta : iota -> Tube (Tube.gridScale delta M block.a.val) E)
      (parent : iota -> iota) (m : iota -> ENNReal)
      (raw : ActualSecondRawWitnessW99 H Z J Ttheta parent m c),
      raw.mid = middleParents
  middle_fullness :
    ((loss : ENNReal) ^ (6 : Nat))⁻¹ *
        (fullness' A (fun i => (Y i).toShadedBody)) ^ (2 : Nat) <=
      fullness' (U.cover.indexSet block.b.val)
        (fun Q => (zeroExtend selections.secondFamily (U.cover.tube block.b.val)
          selections.secondShading Q).toShadedBody)
  coarse_fullness :
    ((loss : ENNReal) ^ (14 : Nat))⁻¹ *
        (fullness' A (fun i => (Y i).toShadedBody)) ^ (4 : Nat) <=
      fullness' (U.cover.indexSet block.a.val)
        (fun R => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
          selections.coarseShading R).toShadedBody)
  coarse_fullness_pos :
    0 < fullness' (U.cover.indexSet block.a.val)
      (fun R => (zeroExtend selections.coarseFamily (U.cover.tube block.a.val)
        selections.coarseShading R).toShadedBody)

/-- The actual same-mass construction retains both fullness bounds on the
SAME selections, using the FULL original middle and coarse carriers. -/
theorem exists_actual_same_mass_selections_with_certificate_w99
    (hdim : Module.finrank Real E = 3) (M : Nat) (hM : 1 <= M)
    (Ccan Ctw Ccell : NNReal)
    (hCcan : 1 <= Ccan) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (eReserve : Real) (heReserve : 0 < eReserve) :
    ∃ (Cselect : NNReal) (Kselect : Nat) (delta0 : NNReal),
      1 <= Cselect ∧ 1 <= Kselect ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (A : Finset iota) (Y : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
          A.Nonempty -> SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
          (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          (delta : ENNReal) ^ eReserve <= fullness' A (fun i => (Y i).toShadedBody) ->
          ∀ {p : Params} {BF : NNReal} (block : ActualSourceDividingBlockW95 U p BF),
            let loss := Cselect * Real.toNNReal
              ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ Kselect)
            ∃ certificate : ActualSameMassSelectionCertificateW99 block loss, True := by  set_option maxHeartbeats 2000000 in
    exact (by

      have hbottomCounts {iota : Type uI} [DecidableEq iota] {delta : NNReal}
          (A : Finset iota) (Y : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
          (regular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
          (b : Nat) (hb : b <= M) :
          ∃ n : NNReal, 0 < n ∧ ∀ Q ∈ U.cover.indexSet b,
            n <= ((completeFibreW94 A (U.cover.assign b) Q).card : NNReal) ∧
            ((completeFibreW94 A (U.cover.assign b) Q).card : NNReal) <= 2 * n := by
        by_cases hbM : b = M
        · subst b
          refine ⟨1, one_pos, ?_⟩
          intro Q hQ
          have hQA : Q ∈ A := regular.bottom_index ▸ hQ
          have hfibre : completeFibreW94 A (U.cover.assign M) Q = {Q} := by
            ext i
            simp only [completeFibreW94, Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨hi, heq⟩
              rwa [regular.bottom_assign i hi] at heq
            · intro heq
              subst i
              exact ⟨hQA, regular.bottom_assign Q hQA⟩
          rw [hfibre]
          norm_num
        · have hbLt : b < M := lt_of_le_of_ne hb hbM
          refine ⟨regular.countBand b M, regular.countBand_pos b M hbLt le_rfl, ?_⟩
          intro Q hQ
          have hfibre : actualDescendantsW95 A U.cover.assign b M Q =
              completeFibreW94 A (U.cover.assign b) Q := by
            ext i
            constructor
            · intro hi
              obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
              rw [regular.bottom_assign j (Finset.mem_filter.mp hj).1] at hji
              exact hji ▸ hj
            · intro hi
              exact Finset.mem_image.mpr ⟨i, hi, regular.bottom_assign i (Finset.mem_filter.mp hi).1⟩
          exact ⟨hfibre ▸ regular.count_lower b M hbLt le_rfl Q hQ,
            hfibre ▸ (regular.count_upper b M hbLt le_rfl Q hQ).le⟩
      have hretainedParentCount {iota : Type uI} [DecidableEq iota]
          (A F J H : Finset iota) (parent : iota -> iota)
          (w w' : iota -> ENNReal) (v n alpha lambda : ENNReal)
          (hv : 0 < v) (hvfinite : v < ⊤) (hn : 0 < n) (hnfinite : n < ⊤)
          (hparent : ∀ i ∈ A, parent i ∈ J) (hFA : F ⊆ A)
          (hFH : ∀ i ∈ F, parent i ∈ H) (hHJ : H ⊆ J)
          (hcount : ∀ Q ∈ J,
            n <= ((completeFibreW94 A parent Q).card : ENNReal) ∧
            ((completeFibreW94 A parent Q).card : ENNReal) <= 2 * n)
          (hw : ∀ i ∈ F, w' i <= v)
          (hinput : (∑ i ∈ A, w i) = lambda * ((A.card : ENNReal) * v))
          (hmass : alpha * (∑ i ∈ A, w i) <= ∑ i ∈ F, w' i) :
          alpha * lambda * (J.card : ENNReal) <= 2 * (H.card : ENNReal) := by
        have hcountA : (A.card : ENNReal) =
            ∑ Q ∈ J, ((completeFibreW94 A parent Q).card : ENNReal) := by
          have h := Finset.sum_fiberwise_of_maps_to hparent (fun _ => (1 : ENNReal))
          simpa only [completeFibreW94, Finset.sum_const, nsmul_eq_mul, mul_one] using h.symm
        have hlower : (J.card : ENNReal) * n <= A.card := by
          rw [hcountA]
          simpa only [Finset.sum_const, nsmul_eq_mul] using
            Finset.sum_le_sum (fun Q hQ => (hcount Q hQ).1)
        have hupper : (∑ i ∈ F, w' i) <= (H.card : ENNReal) * (2 * n * v) := by
          calc
            _ = ∑ Q ∈ H, ∑ i ∈ completeFibreW94 F parent Q, w' i :=
              (Finset.sum_fiberwise_of_maps_to hFH _).symm
            _ <= ∑ Q ∈ H, (2 * n * v) := by
              apply Finset.sum_le_sum
              intro Q hQ
              have hsub : completeFibreW94 F parent Q ⊆ completeFibreW94 A parent Q := by
                intro i hi
                obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
                exact Finset.mem_filter.mpr ⟨hFA hi, heq⟩
              calc
                _ <= ((completeFibreW94 F parent Q).card : ENNReal) * v := by
                  simpa only [completeFibreW94, Finset.sum_const, nsmul_eq_mul] using
                    Finset.sum_le_sum (fun i hi => hw i (Finset.mem_filter.mp hi).1)
                _ <= ((completeFibreW94 A parent Q).card : ENNReal) * v :=
                  mul_le_mul' (by exact_mod_cast Finset.card_le_card hsub) le_rfl
                _ <= 2 * n * v := mul_le_mul' (hcount Q (hHJ hQ)).2 le_rfl
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        have hpaid : (alpha * lambda * (J.card : ENNReal)) * (n * v) <=
            (2 * (H.card : ENNReal)) * (n * v) := by
          calc
            _ = alpha * (lambda * (((J.card : ENNReal) * n) * v)) := by ring
            _ <= alpha * (lambda * ((A.card : ENNReal) * v)) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hlower le_rfl))
            _ = alpha * (∑ i ∈ A, w i) := by rw [hinput]
            _ <= ∑ i ∈ F, w' i := hmass
            _ <= (H.card : ENNReal) * (2 * n * v) := hupper
            _ = _ := by ring
        exact (ENNReal.mul_le_mul_iff_left
          (ENNReal.mul_pos hn.ne' hv.ne').ne' (ENNReal.mul_lt_top hnfinite hvfinite).ne).mp hpaid
      have hparentAmbientFullness {iota : Type uI} [DecidableEq iota] {rho : NNReal}
          (J H : Finset iota) (T : iota -> Tube rho E) (Z : iota -> ShadedTube rho E)
          (hJ : J.Nonempty) (hH : H.Nonempty) (hHJ : H ⊆ J)
          (v : ENNReal) (hv : 0 < v) (hvfinite : v < ⊤)
          (hvolume : ∀ Q ∈ J, volume (T Q).carrier = v)
          (htube : ∀ Q ∈ H, (Z Q).toTube = T Q)
          (a b : NNReal) (hb : 0 < b)
          (hcount : (a : ENNReal) * (J.card : ENNReal) <= 2 * (H.card : ENNReal))
          (hfull : (b : ENNReal)⁻¹ * (a : ENNReal) <= fullness' H (fun Q => (Z Q).toShadedBody)) :
          ((2 * b : NNReal) : ENNReal)⁻¹ * (a : ENNReal) ^ (2 : Nat) <=
            fullness' J (fun Q => (zeroExtend H T Z Q).toShadedBody) := by
        have hdenH : (∑ Q ∈ H, volume (Z Q).carrier) = (H.card : ENNReal) * v := by
          calc
            _ = ∑ Q ∈ H, v := Finset.sum_congr rfl (fun Q hQ => by
              change volume (Z Q).toTube.carrier = v
              rw [htube Q hQ]
              exact hvolume Q (hHJ hQ))
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        have hdenJ : (∑ Q ∈ J, volume (zeroExtend H T Z Q).carrier) = (J.card : ENNReal) * v := by
          calc
            _ = ∑ Q ∈ J, v := Finset.sum_congr rfl (fun Q hQ => by
              change volume (zeroExtend H T Z Q).toTube.carrier = v
              rw [zeroExtend_toTube htube]
              exact hvolume Q hQ)
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        have hHpos : (0 : ENNReal) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
        have hJpos : (0 : ENNReal) < J.card := by exact_mod_cast Finset.card_pos.mpr hJ
        have hdenHpos : (0 : ENNReal) < (H.card : ENNReal) * v := ENNReal.mul_pos hHpos.ne' hv.ne'
        have hdenJpos : (0 : ENNReal) < (J.card : ENNReal) * v := ENNReal.mul_pos hJpos.ne' hv.ne'
        have hdenHfin : (H.card : ENNReal) * v < ⊤ := ENNReal.mul_lt_top (by finiteness) hvfinite
        have hdenJfin : (J.card : ENNReal) * v < ⊤ := ENNReal.mul_lt_top (by finiteness) hvfinite
        have hmassH : ((b : ENNReal)⁻¹ * (a : ENNReal)) * ((H.card : ENNReal) * v) <=
            ∑ Q ∈ H, volume (Z Q).shade := by
          have h := mul_le_mul' hfull (le_refl ((H.card : ENNReal) * v))
          rw [fullness', hdenH, ENNReal.div_mul_cancel hdenHpos.ne' hdenHfin.ne] at h
          exact h
        have hcardHalf : (2 : ENNReal)⁻¹ * ((a : ENNReal) * (J.card : ENNReal)) <= H.card :=
          (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).mpr hcount
        have hmass : ((2 * b : NNReal) : ENNReal)⁻¹ * (a : ENNReal) ^ (2 : Nat) *
            ((J.card : ENNReal) * v) <= ∑ Q ∈ H, volume (Z Q).shade := by
          calc
            _ = ((b : ENNReal)⁻¹ * (a : ENNReal)) *
                (((2 : ENNReal)⁻¹ * ((a : ENNReal) * (J.card : ENNReal))) * v) := by
              rw [ENNReal.coe_mul, ENNReal.coe_ofNat,
                ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
              ring
            _ <= ((b : ENNReal)⁻¹ * (a : ENNReal)) * ((H.card : ENNReal) * v) :=
              mul_le_mul' le_rfl (mul_le_mul' hcardHalf le_rfl)
            _ <= _ := hmassH
        rw [fullness', sum_volume_shade_zeroExtend_of_subset hHJ, hdenJ]
        exact (ENNReal.le_div_iff_mul_le (Or.inl hdenJpos.ne') (Or.inl hdenJfin.ne)).mpr hmass
      have hfullnessOfRetainedMass {iota : Type uI}
          (A F : Finset iota) (Y W : iota -> ShadedBody E)
          (alpha : ENNReal) (hFA : F ⊆ A)
          (hcarrier : ∀ i ∈ F, (W i).carrier = (Y i).carrier)
          (hmass : alpha * (∑ i ∈ A, volume (Y i).shade) <= ∑ i ∈ F, volume (W i).shade) :
          alpha * fullness' A Y <= fullness' F W := by
        have hden : (∑ i ∈ F, volume (W i).carrier) <= ∑ i ∈ A, volume (Y i).carrier := by
          calc
            _ = ∑ i ∈ F, volume (Y i).carrier :=
              Finset.sum_congr rfl (fun i hi => congrArg volume (hcarrier i hi))
            _ <= _ := Finset.sum_le_sum_of_subset hFA
        unfold fullness'
        calc
          _ = (alpha * (∑ i ∈ A, volume (Y i).shade)) / (∑ i ∈ A, volume (Y i).carrier) := by
            simp only [div_eq_mul_inv, mul_assoc]
          _ <= (∑ i ∈ F, volume (W i).shade) / (∑ i ∈ A, volume (Y i).carrier) :=
            ENNReal.div_le_div_right hmass _
          _ <= _ := ENNReal.div_le_div le_rfl hden
      have hzeroExtendFullnessRetention {iota : Type uI} [DecidableEq iota] {rho : NNReal}
          (J H F : Finset iota) (T : iota -> Tube rho E)
          (Z W : iota -> ShadedTube rho E) (alpha : ENNReal)
          (hHJ : H ⊆ J) (hFJ : F ⊆ J)
          (hZT : ∀ Q ∈ H, (Z Q).toTube = T Q) (hWT : ∀ Q ∈ F, (W Q).toTube = T Q)
          (hmass : alpha * (∑ Q ∈ H, volume (Z Q).shade) <= ∑ Q ∈ F, volume (W Q).shade) :
          alpha * fullness' J (fun Q => (zeroExtend H T Z Q).toShadedBody) <=
            fullness' J (fun Q => (zeroExtend F T W Q).toShadedBody) := by
        apply hfullnessOfRetainedMass J J _ _ alpha (Finset.Subset.refl _)
        · intro Q hQ
          change (zeroExtend F T W Q).toTube.carrier = (zeroExtend H T Z Q).toTube.carrier
          rw [zeroExtend_toTube hWT, zeroExtend_toTube hZT]
        · rw [sum_volume_shade_zeroExtend_of_subset hHJ, sum_volume_shade_zeroExtend_of_subset hFJ]
          exact hmass

      have hfullnessDebt (cross Cgeom Cbin K Craw B J L1 L2 : NNReal)
          (hcross : 1 <= cross) (hgeom : 1 <= Cgeom) (hbin : 1 <= Cbin)
          (hK : 1 <= K) (hraw : 1 <= Craw) (hB : 1 <= B)
          (hJ : J <= Cbin * B) (hL1 : L1 <= Craw * B ^ (6 : Nat))
          (hL2 : L2 <= Craw * B ^ (6 : Nat)) :
          32 * cross * J ^ (2 : Nat) * L1 ^ (2 : Nat) * K * L2 <=
            (16 * cross * Cgeom * Cbin * K * Craw ^ (3 : Nat) * B ^ (19 : Nat)) ^ (6 : Nat) := by
        have hc : cross <= cross ^ (6 : Nat) := by
          simpa only [pow_one] using pow_le_pow_right₀ hcross (by norm_num : 1 <= 6)
        have hk : K <= K ^ (6 : Nat) := by
          simpa only [pow_one] using pow_le_pow_right₀ hK (by norm_num : 1 <= 6)
        have hcb : Cbin ^ (2 : Nat) <= Cbin ^ (6 : Nat) := pow_le_pow_right₀ hbin (by norm_num)
        have hcr : Craw ^ (3 : Nat) <= Craw ^ (18 : Nat) := pow_le_pow_right₀ hraw (by norm_num)
        have hb : B ^ (20 : Nat) <= B ^ (114 : Nat) := pow_le_pow_right₀ hB (by norm_num)
        calc
          _ <= 32 * cross * (Cbin * B) ^ (2 : Nat) * (Craw * B ^ (6 : Nat)) ^ (2 : Nat) *
              K * (Craw * B ^ (6 : Nat)) := by gcongr
          _ = 32 * cross * 1 * Cbin ^ (2 : Nat) * K * Craw ^ (3 : Nat) * B ^ (20 : Nat) := by ring
          _ <= (16 : NNReal) ^ (6 : Nat) * cross ^ (6 : Nat) * Cgeom ^ (6 : Nat) *
              Cbin ^ (6 : Nat) * K ^ (6 : Nat) * Craw ^ (18 : Nat) * B ^ (114 : Nat) :=
            mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul'
              (mul_le_mul' (by norm_num : (32 : NNReal) <= 16 ^ (6 : Nat)) hc)
                (one_le_pow₀ hgeom)) hcb) hk) hcr) hb
          _ = _ := by ring
      have hjoint_label {iota : Type uI} [DecidableEq iota]
          (Q : Finset iota) (h m t : iota -> ENNReal) (S : ENNReal) (r : NNReal)
          (hr : 0 < r) (hS : 0 < S) (hSfinite : S < ⊤)
          (hH : 0 < ∑ q ∈ Q, h q) (hHfinite : (∑ q ∈ Q, h q) < ⊤)
          (hM : (∑ q ∈ Q, m q) <= S)
          (hT : (r : ENNReal) * S <= ∑ q ∈ Q, t q)
          (htm : ∀ q ∈ Q, t q <= m q) :
          ∃ q ∈ Q, 0 < t q ∧
            ((r / 4 : NNReal) : ENNReal) * (S / (∑ j ∈ Q, h j)) * h q <= m q ∧
            ((r / 4 : NNReal) : ENNReal) * m q <= t q := by
        let rho : ENNReal := ((r / 4 : NNReal) : ENNReal)
        let H := ∑ q ∈ Q, h q
        by_contra hn
        have hpoint : ∀ q ∈ Q, t q <= rho * (S / H) * h q + rho * m q := by
          intro q hq
          by_cases ht : 0 < t q
          · by_cases hm : rho * (S / H) * h q <= m q
            · have hbad : ¬rho * m q <= t q := fun hgood => hn ⟨q, hq, ht, hm, hgood⟩
              exact (not_le.mp hbad).le.trans (le_add_left le_rfl)
            · exact ((htm q hq).trans (not_le.mp hm).le).trans (le_add_right le_rfl)
          · exact (not_lt.mp ht).trans bot_le
        have hsum : (∑ q ∈ Q, t q) <= rho * S + rho * S := by
          calc
            (∑ q ∈ Q, t q) <= ∑ q ∈ Q, (rho * (S / H) * h q + rho * m q) := Finset.sum_le_sum hpoint
            _ = rho * (S / H) * H + rho * (∑ q ∈ Q, m q) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            _ <= rho * (S / H) * H + rho * S := add_le_add_right (mul_le_mul' le_rfl hM) _
            _ = rho * S + rho * S := by rw [mul_assoc, ENNReal.div_mul_cancel hH.ne' hHfinite.ne]
        have hcoeff : rho + rho < (r : ENNReal) := by
          have hreal : (r : Real) / 4 + (r : Real) / 4 < r := by
            have hrR : (0 : Real) < r := hr
            linarith
          have hnn : (r / 4 : NNReal) + r / 4 < r := by exact_mod_cast hreal
          dsimp [rho]
          exact_mod_cast hnn
        have hstrict : rho * S + rho * S < (r : ENNReal) * S := by
          rw [← add_mul]
          simpa only [mul_comm] using ENNReal.mul_lt_mul_right hS.ne' hSfinite.ne hcoeff
        exact (not_lt_of_ge (hT.trans hsum)) hstrict
      have hactual_joint_label {iota : Type uI} [DecidableEq iota] {delta : NNReal}
          (A F T : Finset iota) (Y Yfirst Ylast : iota -> ShadedTube delta E)
          (parent : iota -> iota) (r : NNReal) (hr : 0 < r)
          (hFA : F ⊆ A) (hTF : T ⊆ F)
          (hfirstTube : ∀ i ∈ F, (Yfirst i).toTube = (Y i).toTube)
          (hlastTube : ∀ i ∈ T, (Ylast i).toTube = (Y i).toTube)
          (hfirstShade : ∀ i ∈ F, (Yfirst i).shade ⊆ (Y i).shade)
          (hlastShade : ∀ i ∈ T, (Ylast i).shade ⊆ (Yfirst i).shade)
          (hS : 0 < ∑ i ∈ A, volume (Y i).shade)
          (hretained : (r : ENNReal) * (∑ i ∈ A, volume (Y i).shade) <=
            ∑ i ∈ T, volume (Ylast i).shade) :
          ∃ q ∈ F.image parent,
            ((r / 4 : NNReal) : ENNReal) * fullness' A (fun i => (Y i).toShadedBody) <=
              fullness' (completeFibreW94 A parent q)
                (fun i => ((selectedShade F Y Yfirst) i).toShadedBody) ∧
            IsCRefinement (completeFibreW94 A parent q)
              (fun i => ((selectedShade T Y Ylast) i).toShadedBody)
              (completeFibreW94 A parent q)
              (fun i => ((selectedShade F Y Yfirst) i).toShadedBody) (r / 4) := by
        let Zfirst := selectedShade F Y Yfirst
        let Zlast := selectedShade T Y Ylast
        let Q := A.image parent
        let fibre := completeFibreW94 A parent
        let h := fun q => ∑ i ∈ fibre q, volume (Y i).carrier
        let m := fun q => ∑ i ∈ fibre q, volume (Zfirst i).shade
        let t := fun q => ∑ i ∈ fibre q, volume (Zlast i).shade
        have hfirst_body (i : iota) : (Zfirst i).toConvexSpaceBody = (Y i).toConvexSpaceBody :=
          congrArg Tube.toConvexSpaceBody (selectedShade_toTube hfirstTube i)
        have hlast_body (i : iota) : (Zlast i).toConvexSpaceBody = (Y i).toConvexSpaceBody :=
          congrArg Tube.toConvexSpaceBody (selectedShade_toTube hlastTube i)
        have hfirst_sub (i : iota) : (Zfirst i).shade ⊆ (Y i).shade := by
          by_cases hi : i ∈ F
          · change (zeroExtend F (fun i => (Y i).toTube) Yfirst i).shade ⊆ _
            rw [zeroExtend_shade_of_mem hi]
            exact hfirstShade i hi
          · change (zeroExtend F (fun i => (Y i).toTube) Yfirst i).shade ⊆ _
            rw [zeroExtend_shade_of_not_mem hi]
            exact Set.empty_subset _
        have hlast_sub (i : iota) : (Zlast i).shade ⊆ (Zfirst i).shade := by
          by_cases hi : i ∈ T
          · change (zeroExtend T (fun i => (Y i).toTube) Ylast i).shade ⊆
              (zeroExtend F (fun i => (Y i).toTube) Yfirst i).shade
            rw [zeroExtend_shade_of_mem hi, zeroExtend_shade_of_mem (hTF hi)]
            exact hlastShade i hi
          · change (zeroExtend T (fun i => (Y i).toTube) Ylast i).shade ⊆ _
            rw [zeroExtend_shade_of_not_mem hi]
            exact Set.empty_subset _
        have hsum (w : iota -> ENNReal) : (∑ q ∈ Q, ∑ i ∈ fibre q, w i) = ∑ i ∈ A, w i :=
          Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem parent hi) w
        have hsumH : (∑ q ∈ Q, h q) = ∑ i ∈ A, volume (Y i).carrier := hsum _
        have hsumM : (∑ q ∈ Q, m q) = ∑ i ∈ F, volume (Yfirst i).shade :=
          (hsum _).trans (sum_volume_shade_zeroExtend_of_subset hFA _ _)
        have hsumT : (∑ q ∈ Q, t q) = ∑ i ∈ T, volume (Ylast i).shade :=
          (hsum _).trans (sum_volume_shade_zeroExtend_of_subset (hTF.trans hFA) _ _)
        have hmass : (∑ q ∈ Q, m q) <= ∑ i ∈ A, volume (Y i).shade := by
          rw [hsum _]
          exact Finset.sum_le_sum (fun i hi => measure_mono (hfirst_sub i))
        have hshade_carrier : (∑ i ∈ A, volume (Y i).shade) <= ∑ i ∈ A, volume (Y i).carrier :=
          Finset.sum_le_sum (fun i hi => measure_mono (Y i).shade_subset)
        have hHfinite : (∑ q ∈ Q, h q) < ⊤ := by
          rw [hsumH, lt_top_iff_ne_top]
          exact ENNReal.sum_ne_top.mpr (fun i hi => (Y i).toConvexSpaceBody.isCompact.measure_ne_top)
        have hHpos : 0 < ∑ q ∈ Q, h q := by rw [hsumH]; exact hS.trans_le hshade_carrier
        have hSfinite : (∑ i ∈ A, volume (Y i).shade) < ⊤ :=
          hshade_carrier.trans_lt (hsumH ▸ hHfinite)
        have htm (q : iota) : t q <= m q := Finset.sum_le_sum (fun i hi => measure_mono (hlast_sub i))
        have hmh (q : iota) : m q <= h q := Finset.sum_le_sum
          (fun i hi => measure_mono ((hfirst_sub i).trans (Y i).shade_subset))
        obtain ⟨q, hq, htq, hfull, hcut⟩ := hjoint_label Q h m t
          (∑ i ∈ A, volume (Y i).shade) r hr hS hSfinite hHpos hHfinite hmass
          (hsumT.symm ▸ hretained) (fun q hq => htm q)
        have hqF : q ∈ F.image parent := by
          by_contra hn
          have htzero : t q = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hiT : i ∉ T := by
              intro hiT
              have hip : parent i = q := (Finset.mem_filter.mp hi).2
              exact hn (hip ▸ Finset.mem_image_of_mem parent (hTF hiT))
            change volume (zeroExtend T (fun i => (Y i).toTube) Ylast i).shade = 0
            rw [zeroExtend_shade_of_not_mem hiT, measure_empty]
          exact htq.ne' htzero
        have hhpos : 0 < h q := htq.trans_le ((htm q).trans (hmh q))
        have hhfinite : h q < ⊤ :=
          (Finset.single_le_sum (fun _ _ => zero_le) hq).trans_lt hHfinite
        refine ⟨q, hqF, ?_, ⟨?_, hcut⟩⟩
        · change ((r / 4 : NNReal) : ENNReal) *
              ((∑ i ∈ A, volume (Y i).shade) / (∑ i ∈ A, volume (Y i).carrier)) <=
              m q / (∑ i ∈ fibre q, volume (Zfirst i).carrier)
          have hden : (∑ i ∈ fibre q, volume (Zfirst i).carrier) = h q :=
            Finset.sum_congr rfl (fun i hi => congrArg (fun V : ConvexSpaceBody E => volume V.carrier) (hfirst_body i))
          rw [hden]
          apply (ENNReal.le_div_iff_mul_le (Or.inl hhpos.ne') (Or.inl hhfinite.ne)).mpr
          rwa [hsumH] at hfull
        · refine ⟨Finset.Subset.refl _, fun i hi => ⟨?_, hlast_sub i⟩⟩
          exact (hlast_body i).trans (hfirst_body i).symm
      have hnormalized_parent_shading {iota : Type uI} [DecidableEq iota]
          {rho : NNReal} (H : Finset iota) (Z : iota -> ShadedTube rho E)
          (mass : iota -> ENNReal) (c : NNReal)
          (hlower : ∀ Q ∈ H, (c : ENNReal) * mass Q <= volume (Z Q).shade)
          (hupper : ∀ Q ∈ H, volume (Z Q).shade <= 2 * (c : ENNReal) * mass Q) :
          ∃ Zmid : iota -> ShadedTube rho E,
            (∀ Q, (Zmid Q).toTube = (Z Q).toTube) ∧
            (∀ Q ∈ H, (Zmid Q).shade ⊆ (Z Q).shade) ∧
            (∀ Q ∈ H, volume (Zmid Q).shade = (c : ENNReal) * mass Q) ∧
            IsCRefinement H (fun Q => (Zmid Q).toShadedBody)
              H (fun Q => (Z Q).toShadedBody) (1 / 2) := by
        have hcuts (Q : iota) (hQ : Q ∈ H) :
            ∃ S : Set E, S ⊆ (Z Q).shade ∧ MeasurableSet S ∧
              volume S = (c : ENNReal) * mass Q :=
          exists_volume_cut_w97 (Z Q).shade (Z Q).measurableSet_shade
            ((measure_mono (Z Q).shade_subset).trans_lt
              (lt_top_iff_ne_top.mpr (Z Q).isCompact.measure_ne_top)) (c * mass Q) (hlower Q hQ)
        let Zmid : iota -> ShadedTube rho E := fun Q =>
          if hQ : Q ∈ H then
            { toTube := (Z Q).toTube
              shade := (hcuts Q hQ).choose
              measurableSet_shade := (hcuts Q hQ).choose_spec.2.1
              shade_subset := (hcuts Q hQ).choose_spec.1.trans (Z Q).shade_subset }
          else
            { toTube := (Z Q).toTube
              shade := ∅
              measurableSet_shade := MeasurableSet.empty
              shade_subset := Set.empty_subset _ }
        have htube (Q : iota) : (Zmid Q).toTube = (Z Q).toTube := by
          dsimp [Zmid]
          split <;> rfl
        have hshade (Q : iota) (hQ : Q ∈ H) : (Zmid Q).shade ⊆ (Z Q).shade := by
          simpa only [Zmid, dif_pos hQ] using (hcuts Q hQ).choose_spec.1
        have hmass (Q : iota) (hQ : Q ∈ H) :
            volume (Zmid Q).shade = (c : ENNReal) * mass Q := by
          simpa only [Zmid, dif_pos hQ] using (hcuts Q hQ).choose_spec.2.2
        refine ⟨Zmid, htube, hshade, hmass,
          ⟨⟨Finset.Subset.refl _, fun Q hQ =>
            ⟨congrArg Tube.toConvexSpaceBody (htube Q), hshade Q hQ⟩⟩, ?_⟩⟩
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro Q hQ
        rw [hmass Q hQ]
        calc
          (((1 / 2 : NNReal) : ENNReal) * volume (Z Q).shade) <=
              (((1 / 2 : NNReal) : ENNReal) * (2 * (c : ENNReal) * mass Q)) :=
            mul_le_mul' le_rfl (hupper Q hQ)
          _ = ((((1 / 2 : NNReal) : ENNReal) * 2) * (c : ENNReal)) * mass Q := by ring
          _ = (c : ENNReal) * mass Q := by
            have hhalf : (((1 / 2 : NNReal) : ENNReal) * 2) = 1 := by
              exact_mod_cast (show (1 / 2 : NNReal) * 2 = 1 by norm_num)
            rw [hhalf, one_mul]
      have hactual_coarse_assign {iota : Type uI} [DecidableEq iota]
          {delta : NNReal} (A : Finset iota) (Y : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
          (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
          (a b : Nat) (hab : a < b) (hb : b <= M) :
          ∃ parent : iota -> iota,
            (∀ i ∈ A, parent (U.cover.assign b i) = U.cover.assign a i) ∧
            (∀ Q ∈ U.cover.indexSet b, parent Q ∈ U.cover.indexSet a) ∧
            (∀ Q ∈ U.cover.indexSet b,
              (U.cover.tube b Q).toConvexSpaceBody <= (U.cover.tube a (parent Q)).toConvexSpaceBody) := by
        let parent : iota -> iota := fun Q => if hQ : Q ∈ A.image (U.cover.assign b) then
          U.cover.assign a (Finset.mem_image.mp hQ).choose else Q
        have hparent : ∀ i ∈ A, parent (U.cover.assign b i) = U.cover.assign a i := by
          intro i hi
          have hQ : U.cover.assign b i ∈ A.image (U.cover.assign b) := Finset.mem_image_of_mem _ hi
          dsimp only [parent]
          rw [dif_pos hQ]
          exact U.cover.assign_eq_of_le hab.le hb
            (Finset.mem_image.mp hQ).choose_spec.1 hi (Finset.mem_image.mp hQ).choose_spec.2
        refine ⟨parent, hparent, ?_, ?_⟩
        · intro Q hQ
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((hregular.surjective b hb).symm ▸ hQ)
          rw [hparent i hi]
          exact U.cover.assign_mem a (by omega) i hi
        · intro Q hQ
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((hregular.surjective b hb).symm ▸ hQ)
          rw [hparent i hi]
          exact U.cover.toChain.tube_assign_le hab.le hb hi
      have hactual_first_raw {iota : Type uI} [DecidableEq iota]
          {delta : NNReal} (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
          (A : Finset iota) (Y : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
          (b : Nat) (hb : b <= M)
          (hball : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
          (hmass : 0 < ∑ i ∈ A, volume (Y i).shade) :
          ∃ (F : ShadedBody.FactorFamily E iota iota)
            (G : ShadedBody.ShadedFactorFamily E iota iota),
            F.innerSet = A ∧ F.outerSet = U.cover.indexSet b ∧
            F.parent = U.cover.assign b ∧ F.innerBody = (fun i => (Y i).toShadedBody) ∧
            F.outerBody = (fun Q => (U.cover.tube b Q).toConvexSpaceBody) ∧
            Nonempty (ActualRawRhoStatisticsW97 F Y (U.cover.tube b) G) := by
        let F : ShadedBody.FactorFamily E iota iota :=
          { innerSet := A
            innerBody := fun i => (Y i).toShadedBody
            outerSet := U.cover.indexSet b
            outerBody := fun Q => (U.cover.tube b Q).toConvexSpaceBody
            parent := U.cover.assign b
            parent_mem := U.cover.assign_mem b hb
            inner_le_parent := U.cover.le_tube_assign b hb }
        have hscale : delta <= Tube.gridScale delta M b := by
          simpa only [Tube.gridScale_self delta hM] using Tube.gridScale_antitone hdelta hdeltaOne M hb
        obtain ⟨G, hraw⟩ := exists_raw_rho_factorization_with_fibre_statistics_w97
          hdelta hscale (Tube.gridScale_le_one hdeltaOne M b) F Y (U.cover.tube b)
          (fun _ _ => rfl) (fun _ _ => rfl) hball hmass
        exact ⟨F, G, rfl, rfl, rfl, rfl, rfl, hraw⟩
      have hwhole_parent_realization :
          ∃ Cgeom : NNReal, 1 <= Cgeom ∧
            ∀ {iota : Type uI} [DecidableEq iota] {delta rho : NNReal},
              0 < delta -> delta <= rho -> rho <= 1 ->
            ∀ (F : ShadedBody.FactorFamily E iota iota)
              (T : iota -> ShadedTube delta E) (Trho : iota -> Tube rho E)
              (G : ShadedBody.ShadedFactorFamily E iota iota)
              (raw : ActualRawRhoStatisticsW97 F T Trho G)
              (H : Finset iota) (r : NNReal),
              (∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody) ->
              H ⊆ G.outerSet -> 0 < r -> r <= 1 ->
              (r : ENNReal) * (∑ Q ∈ G.outerSet, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) <=
                ∑ Q ∈ H, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade ->
              let fine := G.innerSet.filter (fun i => G.parent i ∈ H)
              let Lraw := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank Real E) F.innerSet.card delta 1
              ∃ (W : iota -> ShadedTube delta E) (Z : iota -> ShadedTube rho E),
                H.Nonempty ∧ fine.Nonempty ∧ fine ⊆ F.innerSet ∧ fine.image G.parent = H ∧
                (∀ i, (W i).toTube = (T i).toTube) ∧ (∀ Q, (Z Q).toTube = Trho Q) ∧
                (∀ i ∈ F.innerSet, (W i).shade = (G.innerBody i).shade) ∧
                (∀ Q ∈ G.outerSet, (Z Q).shade = (G.outerBody Q).shade) ∧
                (∀ i ∈ fine, (W i).shade ⊆ (T i).shade ∧ (W i).shade ⊆ (Z (G.parent i)).shade) ∧
                (r : ENNReal) * (Lraw : ENNReal)⁻¹ *
                  (∑ i ∈ F.innerSet, volume (T i).shade) <= ∑ i ∈ fine, volume (W i).shade ∧
                (∀ Q ∈ H, ShadedBody.multiplicity F.innerSet (fun i => (T i).toShadedBody) <=
                  (Cgeom : ENNReal) * (Lraw : ENNReal) ^ (2 : Nat) / (r : ENNReal) *
                    ShadedBody.multiplicity H (fun Q => (Z Q).toShadedBody) *
                    ShadedBody.multiplicity (completeFibreW94 fine G.parent Q)
                      (fun i => (W i).toShadedBody)) ∧
                (2 * (sourceRawCrossCostW97 (Module.finrank Real E) : ENNReal))⁻¹ *
                  fullness' fine (fun i => (W i).toShadedBody) <=
                    fullness' H (fun Q => (Z Q).toShadedBody) := by
        obtain ⟨Cgeom, hCgeom, hstable⟩ := raw_parent_subset_scalar_and_fullness_w97 (E := E)
        refine ⟨Cgeom, hCgeom, ?_⟩
        intro iota inst delta rho hdelta hdrho hrho F T Trho G raw H r hinner hH hr hr1 hretained
        dsimp only
        let fine := G.innerSet.filter (fun i => G.parent i ∈ H)
        have hfineG : fine ⊆ G.innerSet := Finset.filter_subset _ _
        have hfineF : fine ⊆ F.innerSet := hfineG.trans raw.raw_refinement.1.1
        obtain ⟨hHne, hfinene, hfibres, hscalar, hfull⟩ :=
          hstable hdelta hdrho hrho F T Trho G raw H r hH
            (ENNReal.coe_pos.mpr hr) (by exact_mod_cast hr1) hretained
        let W : iota -> ShadedTube delta E := fun i => if hi : i ∈ F.innerSet then
          { toTube := (T i).toTube
            shade := (G.innerBody i).shade
            measurableSet_shade := (G.innerBody i).measurableSet_shade
            shade_subset := by
              change (G.innerBody i).shade ⊆ (T i).carrier
              rw [← raw.inner_body i hi]
              exact (G.innerBody i).shade_subset }
          else
            { toTube := (T i).toTube
              shade := ∅
              measurableSet_shade := MeasurableSet.empty
              shade_subset := Set.empty_subset _ }
        let Z : iota -> ShadedTube rho E := fun Q => if hQ : Q ∈ G.outerSet then
          { toTube := Trho Q
            shade := (G.outerBody Q).shade
            measurableSet_shade := (G.outerBody Q).measurableSet_shade
            shade_subset := by
              change (G.outerBody Q).shade ⊆ (Trho Q).carrier
              rw [← raw.outer_body Q hQ]
              exact (G.outerBody Q).shade_subset }
          else
            { toTube := Trho Q
              shade := ∅
              measurableSet_shade := MeasurableSet.empty
              shade_subset := Set.empty_subset _ }
        have hWtube (i : iota) : (W i).toTube = (T i).toTube := by
          dsimp [W]; split <;> rfl
        have hZtube (Q : iota) : (Z Q).toTube = Trho Q := by
          dsimp [Z]; split <;> rfl
        have hWshade (i : iota) (hi : i ∈ F.innerSet) : (W i).shade = (G.innerBody i).shade := by
          simp only [W, dif_pos hi]
        have hZshade (Q : iota) (hQ : Q ∈ G.outerSet) : (Z Q).shade = (G.outerBody Q).shade := by
          simp only [Z, dif_pos hQ]
        have himage : fine.image G.parent = H := by
          ext Q
          constructor
          · intro hQ
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
            exact (Finset.mem_filter.mp hi).2
          · intro hQ
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (raw.inner_image.symm ▸ hH hQ)
            exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hQ⟩, rfl⟩
        have hmass_fine : (∑ i ∈ fine, volume (W i).shade) =
            ∑ Q ∈ H, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade := by
          calc
            _ = ∑ i ∈ fine, volume (G.innerBody i).shade :=
              Finset.sum_congr rfl (fun i hi => congrArg volume (hWshade i (hfineF hi)))
            _ = ∑ Q ∈ H, ∑ i ∈ completeFibreW94 fine G.parent Q, volume (G.innerBody i).shade :=
              (Finset.sum_fiberwise_of_maps_to (fun i hi => (Finset.mem_filter.mp hi).2) _).symm
            _ = _ := Finset.sum_congr rfl (fun Q hQ => by rw [hfibres Q hQ])
        have hmass_raw : (∑ Q ∈ G.outerSet, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) =
            ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
          have hgfibre (Q : iota) : G.fiber Q = G.innerSet.filter (fun i => G.parent i = Q) := by
            ext i
            simp only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter]
          simp_rw [hgfibre]
          exact Finset.sum_fiberwise_of_maps_to G.parent_mem (fun i => volume (G.innerBody i).shade)
        have hmass_input : (∑ i ∈ F.innerSet, volume (F.innerBody i).shade) =
            ∑ i ∈ F.innerSet, volume (T i).shade :=
          Finset.sum_congr rfl (fun i hi => congrArg (fun V : ShadedBody E => volume V.shade) (hinner i hi))
        refine ⟨W, Z, hHne, hfinene, hfineF, himage, hWtube, hZtube, hWshade, hZshade, ?_, ?_, ?_, ?_⟩
        · intro i hi
          rw [hWshade i (hfineF hi), hZshade _ (G.parent_mem i (hfineG hi))]
          refine ⟨?_, G.shade_subset_parent i (hfineG hi)⟩
          have h := (raw.raw_refinement.1.2 i (hfineG hi)).2
          rwa [hinner i (hfineF hi)] at h
        · rw [hmass_fine]
          have hraw := raw.raw_refinement.2
          have hLne : ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank Real E) F.innerSet.card delta 1 ≠ 0 :=
            (zero_lt_one.trans_le (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _)).ne'
          rw [hmass_input, ENNReal.coe_inv hLne] at hraw
          calc
            _ <= (r : ENNReal) * (∑ i ∈ G.innerSet, volume (G.innerBody i).shade) := by
              rw [mul_assoc]
              exact mul_le_mul' le_rfl hraw
            _ = (r : ENNReal) * (∑ Q ∈ G.outerSet, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) :=
              congrArg ((r : ENNReal) * ·) hmass_raw.symm
            _ <= _ := hretained
        · intro Q hQ
          have hinput := _root_.Tube.multiplicity_congr_of_shading_eq F.innerSet
            F.innerBody (fun i => (T i).toShadedBody)
            (fun i hi => congrArg ShadedBody.shade (hinner i hi).symm)
          have houter := _root_.Tube.multiplicity_congr_of_shading_eq H
            G.outerBody (fun Q => (Z Q).toShadedBody) (fun Q hQ => hZshade Q (hH hQ))
          have hchild := _root_.Tube.multiplicity_congr_of_shading_eq
            (completeFibreW94 fine G.parent Q) G.innerBody (fun i => (W i).toShadedBody)
            (fun i hi => hWshade i (hfineF (Finset.mem_filter.mp hi).1))
          rw [houter, hchild, hfibres Q hQ, hinput]
          exact hscalar Q hQ
        · have hWbody (i : iota) (hi : i ∈ fine) : (W i).toShadedBody = G.innerBody i := by
            apply ShadedBody.ext_of_toConvexSpaceBody_eq
            · exact (congrArg Tube.toConvexSpaceBody (hWtube i)).trans (raw.inner_body i (hfineF hi)).symm
            · exact hWshade i (hfineF hi)
          have hZbody (Q : iota) (hQ : Q ∈ H) : (Z Q).toShadedBody = G.outerBody Q := by
            apply ShadedBody.ext_of_toConvexSpaceBody_eq
            · exact (congrArg Tube.toConvexSpaceBody (hZtube Q)).trans (raw.outer_body Q (hH hQ)).symm
            · exact hZshade Q (hH hQ)
          have hWF : fullness' fine (fun i => (W i).toShadedBody) = fullness' fine G.innerBody := by
            unfold fullness'
            congr 1
            · exact Finset.sum_congr rfl (fun i hi => congrArg (fun V : ShadedBody E => volume V.shade) (hWbody i hi))
            · exact Finset.sum_congr rfl (fun i hi => congrArg (fun V : ShadedBody E => volume V.carrier) (hWbody i hi))
          have hZF : fullness' H (fun Q => (Z Q).toShadedBody) = fullness' H G.outerBody := by
            unfold fullness'
            congr 1
            · exact Finset.sum_congr rfl (fun Q hQ => congrArg (fun V : ShadedBody E => volume V.shade) (hZbody Q hQ))
            · exact Finset.sum_congr rfl (fun Q hQ => congrArg (fun V : ShadedBody E => volume V.carrier) (hZbody Q hQ))
          rwa [hWF, hZF]
      have hactual_second_selected :
          ∃ Kpatch : Nat, 1 <= Kpatch ∧
            ∀ {iota : Type uI} [DecidableEq iota] {rho theta : NNReal},
              0 < rho -> rho <= 1 / 16 -> rho <= theta -> theta <= 1 ->
            ∀ (amb H : Finset iota) (Z : iota -> ShadedTube rho E)
              (Tmid : iota -> Tube rho E) (J : Finset iota)
              (Ttheta : iota -> Tube theta E) (parent : iota -> iota)
              (m : iota -> ENNReal) (c : NNReal),
              H ⊆ amb -> (∀ i ∈ H, (Z i).toTube = Tmid i) -> 0 < c ->
              0 < ∑ i ∈ H, volume (Z i).shade ->
              (∀ i ∈ H, volume (Z i).shade = (c : ENNReal) * m i) ->
              (∀ i ∈ H, (Z i).carrier ⊆ Metric.closedBall 0 2) ->
              H.image parent ⊆ J ->
              (∀ i ∈ H, (Z i).toConvexSpaceBody <= (Ttheta (parent i)).toConvexSpaceBody) ->
              ∃ (mid F2 P2 : Finset iota)
                (Y2 : iota -> ShadedTube rho E) (Z2 : iota -> ShadedTube theta E)
                (label : iota) (lamP lamF : NNReal),
                mid.Nonempty ∧ mid ⊆ H ∧ F2.Nonempty ∧
                (∑ i ∈ H, volume (Z i).shade) <= (Kpatch : ENNReal) * ∑ i ∈ mid, volume (Z i).shade ∧
                (∑ i ∈ H, m i) <= (Kpatch : ENNReal) * ∑ i ∈ mid, m i ∧
                IsOneScaleSelected
                  ((ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
                    (Module.finrank Real E) mid.card rho 1 : NNReal) : ENNReal)⁻¹
                  (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
                    (Module.finrank Real E) mid.card rho 1 : ENNReal)
                  amb mid (zeroExtend mid Tmid Z) J Ttheta parent F2 Y2 P2 Z2 label lamP lamF ∧
                (2 * (sourceRawCrossCostW97 (Module.finrank Real E) : ENNReal))⁻¹ *
                  fullness' F2 (fun i => (Y2 i).toShadedBody) <=
                    fullness' P2 (fun Q => (Z2 Q).toShadedBody) ∧
                ∃ rawWitness : ActualSecondRawWitnessW99 H Z J Ttheta parent m c,
                  rawWitness.mid = mid := by
        obtain ⟨Kpatch, hKpatch, hpatch⟩ := exists_bounded_ball_patch_second_factor_w97 (E := E)
        refine ⟨Kpatch, hKpatch, ?_⟩
        intro iota inst rho theta hrho hrhoSmall hrhotheta htheta amb H Z Tmid J Ttheta parent m c
          hHamb hZtube hc hmass hinduced hball hparents hcontain
        obtain ⟨mid, z, FF, G, Yi, Yo, hmidne, hmidH, hpatchMass, hpatchWeight,
          hcentres, htranslatedBall, hFFinner, hFFouter, hFFparent, hFFinnerBody, hFFouterBody,
          ⟨raw⟩, hYi, hYo, hscalar⟩ :=
          hpatch hrho hrhoSmall hrhotheta htheta H Z J Ttheta parent m c
            hc hmass hinduced hball hparents hcontain
        let L := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
          (Module.finrank Real E) mid.card rho 1
        let V := zeroExtend mid Tmid Z
        have hLone : 1 <= L := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _
        have hLpos : 0 < (L : ENNReal) := ENNReal.coe_pos.mpr (zero_lt_one.trans_le hLone)
        have hmidamb : mid ⊆ amb := hmidH.trans hHamb
        have hinner : G.innerSet ⊆ mid := hFFinner ▸ raw.raw_refinement.1.1
        have hinneramb : G.innerSet ⊆ amb := hinner.trans hmidamb
        have houter : G.outerSet ⊆ J := by
          intro Q hQ
          have hmem := raw.outer_subset hQ
          rw [hFFouter] at hmem
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
          exact hparents (Finset.mem_image_of_mem parent (hmidH hi))
        have hparent : G.parent = parent := raw.parent_eq.trans hFFparent
        have hmaps : ∀ i ∈ G.innerSet, parent i ∈ G.outerSet := by
          intro i hi
          rw [← hparent]
          exact G.parent_mem i hi
        have hVtube (i : iota) : (V i).toTube = Tmid i :=
          zeroExtend_toTube (fun i hi => hZtube i (hmidH hi)) i
        have hchildTube : ∀ i ∈ G.innerSet, (Yi i).toTube = (V i).toTube := by
          intro i hi
          rw [hVtube, (hYi i hi).1, hZtube i (hmidH (hinner hi))]
        have hchildShade : ∀ i ∈ G.innerSet, (Yi i).shade ⊆ (V i).shade := by
          intro i hi
          change (Yi i).shade ⊆ (zeroExtend mid Tmid Z i).shade
          rw [zeroExtend_shade_of_mem (hinner hi)]
          exact (hYi i hi).2.2
        have hvoltranslate (S : ShadedBody E) (v : E) : volume (S.translate v).shade = volume S.shade := by
          change volume ((v + ·) '' S.shade) = volume S.shade
          exact measure_image_add volume v S.shade
        have hmassYi : (∑ i ∈ G.innerSet, volume (Yi i).shade) =
            ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
          apply Finset.sum_congr rfl
          intro i hi
          change volume (Yi i).toShadedBody.shade = _
          rw [(hYi i hi).2.1, hvoltranslate]
        have hmassFF : (∑ i ∈ FF.innerSet, volume (FF.innerBody i).shade) =
            ∑ i ∈ mid, volume (Z i).shade := by
          rw [hFFinner, hFFinnerBody]
          exact Finset.sum_congr rfl (fun i hi => hvoltranslate (Z i).toShadedBody (-z))
        have hretained : (L : ENNReal)⁻¹ * (∑ i ∈ mid, volume (Z i).shade) <=
            ∑ i ∈ G.innerSet, volume (Yi i).shade := by
          have hraw := raw.raw_refinement.2
          rw [hmassFF, hFFinner, ENNReal.coe_inv (zero_lt_one.trans_le hLone).ne'] at hraw
          rw [hmassYi]
          exact hraw
        have hmidmass : 0 < ∑ i ∈ mid, volume (Z i).shade := by
          by_contra hn
          have hz := not_lt.mp hn
          have hzero : (∑ i ∈ mid, volume (Z i).shade) = 0 := le_antisymm hz bot_le
          rw [hzero, mul_zero] at hpatchMass
          exact (not_lt_of_ge hpatchMass) hmass
        have hchildmass : 0 < ∑ i ∈ G.innerSet, volume (Yi i).shade :=
          (ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) hmidmass.ne').trans_le hretained
        have hchildne : G.innerSet.Nonempty := by
          by_contra hn
          rw [Finset.not_nonempty_iff_eq_empty] at hn
          simp only [hn, Finset.sum_empty, lt_self_iff_false] at hchildmass
        obtain ⟨label, hlabel, hfibreNe, hselected⟩ :=
          exists_selected_fibre hrho hinneramb hmaps (fun i => (V i).toTube) Yi hchildmass
        let W := selectedShade G.innerSet V Yi
        have hWtube (i : iota) : (W i).toTube = (V i).toTube := selectedShade_toTube hchildTube i
        have hglobal : (L : ENNReal)⁻¹ * fullness' amb (fun i => (V i).toShadedBody) <=
            fullness' amb (fun i => (W i).toShadedBody) := by
          have hVmass := sum_volume_shade_zeroExtend_of_subset hmidamb Tmid Z
          have hWmass : (∑ i ∈ amb, volume (W i).shade) = ∑ i ∈ G.innerSet, volume (Yi i).shade := by
            change (∑ i ∈ amb, volume (zeroExtend G.innerSet (fun i => (V i).toTube) Yi i).shade) = _
            exact sum_volume_shade_zeroExtend_of_subset hinneramb (fun i => (V i).toTube) Yi
          have hden : (∑ i ∈ amb, volume (W i).carrier) = ∑ i ∈ amb, volume (V i).carrier :=
            Finset.sum_congr rfl (fun i hi => congrArg (fun T : Tube rho E => volume T.carrier) (hWtube i))
          change (L : ENNReal)⁻¹ * ((∑ i ∈ amb, volume (V i).shade) /
            (∑ i ∈ amb, volume (V i).carrier)) <=
            (∑ i ∈ amb, volume (W i).shade) / (∑ i ∈ amb, volume (W i).carrier)
          rw [hVmass, hWmass, hden, ← mul_div_assoc]
          exact ENNReal.div_le_div_right hretained _
        obtain ⟨Cgeom, hCgeom, hstable⟩ := raw_parent_subset_scalar_and_fullness_w97 (E := E)
        have hstableAll := hstable hrho hrhotheta htheta FF
          (fun i => (Z i).translate (-z)) (fun Q => (Ttheta Q).translate (-z))
          G raw G.outerSet 1 (Finset.Subset.refl _) zero_lt_one le_rfl (by simp only [one_mul]; exact le_rfl)
        have hfineAll : G.innerSet.filter (fun i => G.parent i ∈ G.outerSet) = G.innerSet :=
          Finset.filter_eq_self.mpr G.parent_mem
        rw [hfineAll] at hstableAll
        have hfullTransport {s : NNReal} (H : Finset iota) (Zs : iota -> ShadedTube s E)
            (W : iota -> ShadedBody E) (hZW : ∀ i ∈ H, (Zs i).toShadedBody = (W i).translate z) :
            fullness' H (fun i => (Zs i).toShadedBody) = fullness' H W := by
          calc
            _ = fullness' H (fun i => (W i).translate z) := by
              unfold fullness'
              congr 1
              · exact Finset.sum_congr rfl (fun i hi => congrArg (fun V : ShadedBody E => volume V.shade) (hZW i hi))
              · exact Finset.sum_congr rfl (fun i hi => congrArg (fun V : ShadedBody E => volume V.carrier) (hZW i hi))
            _ = _ := by
              rw [← ShadedBody.coe_fullness, ← ShadedBody.coe_fullness,
                ShadedBody.fullness_translate_const]
        have hcoarseActive : (2 * (sourceRawCrossCostW97 (Module.finrank Real E) : ENNReal))⁻¹ *
              fullness' G.innerSet (fun i => (Yi i).toShadedBody) <=
                fullness' G.outerSet (fun Q => (Yo Q).toShadedBody) := by
          rw [hfullTransport G.innerSet Yi G.innerBody (fun i hi => (hYi i hi).2.1),
            hfullTransport G.outerSet Yo G.outerBody (fun Q hQ => (hYo Q hQ).2)]
          exact hstableAll.2.2.2.2
        let rawWitness : ActualSecondRawWitnessW99 H Z J Ttheta parent m c :=
          { mid := mid
            z := z
            FF := FF
            G := G
            Yi := Yi
            Yo := Yo
            mid_nonempty := hmidne
            mid_subset := hmidH
            FF_inner := hFFinner
            FF_outer := hFFouter
            FF_parent := hFFparent
            FF_innerBody := hFFinnerBody
            FF_outerBody := hFFouterBody
            raw := raw
            Yi_transport := hYi
            Yo_transport := hYo
            scalar := hscalar }
        refine ⟨mid, G.innerSet, G.outerSet, Yi, Yo, label,
          ShadedBody.fullness G.outerSet (fun Q => (Yo Q).toShadedBody),
          ShadedBody.fullness (fibre amb parent label) (fun i => (W i).toShadedBody),
          hmidne, hmidH, hchildne, hpatchMass, hpatchWeight, ?_, hcoarseActive,
          ⟨rawWitness, rfl⟩⟩
        refine
          { active_subset := hmidamb
            shade_off := fun i hi hnot => zeroExtend_shade_of_not_mem hnot
            child_subset := hinner
            child_shade := fun i hi => ⟨hchildTube i hi, hchildShade i hi⟩
            child_retention := ?_
            parent_subset := houter
            parent_mapsTo := hmaps
            parent_tube := fun Q hQ => (hYo Q hQ).1
            parent_contain := ?_
            parent_fullness := le_rfl
            scalar := ?_
            sel_mem := hlabel
            sel_nonempty := hfibreNe
            sel_fullness := le_rfl
            sel_fullness_lb := ?_ }
        · have hsame : (∑ i ∈ mid, volume (V i).shade) = ∑ i ∈ mid, volume (Z i).shade :=
            sum_volume_shade_zeroExtend_of_subset (Finset.Subset.refl mid) Tmid Z
          rw [hsame]
          exact hretained
        · intro i hi
          change (Yi i).toShadedBody.shade ⊆ (Yo (parent i)).toShadedBody.shade
          rw [(hYi i hi).2.1, (hYo (parent i) (hmaps i hi)).2]
          change (z + ·) '' (G.innerBody i).shade ⊆ (z + ·) '' (G.outerBody (parent i)).shade
          apply Set.image_mono
          rw [← hparent]
          exact G.shade_subset_parent i hi
        · intro Q hQ
          rw [multiplicity_zeroExtend_of_subset hmidamb Tmid Z]
          have hfibre : fibre G.innerSet parent Q = G.fiber Q := by
            ext i
            simp only [fibre, ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter, hparent]
          rw [hfibre]
          exact hscalar Q hQ
        · rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
          rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness] at hselected
          exact hglobal.trans hselected
      have hsame_cut_funding {iota : Type uI} [DecidableEq iota] {delta rho : NNReal}
          (F : Finset iota) (Yfirst : iota -> ShadedTube delta E)
          (H mid F2 : Finset iota) (Z Yi : iota -> ShadedTube rho E)
          (parent : iota -> iota) (c K L : NNReal)
          (hc : 0 < c) (hK : 1 <= K) (hL : 1 <= L)
          (hmidH : mid ⊆ H) (hF2 : F2.Nonempty) (hF2mid : F2 ⊆ mid)
          (himage : F.image parent = H)
          (hinduced : ∀ Q ∈ H, volume (Z Q).shade = (c : ENNReal) *
            ∑ i ∈ completeFibreW94 F parent Q, volume (Yfirst i).shade)
          (hsecond : ∀ Q ∈ F2, (Yi Q).toTube = (Z Q).toTube ∧ (Yi Q).shade ⊆ (Z Q).shade)
          (hpatch : (∑ Q ∈ H, ∑ i ∈ completeFibreW94 F parent Q, volume (Yfirst i).shade) <=
            (K : ENNReal) * ∑ Q ∈ mid, ∑ i ∈ completeFibreW94 F parent Q, volume (Yfirst i).shade)
          (hretained : (L : ENNReal)⁻¹ * (∑ Q ∈ mid, volume (Z Q).shade) <=
            ∑ Q ∈ F2, volume (Yi Q).shade) :
          ∃ (Fdagger : Finset iota) (Ydagger : iota -> ShadedTube delta E),
            Fdagger = F.filter (fun i => parent i ∈ F2) ∧ Fdagger.Nonempty ∧ Fdagger ⊆ F ∧
            Fdagger.image parent = F2 ∧
            (∀ i ∈ Fdagger, (Ydagger i).toTube = (Yfirst i).toTube ∧ (Ydagger i).shade ⊆ (Yfirst i).shade) ∧
            (∀ Q ∈ F2, (∑ i ∈ completeFibreW94 Fdagger parent Q, volume (Ydagger i).shade) =
              (c : ENNReal)⁻¹ * volume (Yi Q).shade) ∧
            (((K * L)⁻¹ : NNReal) : ENNReal) * (∑ i ∈ F, volume (Yfirst i).shade) <=
              ∑ i ∈ Fdagger, volume (Ydagger i).shade := by
        obtain ⟨Fdagger, Ydagger, hFdagger, hFdaggerNe, hFdaggerF, hdaggerImage,
          hdaggerShade, hfibres, hcut, hpointwise⟩ :=
          exists_same_proportional_fine_cut_w97 F Yfirst H F2 Z Yi parent
            hF2 (hF2mid.trans hmidH) himage c hc hinduced hsecond
        let m := fun Q => ∑ i ∈ completeFibreW94 F parent Q, volume (Yfirst i).shade
        have hsumF : (∑ i ∈ F, volume (Yfirst i).shade) = ∑ Q ∈ H, m Q :=
          (Finset.sum_fiberwise_of_maps_to
            (fun i hi => himage ▸ Finset.mem_image_of_mem parent hi) (fun i => volume (Yfirst i).shade)).symm
        have hsumZ : (∑ Q ∈ mid, volume (Z Q).shade) = (c : ENNReal) * ∑ Q ∈ mid, m Q := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun Q hQ => hinduced Q (hmidH hQ))
        have hsumCut : (∑ i ∈ Fdagger, volume (Ydagger i).shade) =
            (c : ENNReal)⁻¹ * ∑ Q ∈ F2, volume (Yi Q).shade := by
          calc
            _ = ∑ Q ∈ F2, ∑ i ∈ completeFibreW94 Fdagger parent Q, volume (Ydagger i).shade :=
              (Finset.sum_fiberwise_of_maps_to
                (fun i hi => hdaggerImage ▸ Finset.mem_image_of_mem parent hi)
                (fun i => volume (Ydagger i).shade)).symm
            _ = ∑ Q ∈ F2, (c : ENNReal)⁻¹ * volume (Yi Q).shade :=
              Finset.sum_congr rfl hcut
            _ = _ := (Finset.mul_sum _ _ _).symm
        have hcancel : (c : ENNReal)⁻¹ * (c : ENNReal) = 1 :=
          ENNReal.inv_mul_cancel (ENNReal.coe_pos.mpr hc).ne' ENNReal.coe_ne_top
        have hcutMass : (L : ENNReal)⁻¹ * (∑ Q ∈ mid, m Q) <=
            ∑ i ∈ Fdagger, volume (Ydagger i).shade := by
          calc
            _ = ((c : ENNReal)⁻¹ * (c : ENNReal)) * ((L : ENNReal)⁻¹ * (∑ Q ∈ mid, m Q)) := by
              rw [hcancel, one_mul]
            _ = (c : ENNReal)⁻¹ * ((L : ENNReal)⁻¹ * ((c : ENNReal) * ∑ Q ∈ mid, m Q)) := by ring
            _ = (c : ENNReal)⁻¹ * ((L : ENNReal)⁻¹ * ∑ Q ∈ mid, volume (Z Q).shade) := by rw [hsumZ]
            _ <= (c : ENNReal)⁻¹ * (∑ Q ∈ F2, volume (Yi Q).shade) := mul_le_mul' le_rfl hretained
            _ = _ := hsumCut.symm
        have hKne : K ≠ 0 := (zero_lt_one.trans_le hK).ne'
        have hLne : L ≠ 0 := (zero_lt_one.trans_le hL).ne'
        have hpatchMass : (K : ENNReal)⁻¹ * (∑ i ∈ F, volume (Yfirst i).shade) <= ∑ Q ∈ mid, m Q := by
          rw [hsumF]
          exact (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hKne) ENNReal.coe_ne_top).mpr hpatch
        have hcoeff : (((K * L)⁻¹ : NNReal) : ENNReal) = (L : ENNReal)⁻¹ * (K : ENNReal)⁻¹ := by
          rw [mul_inv_rev, ENNReal.coe_mul, ENNReal.coe_inv hLne, ENNReal.coe_inv hKne]
        refine ⟨Fdagger, Ydagger, hFdagger, hFdaggerNe, hFdaggerF, hdaggerImage, hdaggerShade, hcut, ?_⟩
        rw [hcoeff, mul_assoc]
        exact (mul_le_mul' le_rfl hpatchMass).trans hcutMass
      have hraw_polylog (Ccard : Real) (hCcard : 1 <= Ccard) :
          ∃ Craw : NNReal, 1 <= Craw ∧
            ∀ (delta rho : NNReal), 0 < delta -> delta <= rho -> rho <= 1 ->
            ∀ N : Nat, 1 <= N -> (N : Real) <= Ccard * (delta : Real) ^ (-6 : Real) ->
              ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 N rho 1 <=
                Craw * Real.toNNReal ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (6 : Nat)) := by
        let a := Real.logb 2 Ccard
        let b := Real.toNNReal (10 + a)
        let Craw : NNReal := max 1 (max (16000 * b ^ (6 : Nat) * ShadedBody.rhoTubesGeometricLoss 3)
          (ShadedBody.rhoTubesBallLoss 3))
        have ha : 0 <= a := Real.logb_nonneg (by norm_num) hCcard
        have hb : (b : Real) = 10 + a := Real.coe_toNNReal _ (by positivity)
        have hCraw : 1 <= Craw := le_max_left _ _
        refine ⟨Craw, hCraw, ?_⟩
        intro delta rho hdelta hdrho hrho N hN hNcard
        have hd : (0 : Real) < delta := hdelta
        have hr : (0 : Real) < rho := lt_of_lt_of_le hd hdrho
        have hr1 : (rho : Real) <= 1 := hrho
        have hd1 : (delta : Real) <= 1 := hdrho.trans hrho
        have hNpos : (0 : Real) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
        let t := Real.logb 2 (1 / (delta : Real))
        let s := Real.logb 2 (1 / (rho : Real))
        let H : Real := 2 + t
        let Hn := Real.toNNReal H
        have ht : 0 <= t := Real.logb_nonneg (by norm_num) ((one_le_div hd).mpr hd1)
        have hs : 0 <= s := Real.logb_nonneg (by norm_num) ((one_le_div hr).mpr hr1)
        have hst : s <= t := Real.logb_le_logb_of_le (by norm_num) (by positivity)
          (one_div_le_one_div_of_le hd hdrho)
        have hH : 2 <= H := by dsimp [H]; linarith
        have hHn : (Hn : Real) = H := Real.coe_toNNReal _ (by linarith)
        have hHnone : 1 <= Hn := by exact_mod_cast (show (1 : Real) <= Hn by rw [hHn]; linarith)
        have htlog : t = -Real.logb 2 (delta : Real) := by simp only [t, one_div, Real.logb_inv]
        have hlogN : Real.logb 2 (N : Real) <= a + 6 * t := by
          have h : Real.logb 2 (N : Real) <= Real.logb 2 (Ccard * (delta : Real) ^ (-6 : Real)) :=
            Real.logb_le_logb_of_le (by norm_num) hNpos hNcard
          rw [Real.logb_mul (zero_lt_one.trans_le hCcard).ne'
            (Real.rpow_pos_of_pos hd (-6)).ne', Real.logb_rpow_eq_mul_logb_of_pos hd] at h
          dsimp only [a]
          linarith
        have hlog8 : Real.logb 2 (8 : Real) = 3 := by
          rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num, Real.logb_pow,
            Real.logb_self_eq_one (by norm_num)]
          norm_num
        have hlog6 : Real.logb 2 (6 : Real) <= 3 :=
          (Real.logb_le_logb_of_le (by norm_num) (by norm_num) (show (6 : Real) <= 8 by norm_num)).trans_eq hlog8
        have hcommon : 10 + a + 9 * t <= (b : Real) * H := by
          rw [hb]
          dsimp only [H]
          nlinarith [mul_nonneg ha ht]
        have hnatlog : ((Nat.log 2 N + 1 : Nat) : Real) <= (b : Real) * H := by
          have h := Real.natLog_le_logb N 2
          norm_num only [Nat.cast_ofNat] at h
          push_cast
          linarith
        have hnatlogNN : ((Nat.log 2 N + 1 : Nat) : NNReal) <= b * Hn := by
          apply NNReal.coe_le_coe.mp
          simpa only [NNReal.coe_natCast, NNReal.coe_mul, hHn] using hnatlog
        have hstep1 : Kakeya.factoringStep1AtScaleConstant 3 N rho <= 2 * b * Hn := by
          apply NNReal.coe_le_coe.mp
          rw [Kakeya.coe_factoringStep1AtScaleConstant 3 hN (hdelta.trans_le hdrho) hrho]
          norm_num only [Nat.factorial, Nat.cast_ofNat, NNReal.coe_mul, NNReal.coe_ofNat, hHn]
          change 2 * (4 + Real.logb 2 6 + Real.logb 2 N + 3 * s) <= 2 * (b : Real) * H
          nlinarith
        have hstep23 : (Kakeya.factoringStep2Step3Constant N : NNReal) <= 4 * b ^ (4 : Nat) * Hn ^ (4 : Nat) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          push_cast
          calc
            4 * (((Nat.log 2 N : NNReal) + 1) ^ (4 : Nat)) <= 4 * (b * Hn) ^ (4 : Nat) := by
              gcongr
              exact_mod_cast hnatlogNN
            _ = _ := by ring
        let R := ShadedBody.step5PackingRatio 3 N rho
        have hR : R = (8 : NNReal) *
            (Kakeya.step1UpperBdAtScale 3 N / Kakeya.step1LowerBdAtScale 3 rho) := by
          dsimp [R, ShadedBody.step5PackingRatio]
          rw [max_eq_right hN]
          norm_num only [Nat.reducePow]
          ring
        have hratio : (0 : Real) < ((Kakeya.step1UpperBdAtScale 3 N /
            Kakeya.step1LowerBdAtScale 3 rho : NNReal) : Real) := by
          rw [Kakeya.coe_step1UpperBdAtScale_div_step1LowerBdAtScale 3 N (hdelta.trans_le hdrho)]
          positivity
        have hlogR : Real.logb 2 (R : Real) = 6 + Real.logb 2 6 + Real.logb 2 N + 3 * s := by
          rw [hR, NNReal.coe_mul, NNReal.coe_ofNat, Real.logb_mul (by norm_num) hratio.ne', hlog8,
            Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale 3 hN (hdelta.trans_le hdrho)]
          norm_num only [Nat.factorial, Nat.cast_ofNat]
          dsimp only [s]
          ring
        have hbracket : Real.toNNReal (1 + Real.logb 2 (R : Real)) <= b * Hn := by
          apply Real.toNNReal_le_iff_le_coe.mpr
          rw [NNReal.coe_mul, hHn, hlogR]
          linarith
        have hstep5 : ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3 R <= 1000 * b * Hn := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
            Kakeya.factoringStep5OverlapConstant Kakeya.factoringStep1FiberPigeonholeConstant
          norm_num only [Nat.reducePow, Nat.cast_ofNat, NNReal.coe_one, div_one]
          calc
            500 * (2 * Real.toNNReal (1 + Real.logb 2 (R : Real))) <= 500 * (2 * (b * Hn)) := by gcongr
            _ = _ := by ring
        have hmain : 2 * Kakeya.factoringStep1Step2AtScaleConstant 3 N rho *
            (Kakeya.factoringStep3Constant N : NNReal) *
            ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3 R *
            ShadedBody.rhoTubesGeometricLoss 3 <=
            16000 * b ^ (6 : Nat) * ShadedBody.rhoTubesGeometricLoss 3 * Hn ^ (6 : Nat) := by
          calc
            _ = 2 * Kakeya.factoringStep1AtScaleConstant 3 N rho *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant 3 R *
                ShadedBody.rhoTubesGeometricLoss 3 := by
              simp only [Kakeya.factoringStep1Step2AtScaleConstant, Kakeya.factoringStep2Step3Constant, Nat.cast_mul]
              ring
            _ <= 2 * (2 * b * Hn) * (4 * b ^ (4 : Nat) * Hn ^ (4 : Nat)) *
                (1000 * b * Hn) * ShadedBody.rhoTubesGeometricLoss 3 := by gcongr
            _ = _ := by ring
        have hHpow : 1 <= Hn ^ (6 : Nat) := one_le_pow₀ hHnone
        have hbase : Real.toNNReal ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (6 : Nat)) =
            Hn ^ (6 : Nat) := Real.toNNReal_pow (by change 0 <= H; linarith) 6
        rw [hbase]
        unfold ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
        norm_num only [one_pow, one_mul]
        apply max_le
        · exact one_le_mul hCraw hHpow
        · apply max_le
          · exact hmain.trans (mul_le_mul_right' ((le_max_left _ _).trans (le_max_right _ _)) _)
          · exact ((le_max_right _ _).trans (le_max_right _ _)).trans
              (le_mul_of_one_le_right (show (0 : NNReal) <= Craw from zero_le) hHpow)
      have hinput_card {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
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
      have hbottom_line {iota : Type uI} [DecidableEq iota] {delta : NNReal}
          (A : Finset iota) (Y : iota -> ShadedTube delta E)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
          (hregular : SourceRegularizedWorkingTowerW95 U Ctw Ccell) :
          lineEssentiallyDistinctW94 A (fun i => (Y i).toTube) Ctw := by
        intro o v hv
        have h := hregular.parent_line_ed M (Nat.le_refl M) o v hv
        rw [hregular.bottom_index] at h
        have hfilter : A.filter (fun i => liesInFiveDeltaLineTubeW94 (U.cover.tube M i) o v) =
            A.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v) := by
          apply Finset.filter_congr
          intro i hi
          unfold liesInFiveDeltaLineTubeW94
          have hcarrier := congrArg ConvexSpaceBody.carrier (hregular.bottom_tube i hi)
          rw [hcarrier]
          rw [Tube.gridScale_self delta hM]
        rwa [hfilter] at h
      have hone_scale_mono {iota : Type uI} [DecidableEq iota] {delta rho : NNReal}
          {c c' L L' : ENNReal} {amb act child P Q : Finset iota}
          {V W : iota -> ShadedTube delta E} {Z : iota -> ShadedTube rho E}
          {Trho : iota -> Tube rho E} {parent : iota -> iota} {label : iota}
          {lamP lamF : NNReal}
          (h : IsOneScaleSelected c L amb act V P Trho parent child W Q Z label lamP lamF)
          (hc : c' <= c) (hL : L <= L') :
          IsOneScaleSelected c' L' amb act V P Trho parent child W Q Z label lamP lamF := by
        exact { h with
          child_retention := (mul_le_mul' hc le_rfl).trans h.child_retention
          scalar := fun q hq => (h.scalar q hq).trans (mul_le_mul' (mul_le_mul' hL le_rfl) le_rfl)
          sel_fullness_lb := (mul_le_mul' hc le_rfl).trans h.sel_fullness_lb }
      let hselection_mono {iota : Type uI} [DecidableEq iota] {delta : NNReal}
          {A : Finset iota} {Y : iota -> ShadedTube delta E}
          {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
          {p : Params} {BF L L' : NNReal} {block : ActualSourceDividingBlockW95 U p BF}
          (hL : 1 <= L) (hLL' : L <= L') (S : ActualSameMassSelectionsW95 block L) :
          ActualSameMassSelectionsW95 block L' := by
        have hInv : (L' : ENNReal)⁻¹ <= (L : ENNReal)⁻¹ :=
          ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr hLL')
        have hInvNN : L'⁻¹ <= L⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le (zero_lt_one.trans_le hL) hLL'
        refine { S with
          loss_one := hL.trans hLL'
          first := hone_scale_mono S.first hInv (ENNReal.coe_le_coe.mpr hLL')
          normalization := IsCRefinement.mono hInvNN S.normalization
          second := hone_scale_mono S.second hInv (ENNReal.coe_le_coe.mpr hLL')
          selected_fine_refinement := IsCRefinement.mono hInvNN S.selected_fine_refinement
          fine_retention := ?_ }
        apply le_trans (mul_le_mul' ?_ le_rfl) S.fine_retention
        exact ENNReal.inv_le_inv.mpr (pow_le_pow_left₀ zero_le (ENNReal.coe_le_coe.mpr hLL') 3)
      let Ccard : Real := (5 : Real) ^ (6 : Nat) * (Ctw : Real)
      have hCcard : 1 <= Ccard := by
        have htw : (1 : Real) <= Ctw := hCtw
        dsimp [Ccard]
        norm_num
        linarith
      obtain ⟨Craw, hCraw, hrawBound⟩ := hraw_polylog Ccard hCcard
      obtain ⟨Cratio, Cbin, deltaRatio, hCratio, hCbin, hdeltaRatio, hdeltaRatio1, hratio⟩ :=
        exists_paid_common_ratio_bin_w97 hdim eReserve Ccard heReserve hCcard
      obtain ⟨Cgeom, hCgeom, hrealize⟩ := hwhole_parent_realization
      obtain ⟨Kpatch, hKpatch, hsecondActual⟩ := hactual_second_selected
      let K : NNReal := Kpatch
      have hK : 1 <= K := by dsimp only [K]; exact_mod_cast hKpatch
      let cross := sourceRawCrossCostW97 (Module.finrank Real E)
      have hcross : 1 <= cross := le_max_left _ _
      let Cselect : NNReal := 16 * cross * Cgeom * Cbin * K * Craw ^ (3 : Nat)
      have hCselect : 1 <= Cselect :=
        one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul (by norm_num) hcross) hCgeom) hCbin) hK)
          (one_le_pow₀ hCraw)
      let delta0 : NNReal := min deltaRatio (min (1 / 2) ((16 : NNReal) ^ (-(M : Real))))
      have hdelta0 : 0 < delta0 := by dsimp [delta0]; positivity
      have hdelta01 : delta0 < 1 :=
        (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num : (1 / 2 : NNReal) < 1))
      refine ⟨Cselect, 19, delta0, hCselect, by norm_num, hdelta0, hdelta01, ?_⟩
      intro delta hdelta hsmall iota inst A Y U hA hregular hball hfull p BF block
      have hd1 : delta <= 1 := (hsmall.trans hdelta01).le
      have hratioSmall : delta < deltaRatio := hsmall.trans_le (min_le_left _ _)
      have hgridSmall : delta <= (16 : NNReal) ^ (-(M : Real)) :=
        hsmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      let rho := Tube.gridScale delta M block.b.val
      let theta := Tube.gridScale delta M block.a.val
      have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
      have ha : block.a.val <= M := Nat.le_of_lt_succ block.a.isLt
      have hrho : 0 < rho := Tube.gridScale_pos hdelta _ _
      have hrho1 : rho <= 1 := Tube.gridScale_le_one hd1 _ _
      have htheta1 : theta <= 1 := Tube.gridScale_le_one hd1 _ _
      have hdrho : delta <= rho := by
        simpa only [Tube.gridScale_self delta hM] using Tube.gridScale_antitone hdelta hd1 M hb
      have hrhotheta : rho <= theta := Tube.gridScale_antitone hdelta hd1 M block.a_lt_b.le
      have hrhoSmall : rho <= 1 / 16 := by
        have h := Tube.sixteen_mul_gridScale_le hdelta hd1 hgridSmall
          (show 0 < block.b.val by have h := block.a_lt_b; omega) hb
        rw [Tube.gridScale_zero] at h
        apply (le_div_iff₀ (by norm_num : (0 : NNReal) < 16)).mpr
        simpa only [mul_comm] using h
      have hmass : 0 < ∑ i ∈ A, volume (Y i).shade := by
        have hpositive : 0 < fullness' A (fun i => (Y i).toShadedBody) :=
          (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) ENNReal.coe_ne_top).trans_le hfull
        by_contra hn
        have hz : (∑ i ∈ A, volume (Y i).shade) = 0 := le_antisymm (not_lt.mp hn) bot_le
        change 0 < (∑ i ∈ A, volume (Y i).shade) / _ at hpositive
        rw [hz, ENNReal.zero_div] at hpositive
        exact lt_irrefl _ hpositive
      have hcard : (A.card : Real) <= Ccard * (delta : Real) ^ (-6 : Real) :=
        hinput_card hdelta hd1 A (fun i => (Y i).toTube) hball (hbottom_line A Y U hregular)
      obtain ⟨F, G, hFinner, hFouter, hFparent, hFinnerBody, hFouterBody, ⟨raw⟩⟩ :=
        hactual_first_raw hdelta hd1 A Y U block.b.val hb hball hmass
      have hinner : ∀ i ∈ F.innerSet, F.innerBody i = (Y i).toShadedBody := by
        intro i hi
        rw [hFinnerBody]
      have hFfull : (delta : ENNReal) ^ eReserve <= fullness' F.innerSet F.innerBody := by
        rw [hFinner, hFinnerBody]
        exact hfull
      have hFcard : (F.innerSet.card : Real) <= Ccard * (delta : Real) ^ (-6 : Real) := by
        rw [hFinner]
        exact hcard
      obtain ⟨H, c, Jbin, hH, hHheavy, hc, hJbin, hJbound, hheavyMass, hheavyRange, hratioBand, hbinMass⟩ :=
        hratio hdelta hratioSmall hdrho hrho1 F Y (U.cover.tube block.b.val) G raw hinner hFfull hFcard
      have hHG : H ⊆ G.outerSet := hHheavy.trans (Finset.filter_subset _ _)
      have hJ : (1 : NNReal) <= Jbin := by exact_mod_cast hJbin
      let r : NNReal := (2 * (Jbin : NNReal))⁻¹
      have hr : 0 < r := by dsimp [r]; positivity
      have hr1 : r <= 1 := by
        have hden : (1 : NNReal) <= 2 * (Jbin : NNReal) :=
          (show (1 : NNReal) <= 2 by norm_num).trans (by simpa using mul_le_mul_left' hJ 2)
        simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : NNReal) < 1) hden
      have hrcoe : (r : ENNReal) = (2 * (Jbin : ENNReal))⁻¹ := by
        dsimp [r]
        rw [ENNReal.coe_inv (by positivity), ENNReal.coe_mul]
        norm_num
      have hbinRetained : (r : ENNReal) *
          (∑ Q ∈ G.outerSet, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) <=
            ∑ Q ∈ H, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade := by
        rw [hrcoe]
        exact hbinMass
      let F1 := G.innerSet.filter (fun i => G.parent i ∈ H)
      let L1 := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
        (Module.finrank Real E) F.innerSet.card delta 1
      have hL1 : 1 <= L1 := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _
      obtain ⟨W, Z1, hHne, hF1, hF1F, hF1image, hWtube, hZ1tube, hWshade, hZ1shade,
        hWsub, hfirstRetained, hfirstScalar, hfirstParentFullness⟩ :=
        hrealize hdelta hdrho hrho1 F Y (U.cover.tube block.b.val) G raw H r
          hinner hHG hr hr1 hbinRetained
      have hF1A : F1 ⊆ A := hFinner ▸ hF1F
      have hparentG : G.parent = U.cover.assign block.b.val := raw.parent_eq.trans hFparent
      have hHparent : H ⊆ U.cover.indexSet block.b.val := by
        intro Q hQ
        exact hFouter ▸ raw.outer_subset (hHG hQ)
      have hF1actualImage : F1.image (U.cover.assign block.b.val) = H := by
        rw [← hparentG]
        exact hF1image
      let m := fun Q => ∑ i ∈ completeFibreW94 F1 (U.cover.assign block.b.val) Q, volume (W i).shade
      have hmraw (Q : iota) (hQ : Q ∈ H) : m Q = ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade := by
        have hfibre : completeFibreW94 F1 (U.cover.assign block.b.val) Q = G.fiber Q := by
          ext i
          simp only [completeFibreW94, F1, ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter, hparentG]
          constructor
          · rintro ⟨⟨hi, hparentH⟩, hparentQ⟩
            exact ⟨hi, hparentQ⟩
          · rintro ⟨hi, hparentQ⟩
            exact ⟨⟨hi, hparentQ ▸ hQ⟩, hparentQ⟩
        dsimp only [m]
        rw [hfibre]
        apply Finset.sum_congr rfl
        intro i hi
        have hiG : i ∈ G.innerSet ∧ G.parent i = Q := by
          simpa only [ShadedBody.ShadedFactorFamily.fiber, Finset.mem_filter] using hi
        exact congrArg volume (hWshade i (raw.raw_refinement.1.1 hiG.1))
      obtain ⟨Zmid, hZmidTube, hZmidShade, hZmidMass, hnormalized⟩ :=
        hnormalized_parent_shading H Z1 m c
          (fun Q hQ => by rw [hmraw Q hQ, hZ1shade Q (hHG hQ)]; exact (hratioBand Q hQ).1)
          (fun Q hQ => by rw [hmraw Q hQ, hZ1shade Q (hHG hQ)]; exact (hratioBand Q hQ).2.le)
      have hZmidActual (Q : iota) : (Zmid Q).toTube = U.cover.tube block.b.val Q :=
        (hZmidTube Q).trans (hZ1tube Q)
      have hZmidPos : 0 < ∑ Q ∈ H, volume (Zmid Q).shade := by
        obtain ⟨Q, hQ⟩ := hH
        have hqmass : 0 < m Q := by rw [hmraw Q hQ]; exact raw.fibre_mass_pos Q (hHG hQ)
        have hpos : 0 < volume (Zmid Q).shade := by
          rw [hZmidMass Q hQ]
          exact ENNReal.mul_pos (ENNReal.coe_pos.mpr hc).ne' hqmass.ne'
        exact hpos.trans_le (Finset.single_le_sum (f := fun Q => volume (Zmid Q).shade) (fun _ _ => zero_le) hQ)
      obtain ⟨coarseAssign, hcompatible, hcoarseMem, hcoarseTube⟩ :=
        hactual_coarse_assign A Y U hregular block.a.val block.b.val block.a_lt_b hb
      obtain ⟨mid, F2, P2, Y2, Z2, middleLabel, coarseFullness, middleFullness,
        hmid, hmidH, hF2, hpatchMass, hpatchWeight, second, hsecondParentFullness,
        rawData, hrawData⟩ :=
        hsecondActual hrho hrhoSmall hrhotheta htheta1 (U.cover.indexSet block.b.val) H Zmid
          (U.cover.tube block.b.val) (U.cover.indexSet block.a.val) (U.cover.tube block.a.val)
          coarseAssign m c hHparent (fun Q hQ => hZmidActual Q) hc hZmidPos hZmidMass
          (fun Q hQ => by
            rw [show (Zmid Q).carrier = (U.cover.tube block.b.val Q).carrier from
              congrArg (fun T : Tube rho E => T.carrier) (hZmidActual Q)]
            exact hregular.parent_ball _ hb Q (hHparent hQ))
          (by
            intro R hR
            obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hR
            exact hcoarseMem Q (hHparent hQ))
          (fun Q hQ => by
            rw [show (Zmid Q).toConvexSpaceBody = (U.cover.tube block.b.val Q).toConvexSpaceBody from
              congrArg Tube.toConvexSpaceBody (hZmidActual Q)]
            exact hcoarseTube Q (hHparent hQ))
      let L2 := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
        (Module.finrank Real E) mid.card rho 1
      have hL2 : 1 <= L2 := ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _
      have hsecondShade : ∀ Q ∈ F2, (Y2 Q).toTube = (Zmid Q).toTube ∧ (Y2 Q).shade ⊆ (Zmid Q).shade := by
        intro Q hQ
        have h := second.child_shade Q hQ
        rw [zeroExtend_toTube_of_mem (second.child_subset hQ), zeroExtend_shade_of_mem (second.child_subset hQ)] at h
        exact h
      have hsecondRetained : (L2 : ENNReal)⁻¹ * (∑ Q ∈ mid, volume (Zmid Q).shade) <=
          ∑ Q ∈ F2, volume (Y2 Q).shade := by
        have h := second.child_retention
        rw [sum_volume_shade_zeroExtend_of_subset (Finset.Subset.refl mid)] at h
        exact h
      obtain ⟨Fdagger, Ydagger, hFdagger, hFdaggerNe, hFdaggerF1, hFdaggerImage,
        hFdaggerShade, hweightedCut, hcutRetained⟩ :=
        hsame_cut_funding F1 W H mid F2 Zmid Y2 (U.cover.assign block.b.val) c K L2
          hc hK hL2 hmidH hF2 second.child_subset hF1actualImage hZmidMass
          hsecondShade hpatchWeight hsecondRetained
      have hL1pos : 0 < L1 := zero_lt_one.trans_le hL1
      have hL2pos : 0 < L2 := zero_lt_one.trans_le hL2
      have hKpos : 0 < K := zero_lt_one.trans_le hK
      have hJpos : (0 : NNReal) < Jbin := zero_lt_one.trans_le hJ
      let retained : NNReal := (2 * (Jbin : NNReal) * L1 * K * L2)⁻¹
      have hretainedPos : 0 < retained := by dsimp [retained]; positivity
      have hretainedEq : retained = (K * L2)⁻¹ * (r * L1⁻¹) := by
        dsimp [retained, r]
        simp only [mul_inv_rev]
        ring
      have hfirstMass : ((r * L1⁻¹ : NNReal) : ENNReal) * (∑ i ∈ A, volume (Y i).shade) <=
          ∑ i ∈ F1, volume (W i).shade := by
        rw [ENNReal.coe_mul, ENNReal.coe_inv hL1pos.ne']
        simpa only [F1, L1, hFinner] using hfirstRetained
      have hfinalMass : (retained : ENNReal) * (∑ i ∈ A, volume (Y i).shade) <=
          ∑ i ∈ Fdagger, volume (Ydagger i).shade := by
        rw [hretainedEq, ENNReal.coe_mul, mul_assoc]
        exact (mul_le_mul' le_rfl hfirstMass).trans hcutRetained
      obtain ⟨fineLabel, hFineLabel, hFineFullness, hFineRefinement⟩ :=
        hactual_joint_label A F1 Fdagger Y W Ydagger (U.cover.assign block.b.val) retained hretainedPos
          hF1A hFdaggerF1 (fun i hi => hWtube i)
          (fun i hi => (hFdaggerShade i hi).1.trans (hWtube i))
          (fun i hi => (hWsub i hi).1) (fun i hi => (hFdaggerShade i hi).2) hmass hfinalMass
      let Lactual : NNReal := 16 * Cgeom * (Jbin : NNReal) * K * L1 ^ (2 : Nat) * L2
      have hLactual : 1 <= Lactual :=
        one_le_mul (one_le_mul (one_le_mul (one_le_mul (one_le_mul (by norm_num) hCgeom) hJ) hK)
          (one_le_pow₀ hL1)) hL2
      have hLactualPos : 0 < Lactual := zero_lt_one.trans_le hLactual
      have hquarterEq : retained / 4 = (8 * (Jbin : NNReal) * L1 * K * L2)⁻¹ := by
        dsimp [retained]
        simp only [mul_inv_rev, div_eq_mul_inv]
        norm_num
        ring
      have hL1sq : L1 <= L1 ^ (2 : Nat) := by
        calc
          L1 = L1 * 1 := by ring
          _ <= L1 * L1 := mul_le_mul_left' hL1 L1
          _ = _ := by ring
      have hfundingDen : 8 * (Jbin : NNReal) * L1 * K * L2 <= Lactual := by
        have hgeom : (8 : NNReal) <= 16 * Cgeom :=
          (by norm_num : (8 : NNReal) <= 16).trans
            (le_mul_of_one_le_right zero_le hCgeom)
        calc
          _ = 8 * (Jbin : NNReal) * K * L1 * L2 := by ring
          _ <= (16 * Cgeom) * (Jbin : NNReal) * K * L1 ^ (2 : Nat) * L2 :=
            mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hgeom le_rfl) le_rfl) hL1sq) le_rfl
          _ = _ := by rfl
      have hfundingNN : Lactual⁻¹ <= retained / 4 := by
        rw [hquarterEq]
        simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hfundingDen
      have hfunding : (Lactual : ENNReal)⁻¹ <= ((retained / 4 : NNReal) : ENNReal) := by
        rw [← ENNReal.coe_inv hLactualPos.ne']
        exact ENNReal.coe_le_coe.mpr hfundingNN
      have hretainedSmall : retained / 4 <= r * L1⁻¹ := by
        have hKL : (K * L2)⁻¹ <= 1 := by
          simpa only [one_div, inv_one] using
            one_div_le_one_div_of_le (by norm_num : (0 : NNReal) < 1) (one_le_mul hK hL2)
        calc
          retained / 4 <= retained := div_le_self zero_le (by norm_num)
          _ = (K * L2)⁻¹ * (r * L1⁻¹) := hretainedEq
          _ <= r * L1⁻¹ := mul_le_of_le_one_left zero_le hKL
      have hnormCost : 2 * K <= Lactual := by
        have hone : 1 <= Cgeom * (Jbin : NNReal) * L1 ^ (2 : Nat) * L2 :=
          one_le_mul (one_le_mul (one_le_mul hCgeom hJ) (one_le_pow₀ hL1)) hL2
        calc
          2 * K <= 16 * K := by gcongr; norm_num
          _ <= (16 * K) * (Cgeom * (Jbin : NNReal) * L1 ^ (2 : Nat) * L2) :=
            le_mul_of_one_le_right zero_le hone
          _ = Lactual := by dsimp [Lactual]; ring
      have hsecondCost : L2 <= Lactual := by
        have hone : 1 <= 16 * Cgeom * (Jbin : NNReal) * K * L1 ^ (2 : Nat) :=
          one_le_mul (one_le_mul (one_le_mul (one_le_mul (by norm_num) hCgeom) hJ) hK) (one_le_pow₀ hL1)
        exact le_mul_of_one_le_left zero_le hone
      have hscalarCostNN : Cgeom * L1 ^ (2 : Nat) / r <= Lactual := by
        calc
          _ = 2 * (Cgeom * (Jbin : NNReal) * L1 ^ (2 : Nat)) := by
            dsimp [r]
            simp only [div_eq_mul_inv, inv_inv]
            ring
          _ <= 16 * (Cgeom * (Jbin : NNReal) * L1 ^ (2 : Nat)) := by gcongr; norm_num
          _ <= (16 * (Cgeom * (Jbin : NNReal) * L1 ^ (2 : Nat))) * (K * L2) :=
            le_mul_of_one_le_right zero_le (one_le_mul hK hL2)
          _ = _ := by dsimp [Lactual]; ring
      have hscalarCost : (Cgeom : ENNReal) * (L1 : ENNReal) ^ (2 : Nat) / (r : ENNReal) <= Lactual := by
        have h := ENNReal.coe_le_coe.mpr hscalarCostNN
        simpa only [ENNReal.coe_div hr.ne', ENNReal.coe_mul, ENNReal.coe_pow] using h
      have hhalfMass : (∑ Q ∈ H, volume (Z1 Q).shade) <= 2 * ∑ Q ∈ H, volume (Zmid Q).shade := by
        have h := hnormalized.2
        rw [ENNReal.coe_div (by norm_num), ENNReal.coe_one, ENNReal.coe_ofNat, one_div] at h
        exact (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).mp h
      have hmiddleNormalization : IsCRefinement mid (fun Q => (Zmid Q).toShadedBody)
          H (fun Q => (Z1 Q).toShadedBody) (2 * K)⁻¹ := by
        apply isCRefinement_of_isRefinement_of_sum_le
        · exact ⟨hmidH, fun Q hQ => ⟨congrArg Tube.toConvexSpaceBody (hZmidTube Q), hZmidShade Q (hmidH hQ)⟩⟩
        · rw [ENNReal.coe_mul, ENNReal.coe_ofNat]
          exact hhalfMass.trans (by
            simpa only [K, ENNReal.coe_natCast, mul_assoc] using
              mul_le_mul' (le_refl (2 : ENNReal)) hpatchMass)
      have hFineLabelH : fineLabel ∈ H := hF1actualImage ▸ hFineLabel
      have hselectedFibre : fibre A (U.cover.assign block.b.val) fineLabel =
          completeFibreW94 A (U.cover.assign block.b.val) fineLabel := by
        ext i
        simp only [fibre, completeFibreW94, Finset.mem_filter]
      let fineFullness : NNReal := ShadedBody.fullness
        (completeFibreW94 A (U.cover.assign block.b.val) fineLabel)
        (fun i => ((selectedShade F1 Y W) i).toShadedBody)
      have hfirstSelected : IsOneScaleSelected (Lactual : ENNReal)⁻¹ (Lactual : ENNReal)
          A A Y (U.cover.indexSet block.b.val) (U.cover.tube block.b.val) (U.cover.assign block.b.val)
          F1 W H Z1 fineLabel (ShadedBody.fullness H (fun Q => (Z1 Q).toShadedBody)) fineFullness := by
        refine
          { active_subset := Finset.Subset.refl _
            shade_off := fun i hi hn => (hn hi).elim
            child_subset := hF1A
            child_shade := fun i hi => ⟨hWtube i, (hWsub i hi).1⟩
            child_retention := ?_
            parent_subset := hHparent
            parent_mapsTo := ?_
            parent_tube := fun Q hQ => hZ1tube Q
            parent_contain := ?_
            parent_fullness := le_rfl
            scalar := ?_
            sel_mem := hFineLabelH
            sel_nonempty := ?_
            sel_fullness := ?_
            sel_fullness_lb := ?_ }
        · exact (mul_le_mul' (hfunding.trans (ENNReal.coe_le_coe.mpr hretainedSmall)) le_rfl).trans hfirstMass
        · intro i hi
          rw [← hF1actualImage]
          exact Finset.mem_image_of_mem _ hi
        · intro i hi
          rw [← hparentG]
          exact (hWsub i hi).2
        · intro Q hQ
          have h := hfirstScalar Q hQ
          rw [hFinner, hparentG] at h
          have hfibre : fibre F1 (U.cover.assign block.b.val) Q = completeFibreW94 F1 (U.cover.assign block.b.val) Q := by
            ext i
            simp only [fibre, completeFibreW94, Finset.mem_filter]
          rw [hfibre]
          have hcost : (Cgeom : ENNReal) *
              (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank Real E) A.card delta 1 : ENNReal) ^ (2 : Nat) / (r : ENNReal) <= Lactual := by
            simpa only [L1, hFinner] using hscalarCost
          simp only [F1, hparentG]
          exact h.trans (mul_le_mul' (mul_le_mul' hcost le_rfl) le_rfl)
        · obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hFineLabel
          refine ⟨i, ?_⟩
          simpa only [fibre, Finset.mem_filter] using And.intro (hF1A hi) hip
        · rw [hselectedFibre]
        · rw [ShadedBody.coe_fullness]
          rw [show (fineFullness : ENNReal) = fullness'
            (completeFibreW94 A (U.cover.assign block.b.val) fineLabel)
            (fun i => ((selectedShade F1 Y W) i).toShadedBody) from ShadedBody.coe_fullness _ _]
          exact (mul_le_mul' hfunding le_rfl).trans hFineFullness
      have hLactualCube : Lactual <= Lactual ^ (3 : Nat) := by
        calc
          Lactual <= Lactual * Lactual ^ (2 : Nat) := le_mul_of_one_le_right zero_le (one_le_pow₀ hLactual)
          _ = _ := by ring
      have hcubeFunding : ((Lactual : ENNReal) ^ (3 : Nat))⁻¹ <= (retained : ENNReal) := by
        have hcube : (Lactual : ENNReal) <= (Lactual : ENNReal) ^ (3 : Nat) := by
          exact_mod_cast hLactualCube
        apply (ENNReal.inv_le_inv.mpr hcube).trans
        exact hfunding.trans (ENNReal.coe_le_coe.mpr (div_le_self zero_le (by norm_num)))
      let selections : ActualSameMassSelectionsW95 block Lactual :=
        { loss_one := hLactual
          firstFamily := F1
          firstShading := W
          firstParents := H
          firstParentShading := Z1
          fineLabel := fineLabel
          firstParentFullness := ShadedBody.fullness H (fun Q => (Z1 Q).toShadedBody)
          fineFullness := fineFullness
          first := hfirstSelected
          middle := mid
          middleShading := Zmid
          middle_nonempty := hmid
          middle_subset := hmidH
          middle_tube := fun Q hQ => hZmidActual Q
          normalization := IsCRefinement.mono
            (by simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hnormCost) hmiddleNormalization
          commonMass := c
          commonMass_pos := hc
          induced_mass := fun Q hQ => hZmidMass Q (hmidH hQ)
          coarseAssign := coarseAssign
          parent_compatibility := hcompatible
          secondFamily := F2
          secondShading := Y2
          coarseFamily := P2
          coarseShading := Z2
          middleLabel := middleLabel
          coarseFullness := coarseFullness
          middleFullness := middleFullness
          second := hone_scale_mono second
            (ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr hsecondCost)) (ENNReal.coe_le_coe.mpr hsecondCost)
          fineFamily := Fdagger
          fineShading := Ydagger
          fine_nonempty := hFdaggerNe
          fine_subset := hFdaggerF1
          fine_image := hFdaggerImage
          fine_same_tube := fun i hi => (hFdaggerShade i hi).1.trans (hWtube i)
          fine_subshade := fun i hi => (hFdaggerShade i hi).2
          weighted_cut := hweightedCut
          selected_fine_refinement := IsCRefinement.mono hfundingNN hFineRefinement
          fine_retention := (mul_le_mul' hcubeFunding le_rfl).trans hfinalMass }
      have hdeltaReal : (0 : Real) < delta := hdelta
      have hdeltaReal1 : (delta : Real) <= 1 := hd1
      have hlog : 0 <= Real.log (1 / (delta : Real)) :=
        Real.log_nonneg ((one_le_div hdeltaReal).mpr hdeltaReal1)
      have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hbaseNonneg : 0 <= 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by positivity
      let Bdelta := Real.toNNReal (2 + Real.log (1 / (delta : Real)) / Real.log 2)
      have hBdelta : (Bdelta : Real) = 2 + Real.log (1 / (delta : Real)) / Real.log 2 :=
        Real.coe_toNNReal _ hbaseNonneg
      have hJpoly : (Jbin : NNReal) <= Cbin * Bdelta := by
        apply NNReal.coe_le_coe.mp
        rw [NNReal.coe_natCast, NNReal.coe_mul, hBdelta]
        apply hJbound.trans
        apply mul_le_mul_of_nonneg_left _ Cbin.coe_nonneg
        apply add_le_add le_rfl
        apply (le_div_iff₀ hlogTwo).mpr
        have hlogTwoLe : Real.log 2 <= 1 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
          norm_num at h
          exact h
        exact mul_le_of_le_one_right hlog hlogTwoLe
      have hL1poly : L1 <= Craw * Bdelta ^ (6 : Nat) := by
        have h := hrawBound delta delta hdelta (le_refl _) hd1 A.card (Finset.card_pos.mpr hA) hcard
        rw [Real.toNNReal_pow hbaseNonneg] at h
        simpa only [L1, hdim, hFinner] using h
      have hmidCard : mid.card <= A.card := by
        apply (Finset.card_le_card (hmidH.trans hHparent)).trans
        rw [← hregular.surjective block.b.val hb]
        exact Finset.card_image_le
      have hmidCardReal : (mid.card : Real) <= Ccard * (delta : Real) ^ (-6 : Real) :=
        (Nat.cast_le.mpr hmidCard).trans hcard
      have hL2poly : L2 <= Craw * Bdelta ^ (6 : Nat) := by
        have h := hrawBound delta rho hdelta hdrho hrho1 mid.card (Finset.card_pos.mpr hmid) hmidCardReal
        rw [Real.toNNReal_pow hbaseNonneg] at h
        simpa only [L2, hdim] using h
      have hpaid : Lactual <= Cselect * Real.toNNReal
          ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (19 : Nat)) := by
        rw [Real.toNNReal_pow hbaseNonneg]
        change Lactual <= Cselect * Bdelta ^ (19 : Nat)
        dsimp only [Lactual]
        calc
          _ <= 16 * Cgeom * (Cbin * Bdelta) * K *
              (Craw * Bdelta ^ (6 : Nat)) ^ (2 : Nat) * (Craw * Bdelta ^ (6 : Nat)) := by gcongr
          _ = (16 * Cgeom * Cbin * K * Craw ^ (3 : Nat)) * Bdelta ^ (19 : Nat) := by ring
          _ <= cross * ((16 * Cgeom * Cbin * K * Craw ^ (3 : Nat)) * Bdelta ^ (19 : Nat)) :=
            le_mul_of_one_le_left zero_le hcross
          _ = _ := by dsimp [Cselect]; ring
      let lambda : NNReal := ShadedBody.fullness A (fun i => (Y i).toShadedBody)
      have hlambda : (lambda : ENNReal) = fullness' A (fun i => (Y i).toShadedBody) :=
        ShadedBody.coe_fullness _ _
      let alpha : NNReal := r * L1⁻¹
      have halpha : 0 < alpha := mul_pos hr (inv_pos.mpr hL1pos)
      let J := U.cover.indexSet block.b.val
      have hJne : J.Nonempty := by
        change (U.cover.indexSet block.b.val).Nonempty
        rw [← hregular.surjective block.b.val hb]
        exact hA.image _
      obtain ⟨n, hn, hnBounds⟩ := hbottomCounts A Y U hregular block.b.val hb
      obtain ⟨i0, hi0⟩ := hA
      let vFine := volume (Y i0).carrier
      obtain ⟨hvFine, hvFineTop⟩ := Tube.volume_pos_and_lt_top hdelta hd1 (Y i0).toTube
      have hparentCount : ((alpha * lambda : NNReal) : ENNReal) * (J.card : ENNReal) <=
          2 * (H.card : ENNReal) := by
        rw [ENNReal.coe_mul]
        apply hretainedParentCount A F1 J H (U.cover.assign block.b.val)
          (fun i => volume (Y i).shade) (fun i => volume (W i).shade)
          vFine n alpha lambda hvFine hvFineTop (ENNReal.coe_pos.mpr hn) ENNReal.coe_lt_top
          (U.cover.assign_mem block.b.val hb) hF1A
          (fun i hi => hF1actualImage ▸ Finset.mem_image_of_mem _ hi) hHparent
        · intro Q hQ
          exact ⟨by exact_mod_cast (hnBounds Q hQ).1, by exact_mod_cast (hnBounds Q hQ).2⟩
        · intro i hi
          calc
            volume (W i).shade <= volume (W i).carrier := measure_mono (W i).shade_subset
            _ = volume (Y i).carrier := congrArg (fun T : Tube delta E => volume T.carrier) (hWtube i)
            _ = vFine := Tube.volume_carrier_eq_volume_carrier _ _
        · calc
            _ = (lambda : ENNReal) * ∑ i ∈ A, volume (Y i).carrier :=
              ShadedBody.sum_volumeReal_shade_eq_fullness_mul _ _
            _ = _ := by
              congr 1
              calc
                _ = ∑ i ∈ A, vFine := Finset.sum_congr rfl
                  (fun i hi => Tube.volume_carrier_eq_volume_carrier _ _)
                _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        · exact hfirstMass
      have hfirstFineFullness : (alpha : ENNReal) * (lambda : ENNReal) <=
          fullness' F1 (fun i => (W i).toShadedBody) := by
        rw [hlambda]
        exact hfullnessOfRetainedMass A F1 _ _ alpha hF1A
          (fun i hi => congrArg (fun T : Tube delta E => T.carrier) (hWtube i)) hfirstMass
      have hfirstFullness : ((2 * cross : NNReal) : ENNReal)⁻¹ *
          ((alpha * lambda : NNReal) : ENNReal) <= fullness' H (fun Q => (Z1 Q).toShadedBody) := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_ofNat]
        exact (mul_le_mul' le_rfl hfirstFineFullness).trans hfirstParentFullness
      obtain ⟨Q0, hQ0⟩ := hJne
      let vMiddle := volume (U.cover.tube block.b.val Q0).carrier
      obtain ⟨hvMiddle, hvMiddleTop⟩ := Tube.volume_pos_and_lt_top hrho hrho1
        (U.cover.tube block.b.val Q0)
      have hparentOldFullness : ((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ *
          ((alpha * lambda : NNReal) : ENNReal) ^ (2 : Nat) <=
          fullness' J (fun Q => (zeroExtend H (U.cover.tube block.b.val) Z1 Q).toShadedBody) :=
        hparentAmbientFullness J H (U.cover.tube block.b.val) Z1 ⟨Q0, hQ0⟩ hHne hHparent
          vMiddle hvMiddle hvMiddleTop (fun Q hQ => Tube.volume_carrier_eq_volume_carrier _ _)
          (fun Q hQ => hZ1tube Q) (alpha * lambda) (2 * cross) (by positivity) hparentCount hfirstFullness
      have hsecondTubeActual : ∀ Q ∈ F2, (Y2 Q).toTube = U.cover.tube block.b.val Q :=
        fun Q hQ => (hsecondShade Q hQ).1.trans (hZmidActual Q)
      let Bsecond : NNReal := 2 * K * L2
      have hBsecond : 0 < Bsecond := by dsimp [Bsecond]; positivity
      have hmiddleMass : ((2 * K : NNReal) : ENNReal)⁻¹ *
          (∑ Q ∈ H, volume (Z1 Q).shade) <= ∑ Q ∈ mid, volume (Zmid Q).shade := by
        have h := hmiddleNormalization.2
        rw [ENNReal.coe_inv (by positivity)] at h
        exact h
      have hsecondMassPaid : (Bsecond : ENNReal)⁻¹ *
          (∑ Q ∈ H, volume (Z1 Q).shade) <= ∑ Q ∈ F2, volume (Y2 Q).shade := by
        calc
          _ = (L2 : ENNReal)⁻¹ * (((2 * K : NNReal) : ENNReal)⁻¹ *
              (∑ Q ∈ H, volume (Z1 Q).shade)) := by
            dsimp only [Bsecond]
            rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top)]
            ring
          _ <= (L2 : ENNReal)⁻¹ * (∑ Q ∈ mid, volume (Zmid Q).shade) := mul_le_mul' le_rfl hmiddleMass
          _ <= _ := hsecondRetained
      have hfinalOldFullness : (Bsecond : ENNReal)⁻¹ *
          (((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ * ((alpha * lambda : NNReal) : ENNReal) ^ (2 : Nat)) <=
          fullness' J (fun Q => (zeroExtend F2 (U.cover.tube block.b.val) Y2 Q).toShadedBody) :=
        (mul_le_mul' le_rfl hparentOldFullness).trans
          (hzeroExtendFullnessRetention J H F2 (U.cover.tube block.b.val) Z1 Y2
            (Bsecond : ENNReal)⁻¹ hHparent (second.child_subset.trans (hmidH.trans hHparent))
            (fun Q hQ => hZ1tube Q) hsecondTubeActual hsecondMassPaid)
      let D : NNReal := Bsecond * (2 * (2 * cross)) * (alpha⁻¹) ^ (2 : Nat)
      have hfourCross : (0 : NNReal) < 2 * (2 * cross) := by positivity
      have hD : 0 < D := by dsimp only [D]; positivity
      have hDformula : D = 32 * cross * (Jbin : NNReal) ^ (2 : Nat) * L1 ^ (2 : Nat) * K * L2 := by
        dsimp only [D, Bsecond, alpha, r]
        simp only [mul_inv_rev, inv_inv]
        ring
      have hBdeltaOne : 1 <= Bdelta := by
        apply NNReal.coe_le_coe.mp
        rw [NNReal.coe_one, hBdelta]
        have h := div_nonneg hlog hlogTwo.le
        linarith
      have hDpaid : D <= (Cselect * Real.toNNReal
          ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (19 : Nat))) ^ (6 : Nat) := by
        rw [Real.toNNReal_pow hbaseNonneg]
        change D <= (Cselect * Bdelta ^ (19 : Nat)) ^ (6 : Nat)
        rw [hDformula]
        exact hfullnessDebt cross Cgeom Cbin K Craw Bdelta (Jbin : NNReal) L1 L2
          hcross hCgeom hCbin hK hCraw hBdeltaOne hJpoly hL1poly hL2poly
      have hcoefficientNN : D⁻¹ * lambda ^ (2 : Nat) =
          Bsecond⁻¹ * ((2 * (2 * cross))⁻¹ * (alpha * lambda) ^ (2 : Nat)) := by
        dsimp only [D]
        simp only [mul_inv_rev, inv_pow, inv_inv]
        ring
      have hcoefficient : (D : ENNReal)⁻¹ * (lambda : ENNReal) ^ (2 : Nat) =
          (Bsecond : ENNReal)⁻¹ * (((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ *
            ((alpha * lambda : NNReal) : ENNReal) ^ (2 : Nat)) := by
        have h := congrArg (fun x : NNReal => (x : ENNReal)) hcoefficientNN
        simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv hD.ne',
          ENNReal.coe_inv hBsecond.ne', ENNReal.coe_inv hfourCross.ne'] using h
      let Lpaid := Cselect * Real.toNNReal
        ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (19 : Nat))
      have hLpaid : 1 <= Lpaid := hLactual.trans hpaid
      have hDpaidE : (D : ENNReal) <=
          (((Cselect * Real.toNNReal ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ (19 : Nat)) : NNReal) : ENNReal)
            ^ (6 : Nat)) := by exact_mod_cast hDpaid
      have hmiddle : ((Lpaid : ENNReal) ^ (6 : Nat))⁻¹ * (lambda : ENNReal) ^ (2 : Nat) <=
          fullness' J (fun Q => (zeroExtend F2 (U.cover.tube block.b.val) Y2 Q).toShadedBody) := by
        apply (mul_le_mul' (ENNReal.inv_le_inv.mpr hDpaidE) le_rfl).trans
        rw [hcoefficient]
        exact hfinalOldFullness
      let Vsecond := zeroExtend F2 (U.cover.tube block.b.val) Y2
      let lambdaB : NNReal := ShadedBody.fullness J (fun Q => (Vsecond Q).toShadedBody)
      have hlambdaB : (lambdaB : ENNReal) = fullness' J (fun Q => (Vsecond Q).toShadedBody) :=
        ShadedBody.coe_fullness _ _
      have hF2J : F2 ⊆ J := second.child_subset.trans (hmidH.trans hHparent)
      have hparentTube : ∀ R ∈ P2, (Z2 R).toTube = U.cover.tube block.a.val R :=
        second.parent_tube
      have hmidActive : (lambdaB : ENNReal) <= fullness' F2 (fun Q => (Y2 Q).toShadedBody) := by
        rw [hlambdaB]
        simpa only [one_mul] using hfullnessOfRetainedMass J F2
          (fun Q => (Vsecond Q).toShadedBody) (fun Q => (Y2 Q).toShadedBody) 1 hF2J
          (fun Q hQ => by
            change (Y2 Q).toTube.carrier = (Vsecond Q).toTube.carrier
            rw [hsecondTubeActual Q hQ, zeroExtend_toTube hsecondTubeActual])
          (by rw [one_mul]; exact le_of_eq (sum_volume_shade_zeroExtend_of_subset hF2J _ _))
      let Ja := U.cover.indexSet block.a.val
      have hJa : Ja.Nonempty := by
        rw [show Ja = A.image (U.cover.assign block.a.val) from
          (hregular.surjective block.a.val (by omega)).symm]
        exact ⟨U.cover.assign block.a.val i0, Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩
      have hP2 : P2.Nonempty := by
        obtain ⟨Q, hQ⟩ := hF2
        exact ⟨coarseAssign Q, second.parent_mapsTo Q hQ⟩
      have hcoarseFibre (R : iota) : completeFibreW94 J coarseAssign R =
          actualDescendantsW95 A U.cover.assign block.a.val block.b.val R := by
        ext Q
        constructor
        · intro hQ
          obtain ⟨hQJ, hQR⟩ := Finset.mem_filter.mp hQ
          rw [show J = A.image (U.cover.assign block.b.val) from
            (hregular.surjective block.b.val hb).symm] at hQJ
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQJ
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
            ⟨hi, by rw [← hcompatible i hi]; exact hQR⟩, rfl⟩
        · intro hQ
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
          obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨U.cover.assign_mem block.b.val hb i hiA,
            (hcompatible i hiA).trans hiR⟩
      let nc := hregular.countBand block.a.val block.b.val
      have hnc : 0 < nc := hregular.countBand_pos _ _ block.a_lt_b hb
      have hcoarseCount : (lambdaB : ENNReal) * (Ja.card : ENNReal) <= 2 * (P2.card : ENNReal) := by
        simpa only [one_mul] using hretainedParentCount J F2 Ja P2 coarseAssign
          (fun Q => volume (Vsecond Q).shade) (fun Q => volume (Y2 Q).shade)
          vMiddle nc 1 lambdaB hvMiddle hvMiddleTop (ENNReal.coe_pos.mpr hnc) ENNReal.coe_lt_top
          hcoarseMem hF2J second.parent_mapsTo second.parent_subset
          (fun R hR => by
            rw [hcoarseFibre]
            exact ⟨by exact_mod_cast hregular.count_lower _ _ block.a_lt_b hb R hR,
              by exact_mod_cast (hregular.count_upper _ _ block.a_lt_b hb R hR).le⟩)
          (fun Q hQ => by
            calc
              volume (Y2 Q).shade <= volume (Y2 Q).carrier := measure_mono (Y2 Q).shade_subset
              _ = volume (U.cover.tube block.b.val Q).carrier :=
                congrArg (fun T : Tube rho E => volume T.carrier) (hsecondTubeActual Q hQ)
              _ = vMiddle := Tube.volume_carrier_eq_volume_carrier _ _)
          (by
            calc
              _ = (lambdaB : ENNReal) * ∑ Q ∈ J, volume (Vsecond Q).carrier :=
                ShadedBody.sum_volumeReal_shade_eq_fullness_mul _ _
              _ = _ := by
                congr 1
                calc
                  _ = ∑ Q ∈ J, vMiddle := Finset.sum_congr rfl (fun Q hQ => by
                    change volume (Vsecond Q).toTube.carrier = vMiddle
                    rw [zeroExtend_toTube hsecondTubeActual]
                    exact Tube.volume_carrier_eq_volume_carrier _ _)
                  _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul])
          (by rw [one_mul]; exact le_of_eq (sum_volume_shade_zeroExtend_of_subset hF2J _ _))
      have hcoarseActive : ((2 * cross : NNReal) : ENNReal)⁻¹ * (lambdaB : ENNReal) <=
          fullness' P2 (fun R => (Z2 R).toShadedBody) := by
        rw [ENNReal.coe_mul, ENNReal.coe_ofNat]
        exact (mul_le_mul' le_rfl hmidActive).trans hsecondParentFullness
      obtain ⟨R0, hR0⟩ := hJa
      let vCoarse := volume (U.cover.tube block.a.val R0).carrier
      obtain ⟨hvCoarse, hvCoarseTop⟩ := Tube.volume_pos_and_lt_top
        (Tube.gridScale_pos hdelta _ _) htheta1 (U.cover.tube block.a.val R0)
      have hcoarseOld : ((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ * (lambdaB : ENNReal) ^ (2 : Nat) <=
          fullness' Ja (fun R => (zeroExtend P2 (U.cover.tube block.a.val) Z2 R).toShadedBody) :=
        hparentAmbientFullness Ja P2 (U.cover.tube block.a.val) Z2 ⟨R0, hR0⟩ hP2 second.parent_subset
          vCoarse hvCoarse hvCoarseTop (fun R hR => Tube.volume_carrier_eq_volume_carrier _ _)
          hparentTube lambdaB (2 * cross) (by positivity) hcoarseCount hcoarseActive
      have hCselectCross : 16 * cross <= Cselect := by
        calc
          16 * cross <= (16 * cross) * (Cgeom * Cbin * K * Craw ^ (3 : Nat)) :=
            le_mul_of_one_le_right zero_le
              (one_le_mul (one_le_mul (one_le_mul hCgeom hCbin) hK) (one_le_pow₀ hCraw))
          _ = Cselect := by dsimp only [Cselect]; ring
      have hCselectPaid : Cselect <= Lpaid := by
        dsimp only [Lpaid]
        rw [Real.toNNReal_pow hbaseNonneg]
        exact le_mul_of_one_le_right zero_le (one_le_pow₀ hBdeltaOne)
      have hcrossPaid : 2 * (2 * cross) <= Lpaid ^ (2 : Nat) := by
        calc
          2 * (2 * cross) <= 16 * cross := by nlinarith
          _ <= Lpaid := hCselectCross.trans hCselectPaid
          _ <= Lpaid ^ (2 : Nat) := by
            simpa only [pow_one] using pow_le_pow_right₀ hLpaid (by norm_num : 1 <= 2)
      have hdebtNN : (2 * (2 * cross)) * Lpaid ^ (12 : Nat) <= Lpaid ^ (14 : Nat) := by
        calc
          _ <= Lpaid ^ (2 : Nat) * Lpaid ^ (12 : Nat) := mul_le_mul' hcrossPaid le_rfl
          _ = _ := by ring
      have hdebt : ((Lpaid : ENNReal) ^ (14 : Nat))⁻¹ <=
          ((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ *
            (((Lpaid : ENNReal) ^ (6 : Nat))⁻¹) ^ (2 : Nat) := by
        have h := ENNReal.inv_le_inv.mpr
          (show ((2 * (2 * cross) : NNReal) : ENNReal) * (Lpaid : ENNReal) ^ (12 : Nat) <=
            (Lpaid : ENNReal) ^ (14 : Nat) by exact_mod_cast hdebtNN)
        rw [ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.mpr hfourCross.ne'))
          (Or.inl ENNReal.coe_ne_top)] at h
        simpa only [ENNReal.inv_pow, ← pow_mul, show (6 : Nat) * 2 = 12 by rfl] using h
      have hcoarseFinal : ((Lpaid : ENNReal) ^ (14 : Nat))⁻¹ * (lambda : ENNReal) ^ (4 : Nat) <=
          fullness' Ja (fun R => (zeroExtend P2 (U.cover.tube block.a.val) Z2 R).toShadedBody) := by
        calc
          _ <= (((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ *
              (((Lpaid : ENNReal) ^ (6 : Nat))⁻¹) ^ (2 : Nat)) * (lambda : ENNReal) ^ (4 : Nat) :=
            mul_le_mul' hdebt le_rfl
          _ = ((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ *
              (((Lpaid : ENNReal) ^ (6 : Nat))⁻¹ * (lambda : ENNReal) ^ (2 : Nat)) ^ (2 : Nat) := by ring
          _ <= ((2 * (2 * cross) : NNReal) : ENNReal)⁻¹ * (lambdaB : ENNReal) ^ (2 : Nat) :=
            mul_le_mul' le_rfl (pow_le_pow_left' (hmiddle.trans_eq hlambdaB.symm) 2)
          _ <= _ := hcoarseOld
      let selectionsPaid := hselection_mono hLactual hpaid selections
      have hlambdaPos : 0 < (lambda : ENNReal) := by
        exact (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) ENNReal.coe_ne_top).trans_le
          (hlambda ▸ hfull)
      have hcoarseCoeffPos : 0 <
          ((Lpaid : ENNReal) ^ (14 : Nat))⁻¹ * (lambda : ENNReal) ^ (4 : Nat) := by
        exact ENNReal.mul_pos
          (ne_of_gt (ENNReal.inv_pos.mpr (ENNReal.pow_ne_top ENNReal.coe_ne_top)))
          (pow_ne_zero _ (ne_of_gt hlambdaPos))
      have hcoarsePos : 0 < fullness' Ja
          (fun R => (zeroExtend P2 (U.cover.tube block.a.val) Z2 R).toShadedBody) :=
        lt_of_lt_of_le hcoarseCoeffPos hcoarseFinal
      refine ⟨{ selections := selectionsPaid
                middleParents := mid
                coarseParents := P2
                commonMass := c
                raw_witness := ⟨H, c, Ja, Zmid, U.cover.tube block.a.val,
                  coarseAssign, m, rawData, hrawData⟩
                middle_fullness := ?_
                coarse_fullness := ?_
                coarse_fullness_pos := ?_ }, trivial⟩
      · change ((Lpaid : ENNReal) ^ (6 : Nat))⁻¹ *
          (fullness' A (fun i => (Y i).toShadedBody)) ^ (2 : Nat) <= _
        rw [← hlambda]
        exact hmiddle
      · change ((Lpaid : ENNReal) ^ (14 : Nat))⁻¹ *
          (fullness' A (fun i => (Y i).toShadedBody)) ^ (4 : Nat) <= _
        rw [← hlambda]
        exact hcoarseFinal
      · exact hcoarsePos
    )


end

end Kakeya.ml1Boot.TrialRestartW94
