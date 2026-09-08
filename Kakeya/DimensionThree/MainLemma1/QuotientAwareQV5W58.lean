module

public import Kakeya.DimensionThree.MainLemma1.QuotientAwareQV5SupportW58

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W58QuotientAwareQV5

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

structure FinalSecondFactorAtStopV5W58
    {delta Cd : NNReal} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N a b : Nat}
    (p : Params) (m M : Nat)
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (pre : PreSecondFactorLevelBPacketV5W58 (b := b) p U)
    (stop : StoppedTwoSourceV5W58 (a := a) (b := b) p m U pre) where
  cell : Finset iota
  v0 : E
  middleActive : Finset iota
  ZTauFinal : iota -> ShadedTube (Tube.gridScale delta N b) E
  coarseActive : Finset iota
  ZThetaFinal : iota -> ShadedTube (Tube.gridScale delta N stop.j) E
  lM : iota
  lamM : NNReal
  cell_subset : cell ⊆ stop.active
  cell_nonempty : cell.Nonempty
  cell_ball : forall k, k ∈ cell ->
    ((pre.ZTau k).translate v0).carrier ⊆ Metric.closedBall 0 1
  cell_mass_paid :
    (∑ k ∈ stop.active, volume (pre.ZTau k).shade) <=
      4 * (M : ENNReal) *
        ∑ k ∈ cell, volume ((pre.ZTau k).translate v0).shade
  cell_multiplicity_paid :
    ShadedBody.multiplicity stop.active
        (fun k => (pre.ZTau k).toShadedBody) <=
      4 * (M : ENNReal) * ShadedBody.multiplicity cell
        (fun k => ((pre.ZTau k).translate v0).toShadedBody)
  raw_parent : IsParentFamily stop.active (U.cover.tube b)
    ({stop.pJ} : Finset iota) (U.cover.tube stop.j)
    (U.nodeAncestor b stop.j)
  translated_parent : IsParentFamily stop.active
    (fun k => (U.cover.tube b k).translate v0)
    ({stop.pJ} : Finset iota)
    (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
    (U.nodeAncestor b stop.j)
  second_factor : IsOneScaleSelected
    ((((factorOneScale.C cell.card (Tube.gridScale delta N b))⁻¹ : NNReal) :
      ENNReal))
    ((factorOneScale.C cell.card (Tube.gridScale delta N b) : NNReal) : ENNReal)
    stop.active cell
    (zeroExtend cell (fun k => (U.cover.tube b k).translate v0)
      (fun k => (pre.ZTau k).translate v0))
    ({stop.pJ} : Finset iota)
    (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
    (U.nodeAncestor b stop.j)
    middleActive ZTauFinal coarseActive ZThetaFinal lM
    ((2 * factorOneScale.C cell.card
      (Tube.gridScale delta N b))⁻¹ * pre.mu0) lamM
  selected_parent_eq : lM = stop.pJ
  literal_active_source :
    fibre stop.active (U.nodeAncestor b stop.j) lM = stop.active
  selected_fullness_paid :
    ((((factorOneScale.C cell.card
        (Tube.gridScale delta N b))⁻¹ : NNReal) : ENNReal)) *
        (((4 : ENNReal) * (M : ENNReal))⁻¹ *
          (ShadedBody.fullness stop.active
            (fun k => (pre.ZTau k).toShadedBody) : ENNReal)) <=
      (lamM : ENNReal)
  frostman_final_active_levelA :
    frostmanConstIn
        (fibre stop.active (U.nodeAncestor b stop.j) lM)
        (fun k =>
          (selectedShade middleActive
            (zeroExtend cell (fun r => (U.cover.tube b r).translate v0)
              (fun r => (pre.ZTau r).translate v0))
            ZTauFinal k).toConvexSpaceBody)
        ((U.cover.tube a stop.q).translate v0).toConvexSpaceBody <=
      stop.kappa⁻¹ * completeLevelAFrostmanBudgetV5W58 delta N a b m p
  q_on_literal_active_source :
    (stop.j = 0 /\ Tube.gridScale delta N stop.j = 1 /\
      stop.kappa * (delta : ENNReal) ^ (3 * p.η m) <=
        normalizedQV5W58
          (Tube.gridScale delta N b / Tube.gridScale delta N stop.j)
          (fibre stop.active (U.nodeAncestor b stop.j) lM)) \/
    (0 < stop.j /\ QuotientScaledActiveQBandV5W58 delta
      (Tube.gridScale delta N b / Tube.gridScale delta N stop.j)
      (fibre stop.active (U.nodeAncestor b stop.j) lM)
      stop.kappa 1 (3 * p.η m))

theorem eventually_exists_preSecondFactor_levelB_v5_w58 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    (Cd : NNReal) (hCd : 1 <= Cd) (Kd cd : Nat) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      forall {iota : Type u} [DecidableEq iota]
        (s s2 sPrime : Finset iota) (V : iota -> ShadedTube delta E)
        (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
          (Tube.ssfGridLen delta) Cd)
        (a b m : Nat),
        (forall i, i ∈ s -> (V i).carrier ⊆ Metric.closedBall 0 1) ->
        s2 ⊆ s -> sPrime ⊆ s2 -> sPrime.Nonempty ->
        (forall t, t ⊆ s2 -> t.Nonempty ->
          (delta : ENNReal) ^ p.η 0 <=
            (ShadedBody.fullness t
              (fun i => (V i).toShadedBody) : ENNReal)) ->
        StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
        Nonempty (PreSecondFactorLevelBPacketV5W58
          (b := b) p U) := by
  filter_upwards [self_mem_nhdsWithin,
      eventually_le_nhdsGT (c := (1 / 2 : NNReal)) (by norm_num)] with
    delta hdelta0 hdeltaHalf
  intro iota _ s s2 sPrime V U a b m hball hs2s hsPrimeSub hsPrimeNe hhered hblock
  have hdelta1 : delta <= 1 := hdeltaHalf.trans (by norm_num)
  have hdeltaLtOne : delta < 1 := hdeltaHalf.trans_lt (by norm_num)
  obtain ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
      htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
      hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
      hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta⟩ :=
    W50Upstream.exists_blockSkeleton_counted_upstream_w50
      U hblock.coarse_lt_fine.le hblock.fine_le hsPrimeNe
  have hscales := caseTwoThreePassScales hdelta1 U
    hblock.coarse_lt_fine.le hblock.fine_le
  have hdeltaTau : delta <= Tube.gridScale delta (Tube.ssfGridLen delta) b :=
    hscales.1.1
  have hTauOne : Tube.gridScale delta (Tube.ssfGridLen delta) b <= 1 :=
    hscales.1.2.1.trans hscales.1.2.2
  have hTau0 : 0 < Tube.gridScale delta (Tube.ssfGridLen delta) b :=
    Tube.gridScale_pos hdelta0 _ _
  have hballPrime : forall i, i ∈ sPrime ->
      (V i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    exact hball i (hs2s (hsPrimeSub hi))
  have hdensRaw : forall i, i ∈ s2 ->
      (delta : ENNReal) ^ p.η 0 * volume (V i).carrier <=
        volume (V i).shade := by
    intro i hi
    have hfull := hhered ({i} : Finset iota)
      (Finset.singleton_subset_iff.mpr hi) (by simp)
    have hsum := ShadedBody.sum_volumeReal_shade_eq_fullness_mul
      ({i} : Finset iota) (fun j => (V j).toShadedBody)
    have hsingle :
        volume (V i).shade =
          (ShadedBody.fullness ({i} : Finset iota)
            (fun j => (V j).toShadedBody) : ENNReal) * volume (V i).carrier := by
      simpa using hsum
    exact (mul_le_mul_left hfull _).trans_eq hsingle.symm
  have hdens : forall i, i ∈ sPrime ->
      ((1 : NNReal) : ENNReal)⁻¹ *
          (((delta ^ p.η 0 : NNReal) : ENNReal)) * volume (V i).carrier <=
        volume (V i).shade := by
    intro i hi
    simpa [ENNReal.coe_rpow_of_ne_zero hdelta0.ne'] using
      (hdensRaw i (hsPrimeSub hi))
  have hvolpos : forall i : iota, 0 < volume (V i).carrier := by
    intro i
    exact (tube_volume_pos_ne_top (E := E) hdelta0 (V i).toTube).1
  have hs0 : ∑ i ∈ sPrime, volume (V i).carrier ≠ 0 := by
    obtain ⟨i0, hi0⟩ := hsPrimeNe
    exact ne_of_gt (lt_of_lt_of_le (hvolpos i0)
      (Finset.single_le_sum (f := fun i => volume (V i).carrier)
        (fun _ _ => (by simp : (0 : ENNReal) <= _)) hi0))
  have hpos : 0 < ∑ i ∈ sPrime, volume (V i).shade :=
    sum_shade_pos_of_fullness_ge hdelta0 V
      (hhered sPrime hsPrimeSub hsPrimeNe)
  obtain ⟨fineActive, Zf, tAct, ZTau, kF, lamF, hfirst⟩ :=
    exists_isOneScaleSelected_of_dens (E := E) hdim hdelta0 hdeltaTau hTauOne
      (amb := sPrime) (act := sPrime) (hact := by intro i hi; exact hi)
      V (U.cover.tube b) pTau
      (hoff := by intro i hi hnot; exact False.elim (hnot hi))
      hballPrime (lam := delta ^ p.η 0) (Cd := 1)
      (by norm_num : (1 : NNReal) <= 1) hdens hs0 hparentFine hpos
  let lamP : NNReal :=
    ((1 * factorOneScale.C sPrime.card delta)⁻¹ * delta ^ p.η 0)
  have hfirst' : IsOneScaleSelected
      ((((factorOneScale.C sPrime.card delta)⁻¹ : NNReal) : ENNReal))
      ((factorOneScale.C sPrime.card delta : NNReal) : ENNReal)
      sPrime sPrime V tTau (U.cover.tube b) pTau
      fineActive Zf tAct ZTau kF lamP lamF := by
    simpa [lamP] using hfirst
  have hlamP0 : 0 < lamP := by
    have hC0 : 0 < factorOneScale.C sPrime.card delta :=
      lt_of_lt_of_le zero_lt_one (one_le_factorOneScale_C _ _)
    exact mul_pos (inv_pos.mpr (by simpa using hC0)) (NNReal.rpow_pos hdelta0)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hlamP0 hdeltaLtOne
  let regularizationExponent : Real := n
  have hpoly : (delta : ENNReal) ^ regularizationExponent <= (lamP : ENNReal) := by
    have hpow : ((delta ^ n : NNReal) : ENNReal) <= (lamP : ENNReal) :=
      ENNReal.coe_le_coe.mpr hn.le
    simpa [regularizationExponent, ENNReal.rpow_natCast] using hpow
  obtain ⟨mid, hmid, hmidNe, muE, hmuE, hbandE, hmult, hfull, hcard,
      _hinc, _hsum⟩ :=
    regularizeOnFixedTree (E := E) hTau0 hfirst'.parent_subset
      (fun _ => ()) ({()} : Finset Unit) (by simp) ZTau
      ⟨kF, hfirst'.sel_mem⟩ hlamP0 hfirst'.parent_fullness hpoly
  have hmidNonempty : mid.Nonempty := hmidNe
  obtain ⟨k0, hk0⟩ := hmidNe
  have hvol := tube_volume_pos_ne_top (E := E) hTau0 (ZTau k0).toTube
  have hshade : volume (ZTau k0).shade <= volume (ZTau k0).carrier :=
    measure_mono (ZTau k0).shade_subset
  have hle1 : ((2 : NNReal) : ENNReal)⁻¹ * muE <= 1 := by
    have hmul : ((2 : NNReal) : ENNReal)⁻¹ * muE * volume (ZTau k0).carrier <=
        1 * volume (ZTau k0).carrier := by
      simpa [one_mul] using ((hbandE k0 hk0).1.trans hshade)
    have hdiv := ENNReal.div_le_div_right hmul (volume (ZTau k0).carrier)
    rwa [ENNReal.mul_div_cancel_right hvol.1.ne' hvol.2,
      ENNReal.mul_div_cancel_right hvol.1.ne' hvol.2] at hdiv
  have hmuETop : muE ≠ ⊤ := by
    intro htop
    rw [htop] at hle1
    simp at hle1
  let mu0 : NNReal := muE.toNNReal
  have hmu0pos : 0 < mu0 := by
    simpa [mu0] using ENNReal.toNNReal_pos hmuE.ne' hmuETop
  have hband : forall k, k ∈ mid ->
      ((2 : NNReal) : ENNReal)⁻¹ * (mu0 : ENNReal) * volume (ZTau k).carrier <=
          volume (ZTau k).shade /\
        volume (ZTau k).shade <=
          ((2 : NNReal) : ENNReal) * (mu0 : ENNReal) * volume (ZTau k).carrier := by
    intro k hk
    simpa [mu0, ENNReal.coe_toNNReal hmuETop] using hbandE k hk
  exact ⟨{
    tTau := tTau
    pTau := pTau
    repTau := repTau
    fineActive := fineActive
    Zf := Zf
    tAct := tAct
    ZTau := ZTau
    kF := kF
    lamP := lamP
    lamF := lamF
    regularizationExponent := regularizationExponent
    mid := mid
    mu0 := mu0
    tau_subset := htTau
    tau_map_mem := hpTau
    tau_map_is_representative := hpTauRep
    tau_represents_every_body := hrepTau
    tau_representative_onto := hontoTau
    tau_selected_body := hpTauBody
    fine_parent := hparentFine
    lamP_exact := rfl
    first_factor := hfirst'
    lamP_funded := hpoly
    mid_subset := hmid
    mid_nonempty := hmidNonempty
    mu0_pos := hmu0pos
    middle_tube := fun k hk => hfirst'.parent_tube k (hmid hk)
    density_band := hband
    regularization_multiplicity := hmult
    regularization_fullness := hfull
    regularization_card := hcard }⟩

theorem frostman_mul_Q_cancel_retainedShare_v5_w58
    {kappa A B Factive Qactive : ENNReal}
    (hk0 : kappa ≠ 0) (hkTop : kappa ≠ ⊤)
    (hF : Factive <= kappa⁻¹ * A)
    (hQ : Qactive <= kappa * B) :
    Factive * Qactive <= A * B := by
  calc
    Factive * Qactive <= (kappa⁻¹ * A) * (kappa * B) :=
      mul_le_mul' hF hQ
    _ = (kappa⁻¹ * kappa) * (A * B) := by ac_rfl
    _ = A * B := by rw [ENNReal.inv_mul_cancel hk0 hkTop, one_mul]

theorem eventually_exists_finalSecondFactor_of_stopped_v5_w58
    [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    (Cd : NNReal) (hCd : 1 <= Cd) (Kd cd : Nat) :
    exists M : Nat, 0 < M /\
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        forall {iota : Type u} [DecidableEq iota]
          {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
          (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
            (Tube.ssfGridLen delta) Cd)
          (a b m : Nat)
          (pre : PreSecondFactorLevelBPacketV5W58 (b := b) p U)
          (stop : StoppedTwoSourceV5W58
            (a := a) (b := b) p m U pre),
          (forall i, i ∈ sPrime ->
            (V i).carrier ⊆ Metric.closedBall 0 1) ->
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
              p.η p.ε a b m p.N ->
          Nonempty (FinalSecondFactorAtStopV5W58
            (a := a) (b := b) p m M U pre stop) := by
  classical
  obtain ⟨M, hM, hcell⟩ :=
    exists_unitBallCell_productInput (E := E) 4 (by norm_num)
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_rpow_le_quarter hp.epsPos,
      self_mem_nhdsWithin]
    with delta hsmall hdelta0
  intro iota _ sPrime V U a b m pre stop hball hblock
  have hdelta1 : delta <= 1 := hsmall.1
  have hsPrime : sPrime.Nonempty := by
    obtain ⟨k, hk⟩ := stop.active_nonempty
    have hkLevel : k ∈ U.cover.indexSet b :=
      stop.complete_subset_levelB (stop.active_subset_complete hk)
    obtain ⟨i, hi, _hassign⟩ := stop.parents.nodes_carry_leaf k hkLevel
    exact ⟨i, hi⟩
  have hactiveNodes : stop.active ⊆ U.cover.indexSet b :=
    stop.active_subset_complete.trans stop.complete_subset_levelB
  have hjb : stop.j <= b :=
    stop.level_le.trans hblock.coarse_lt_fine.le
  have hTauTheta :
      Tube.gridScale delta (Tube.ssfGridLen delta) b <=
        Tube.gridScale delta (Tube.ssfGridLen delta) stop.j :=
    Tube.gridScale_antitone hdelta0 hdelta1 _ hjb
  have hThetaOne :
      Tube.gridScale delta (Tube.ssfGridLen delta) stop.j <= 1 :=
    Tube.gridScale_le_one hdelta1 _ _
  have hsep : Tube.gridScale delta (Tube.ssfGridLen delta) b <=
      delta ^ p.ε * Tube.gridScale delta (Tube.ssfGridLen delta) a := by
    exact NNReal.coe_le_coe.mp (by
      rw [NNReal.coe_mul, NNReal.coe_rpow]
      exact hblock.separated)
  have hTauQuarter : Tube.gridScale delta (Tube.ssfGridLen delta) b <=
      (1 / 4 : NNReal) := by
    calc
      Tube.gridScale delta (Tube.ssfGridLen delta) b <=
          delta ^ p.ε * Tube.gridScale delta (Tube.ssfGridLen delta) a := hsep
      _ <= delta ^ p.ε * 1 := by
        gcongr
        exact Tube.gridScale_le_one hdelta1 _ _
      _ = delta ^ p.ε := by rw [mul_one]
      _ <= (1 / 4 : NNReal) := by exact_mod_cast hsmall.2
  have hTauQuarterReal :
      ((Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : Real) <=
        1 / 4 := by
    exact_mod_cast hTauQuarter
  have hTau0 : 0 < Tube.gridScale delta (Tube.ssfGridLen delta) b :=
    Tube.gridScale_pos hdelta0 _ _
  have hactiveBall : forall k, k ∈ stop.active ->
      (pre.ZTau k).carrier ⊆ Metric.closedBall (0 : E) 4 := by
    intro k hk
    rw [show (pre.ZTau k).carrier = (U.cover.tube b k).carrier by
      exact congrArg
        (fun W : Tube (Tube.gridScale delta (Tube.ssfGridLen delta) b) E =>
          W.carrier)
        (pre.middle_tube k (stop.active_subset_mid hk))]
    exact MultiScaleFac.node_carrier_subset_ball hdelta0 hdelta1 U hsPrime
      hball hblock.fine_le (hactiveNodes hk)
  obtain ⟨cell, hcellSub, v0, hcellNe, hcellMass, hcellBall,
      _hcellFull, hmassRet, hmultRet⟩ :=
    hcell hTau0 hTauQuarterReal stop.active pre.ZTau
      stop.active_mass_pos hactiveBall
  let W : iota -> ShadedTube
      (Tube.gridScale delta (Tube.ssfGridLen delta) b) E :=
    zeroExtend cell (fun k => (U.cover.tube b k).translate v0)
      (fun k => (pre.ZTau k).translate v0)
  have hcellMid : cell ⊆ pre.mid :=
    hcellSub.trans stop.active_subset_mid
  have hWmem : forall k, k ∈ cell -> W k = (pre.ZTau k).translate v0 := by
    intro k hk
    simp [W, zeroExtend, hk]
  have hWtube : forall k,
      (W k).toTube = (U.cover.tube b k).translate v0 := by
    exact zeroExtend_toTube fun k hk => by
      rw [StickyKakeya.shadedTube_translate_toTube,
        pre.middle_tube k (hcellMid hk)]
  have hoff : forall k, k ∈ stop.active -> k ∉ cell ->
      (W k).shade = ∅ := by
    intro k _hk hkc
    exact zeroExtend_shade_of_not_mem hkc
  have hballW : forall k, k ∈ cell ->
      (W k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk
    rw [hWmem k hk]
    exact hcellBall k hk
  have hdensW : forall k, k ∈ cell ->
      ((2 : NNReal) : ENNReal)⁻¹ * (pre.mu0 : ENNReal) *
          volume (W k).carrier <= volume (W k).shade := by
    intro k hk
    rw [hWmem k hk]
    simpa [MeasureTheory.measure_vadd] using
      (pre.density_band k (hcellMid hk)).1
  have hcarrierSum : ∑ k ∈ cell, volume (W k).carrier ≠ 0 := by
    obtain ⟨k, hk⟩ := hcellNe
    have hkpos : 0 < volume (W k).carrier := by
      rw [hWmem k hk]
      simpa [MeasureTheory.measure_vadd] using
        (tube_volume_pos_ne_top (E := E) hTau0 (pre.ZTau k).toTube).1
    exact ne_of_gt (lt_of_lt_of_le hkpos
      (Finset.single_le_sum
        (f := fun j => volume (W j).carrier)
        (fun _ _ => (by simp : (0 : ENNReal) <= _)) hk))
  have hconstant : forall k, k ∈ stop.active ->
      U.nodeAncestor b stop.j k = stop.pJ :=
    stop.active_constant_at_stop
  have hrawParent : IsParentFamily stop.active (U.cover.tube b)
      ({stop.pJ} : Finset iota) (U.cover.tube stop.j)
      (U.nodeAncestor b stop.j) := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp [hconstant k hk]
    · intro q hq q' hq' _heq
      simpa using
        (Finset.mem_singleton.mp hq).trans
          (Finset.mem_singleton.mp hq').symm
    · intro k hk
      have hle := U.tube_le_tube_nodeAncestor hjb hblock.fine_le hsPrime
        (hactiveNodes hk)
      simpa [hconstant k hk] using hle
  have htranslatedParent : IsParentFamily stop.active
      (fun k => (U.cover.tube b k).translate v0)
      ({stop.pJ} : Finset iota)
      (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
      (U.nodeAncestor b stop.j) := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp [hconstant k hk]
    · intro q hq q' hq' _heq
      simpa using
        (Finset.mem_singleton.mp hq).trans
          (Finset.mem_singleton.mp hq').symm
    · intro k hk
      have hle := U.tube_le_tube_nodeAncestor hjb hblock.fine_le hsPrime
        (hactiveNodes hk)
      rw [hconstant k hk] at hle
      exact translate_le_translate v0 hle
  have hparentCell : IsParentFamily cell (fun k => (W k).toTube)
      ({stop.pJ} : Finset iota)
      (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
      (U.nodeAncestor b stop.j) := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      simp [hconstant k (hcellSub hk)]
    · intro q hq q' hq' _heq
      simpa using
        (Finset.mem_singleton.mp hq).trans
          (Finset.mem_singleton.mp hq').symm
    · intro k hk
      rw [hWtube k]
      have hle := U.tube_le_tube_nodeAncestor hjb hblock.fine_le hsPrime
        (hactiveNodes (hcellSub hk))
      rw [hconstant k (hcellSub hk)] at hle
      exact translate_le_translate v0 hle
  have hcellMassW : 0 < ∑ k ∈ cell, volume (W k).shade := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [hWmem k hk])]
    exact hcellMass
  obtain ⟨middleActive, ZTauFinal, coarseActive, ZThetaFinal,
      lM, lamM, h2⟩ :=
    exists_isOneScaleSelected_of_dens (E := E) hdim hTau0 hTauTheta
      hThetaOne hcellSub W
      (fun _ => (U.cover.tube stop.j stop.pJ).translate v0)
      (U.nodeAncestor b stop.j) hoff hballW
      (by norm_num : (1 : NNReal) <= 2) hdensW hcarrierSum
      hparentCell hcellMassW
  have hlM : lM = stop.pJ := by
    have hlMmem : lM ∈ ({stop.pJ} : Finset iota) :=
      h2.parent_subset h2.sel_mem
    exact Finset.mem_singleton.mp hlMmem
  have hfibre : fibre stop.active (U.nodeAncestor b stop.j) lM =
      stop.active := by
    rw [hlM]
    ext k
    constructor
    · intro hk
      exact (Finset.mem_filter.mp hk).1
    · intro hk
      exact Finset.mem_filter.mpr ⟨hk, hconstant k hk⟩
  have hTbase : forall k, k ∈ stop.active ->
      U.cover.tube b k = (pre.ZTau k).toTube := by
    intro k hk
    exact (pre.middle_tube k (stop.active_subset_mid hk)).symm
  have hD0 : (4 : ENNReal) * (M : ENNReal) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hM.ne')
  have hDtop : (4 : ENNReal) * (M : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hlam :=
    W48SelectedFreshStopProducer.secondSelected_lam_lower_of_ballMassRetention
      (E := E) hTau0
      (Tube.gridScale_le_one hdelta1 (Tube.ssfGridLen delta) b)
      stop.active_nonempty hcellSub hTbase hD0 hDtop hmassRet
      (by simpa [W] using h2)
  have hselectedTube : forall k,
      (selectedShade middleActive W ZTauFinal k).toTube =
        (U.cover.tube b k).translate v0 := by
    intro k
    calc
      (selectedShade middleActive W ZTauFinal k).toTube = (W k).toTube :=
        selectedShade_toTube (fun q hq => (h2.child_shade q hq).1) k
      _ = (U.cover.tube b k).translate v0 := hWtube k
  have hfrost :
      frostmanConstIn
          (fibre stop.active (U.nodeAncestor b stop.j) lM)
          (fun k =>
            (selectedShade middleActive W ZTauFinal k).toConvexSpaceBody)
          ((U.cover.tube a stop.q).translate v0).toConvexSpaceBody <=
        stop.kappa⁻¹ * completeLevelAFrostmanBudgetV5W58
          delta (Tube.ssfGridLen delta) a b m p := by
    rw [hfibre]
    rw [frostmanConstIn_congr stop.active
      (fun k _hk => congrArg
        (fun T : Tube (Tube.gridScale delta (Tube.ssfGridLen delta) b) E =>
          T.toConvexSpaceBody)
        (hselectedTube k))
      ((U.cover.tube a stop.q).translate v0).toConvexSpaceBody]
    rw [show ((U.cover.tube a stop.q).translate v0).toConvexSpaceBody =
        ConvexSpaceBody.translate
          (U.cover.tube a stop.q).toConvexSpaceBody v0 from rfl]
    change frostmanConstIn stop.active
        (fun k => ConvexSpaceBody.translate
          (U.cover.tube b k).toConvexSpaceBody v0)
        (ConvexSpaceBody.translate
          (U.cover.tube a stop.q).toConvexSpaceBody v0) <= _
    rw [W54ModuleSafeMiddleProducer.frostmanConstIn_translate_w54]
    exact stop.frostman_active_levelA
  refine ⟨{
    cell := cell
    v0 := v0
    middleActive := middleActive
    ZTauFinal := ZTauFinal
    coarseActive := coarseActive
    ZThetaFinal := ZThetaFinal
    lM := lM
    lamM := lamM
    cell_subset := hcellSub
    cell_nonempty := hcellNe
    cell_ball := hcellBall
    cell_mass_paid := hmassRet
    cell_multiplicity_paid := hmultRet
    raw_parent := hrawParent
    translated_parent := htranslatedParent
    second_factor := by simpa [W] using h2
    selected_parent_eq := hlM
    literal_active_source := hfibre
    selected_fullness_paid := by simpa [W] using hlam
    frostman_final_active_levelA := by simpa [W] using hfrost
    q_on_literal_active_source := by
      simpa [hfibre] using stop.endpoint_or_nonTop_active_scaled }⟩

theorem eventually_exists_twoSourceStop_then_finalSecondFactor_v5_w58
    [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    (Cd : NNReal) (hCd : 1 <= Cd) (Kd cd : Nat) :
    exists M : Nat, 0 < M /\
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        forall {iota : Type u} [DecidableEq iota]
          (s s2 sPrime : Finset iota) (V : iota -> ShadedTube delta E)
          (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
            (Tube.ssfGridLen delta) Cd)
          (a b m : Nat),
          (forall i, i ∈ s -> (V i).carrier ⊆ Metric.closedBall 0 1) ->
          s2 ⊆ s -> sPrime ⊆ s2 -> sPrime.Nonempty ->
          (forall t, t ⊆ s2 -> t.Nonempty ->
            (delta : ENNReal) ^ p.η 0 <=
              (ShadedBody.fullness t
                (fun i => (V i).toShadedBody) : ENNReal)) ->
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
              p.η p.ε a b m p.N ->
          exists pre : PreSecondFactorLevelBPacketV5W58
              (b := b) p U,
            exists stop : StoppedTwoSourceV5W58
              (a := a) (b := b) p m U pre,
              Nonempty (FinalSecondFactorAtStopV5W58
                (a := a) (b := b) p m M U pre stop) := by
  obtain ⟨M, hM, hfinal⟩ :=
    eventually_exists_finalSecondFactor_of_stopped_v5_w58 (E := E) hdim hp Cd hCd Kd cd
  refine ⟨M, hM, ?_⟩
  have hpre :=
    eventually_exists_preSecondFactor_levelB_v5_w58 (E := E) hdim hp Cd hCd Kd cd
  have hstop :=
    eventually_exists_stoppedTwoSource_of_preSecond_v5_w58
      (E := E) hdim hp Cd hCd Kd cd
  filter_upwards [hpre, hstop, hfinal]
    with delta hpreDelta hstopDelta hfinalDelta
  intro iota _ s s2 sPrime V U a b m hball hs2s hsPrimeSub
    hsPrimeNe hhered hblock
  obtain ⟨pre⟩ :=
    hpreDelta s s2 sPrime V U a b m hball hs2s hsPrimeSub
      hsPrimeNe hhered hblock
  obtain ⟨stop⟩ := hstopDelta U a b m pre hblock
  have hballPrime : forall i, i ∈ sPrime ->
      (V i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    exact hball i (hs2s (hsPrimeSub hi))
  exact ⟨pre, stop, hfinalDelta U a b m pre stop hballPrime hblock⟩

theorem rawMiddle_le_target_mul_quotientResidual_v5_w58
    {iota : Type u}
    {delta qStop : NNReal}
    {active complete : Finset iota}
    {betaPrime gamma zeta zD zQ eM : Real}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1) (hq0 : 0 < qStop)
    (hbeta0 : 0 <= betaPrime) (hbeta1 : betaPrime <= 1)
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hbetaGamma : betaPrime <= gamma)
    (_hzeta : 0 <= zeta) (_hzD : 0 <= zD) (hzQ : 0 <= zQ)
    {Mactive Delta : ENNReal} {CDelta CQ : NNReal}
    (_hCDelta : 1 <= CDelta) (hCQ : 1 <= CQ)
    (hk0 : retainedShareV5W58 active complete ≠ 0)
    (hkTop : retainedShareV5W58 active complete ≠ ⊤)
    (hk1 : retainedShareV5W58 active complete <= 1)
    (hQidentity : normalizedQV5W58 qStop active =
      retainedShareV5W58 active complete *
        normalizedQV5W58 qStop complete)
    (hraw : Mactive <=
      (delta : ENNReal) ^ (-eM) * Delta ^ (1 - betaPrime) *
        (active.card : ENNReal) ^ betaPrime)
    (hDelta : Delta <=
      (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD))
    (hCompleteQ : SymmetricCompleteQBandV5W58
      delta qStop complete CQ zQ)
    (hsep : qStop <= delta ^ (zeta / 5)) :
    Mactive <=
      (CDelta : ENNReal) ^ (1 - betaPrime) * (CQ : ENNReal) *
      (delta : ENNReal) ^
        (-eM - (1 - betaPrime) * zD - zQ +
          2 * zeta * (gamma - betaPrime) / 5) *
      (retainedShareV5W58 active complete) ^
        (betaPrime + gamma / 2 - 1) *
      (qStop : ENNReal) ^ (-2 * gamma) *
      (normalizedQV5W58 qStop active) ^ (1 - gamma / 2) := by
  have hdeltaE0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaEtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hqE0 : (qStop : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hq0.ne'
  have hqEtop : (qStop : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCQ0 : (CQ : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hCQ).ne'
  have hCQtop : (CQ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCDtop : (CDelta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdeltaZ0 : (delta : ENNReal) ^ zQ ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hdeltaE0, hdeltaEtop]
  have hdeltaNZtop : (delta : ENNReal) ^ (-zQ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hdeltaE0 hdeltaEtop
  have hdeltaNZDtop : (delta : ENNReal) ^ (-zD) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hdeltaE0 hdeltaEtop
  let kappa : ENNReal := retainedShareV5W58 active complete
  let QA : ENNReal := normalizedQV5W58 qStop active
  let QC : ENNReal := normalizedQV5W58 qStop complete
  let d : Real := betaPrime + gamma / 2 - 1
  let g : Real := gamma - betaPrime
  let h : Real := 1 - gamma / 2
  have hk0' : kappa ≠ 0 := by simpa [kappa] using hk0
  have hkTop' : kappa ≠ ⊤ := by simpa [kappa] using hkTop
  have _hk1' : kappa ≤ 1 := by simpa [kappa] using hk1
  have hQid : QA = kappa * QC := by
    simpa [QA, QC, kappa] using hQidentity
  have hQlo : (CQ : ENNReal) ^ (-1 : Real) *
      (delta : ENNReal) ^ zQ ≤ QC := by
    exact hCompleteQ.1
  have hQhi : QC ≤
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) := by
    exact hCompleteQ.2
  have hQlo' : (CQ : ENNReal)⁻¹ *
      (delta : ENNReal) ^ zQ ≤ QC := by
    simpa [ENNReal.rpow_neg] using hQlo
  have hQleft0 : (CQ : ENNReal) ^ (-1 : Real) *
      (delta : ENNReal) ^ zQ ≠ 0 := by
    apply mul_ne_zero
    · simp [ENNReal.rpow_eq_zero_iff, hCQ0, hCQtop]
    · exact hdeltaZ0
  have hQC0 : QC ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hQleft0) hQlo)
  have hQCtop : QC ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hCQtop hdeltaNZtop) hQhi
  have hQA0 : QA ≠ 0 := by
    rw [hQid]
    exact mul_ne_zero hk0' hQC0
  have hQAtop : QA ≠ ⊤ := by
    rw [hQid]
    exact ENNReal.mul_ne_top hkTop' hQCtop
  have hP0 : (active.card : ENNReal) ≠ 0 := by
    intro hP
    apply hQA0
    simp [QA, normalizedQV5W58, hP]
  have hPtop : (active.card : ENNReal) ≠ ⊤ := by simp
  have hq2top : (qStop : ENNReal) ^ (2 : Nat) ≠ ⊤ :=
    ENNReal.pow_ne_top hqEtop
  have hq2pow : ((qStop : ENNReal) ^ (2 : Nat)) ^ betaPrime =
      (qStop : ENNReal) ^ (2 * betaPrime) := by
    rw [pow_two]
    rw [ENNReal.mul_rpow_of_ne_top hqEtop hqEtop betaPrime]
    rw [← ENNReal.rpow_add (x := (qStop : ENNReal))
      betaPrime betaPrime hqE0 hqEtop]
    congr 1
    ring
  have hQApowBeta : QA ^ betaPrime =
      (qStop : ENNReal) ^ (2 * betaPrime) *
        (active.card : ENNReal) ^ betaPrime := by
    dsimp [QA, normalizedQV5W58]
    rw [ENNReal.mul_rpow_of_ne_top hq2top hPtop betaPrime, hq2pow]
  have hqneg_add : (qStop : ENNReal) ^ (-2 * betaPrime) *
      (qStop : ENNReal) ^ (2 * betaPrime) = 1 := by
    rw [← ENNReal.rpow_add (x := (qStop : ENNReal))
      (-2 * betaPrime) (2 * betaPrime) hqE0 hqEtop]
    rw [show -2 * betaPrime + 2 * betaPrime = 0 by ring]
    simp
  have hCardId : (active.card : ENNReal) ^ betaPrime =
      (qStop : ENNReal) ^ (-2 * betaPrime) * QA ^ betaPrime := by
    calc
      (active.card : ENNReal) ^ betaPrime =
          (qStop : ENNReal) ^ (-2 * betaPrime) *
            (qStop : ENNReal) ^ (2 * betaPrime) *
              (active.card : ENNReal) ^ betaPrime := by
        rw [hqneg_add]
        simp
      _ = (qStop : ENNReal) ^ (-2 * betaPrime) *
          ((qStop : ENNReal) ^ (2 * betaPrime) *
            (active.card : ENNReal) ^ betaPrime) := by
        rw [mul_assoc]
      _ = (qStop : ENNReal) ^ (-2 * betaPrime) * QA ^ betaPrime := by
        rw [← hQApowBeta]
  have hd0 : -1 ≤ d := by
    dsimp [d]
    linarith
  have hd1 : d ≤ 1 := by
    dsimp [d]
    linarith
  have hQApow : QA ^ betaPrime = QA ^ h * QA ^ d := by
    have hsum : h + d = betaPrime := by
      dsimp [h, d]
      ring
    calc
      QA ^ betaPrime = QA ^ (h + d) := by rw [hsum]
      _ = QA ^ h * QA ^ d :=
        ENNReal.rpow_add (x := QA) h d hQA0 hQAtop
  have hQAd : QA ^ d = kappa ^ d * QC ^ d := by
    rw [hQid, ENNReal.mul_rpow_of_ne_top hkTop' hQCtop]
  have hQCbracket : QC ^ d ≤
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) := by
    apply Kakeya.ml1Boot.bracket_rpow_le hdelta1 hCQ hzQ
    · exact hQlo'
    · exact hQhi
    · exact hd0
    · exact hd1
  have hcard : (active.card : ENNReal) ^ betaPrime ≤
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) *
        kappa ^ d * (qStop : ENNReal) ^ (-2 * betaPrime) * QA ^ h := by
    calc
      (active.card : ENNReal) ^ betaPrime =
          (qStop : ENNReal) ^ (-2 * betaPrime) * QA ^ betaPrime := hCardId
      _ = (qStop : ENNReal) ^ (-2 * betaPrime) *
          (QA ^ h * QA ^ d) := by rw [hQApow]
      _ = (qStop : ENNReal) ^ (-2 * betaPrime) *
          (QA ^ h * (kappa ^ d * QC ^ d)) := by rw [hQAd]
      _ ≤ (qStop : ENNReal) ^ (-2 * betaPrime) *
          (QA ^ h * (kappa ^ d *
            ((CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)))) := by
        gcongr
      _ = (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) *
          kappa ^ d * (qStop : ENNReal) ^ (-2 * betaPrime) * QA ^ h := by
        ac_rfl
  have hDeltaPow : Delta ^ (1 - betaPrime) ≤
      (CDelta : ENNReal) ^ (1 - betaPrime) *
        (delta : ENNReal) ^ (-(1 - betaPrime) * zD) := by
    calc
      Delta ^ (1 - betaPrime) ≤
          ((CDelta : ENNReal) * (delta : ENNReal) ^ (-zD)) ^
            (1 - betaPrime) :=
        ENNReal.rpow_le_rpow hDelta (by linarith)
      _ = (CDelta : ENNReal) ^ (1 - betaPrime) *
          ((delta : ENNReal) ^ (-zD)) ^ (1 - betaPrime) := by
        rw [ENNReal.mul_rpow_of_ne_top hCDtop hdeltaNZDtop]
      _ = (CDelta : ENNReal) ^ (1 - betaPrime) *
          (delta : ENNReal) ^ (-(1 - betaPrime) * zD) := by
        rw [← ENNReal.rpow_mul]
        congr 2
        ring
  have hg0 : 0 ≤ g := by
    dsimp [g]
    linarith
  have hsepE : (qStop : ENNReal) ≤
      (delta : ENNReal) ^ (zeta / 5) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta0.ne']
    exact_mod_cast hsep
  have hgain : (qStop : ENNReal) ^ (2 * g) ≤
      (delta : ENNReal) ^ (2 * zeta * g / 5) := by
    calc
      (qStop : ENNReal) ^ (2 * g) ≤
          ((delta : ENNReal) ^ (zeta / 5)) ^ (2 * g) :=
        ENNReal.rpow_le_rpow hsepE (by positivity)
      _ = (delta : ENNReal) ^ (2 * zeta * g / 5) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
  have hqfactor : (qStop : ENNReal) ^ (-2 * betaPrime) =
      (qStop : ENNReal) ^ (-2 * gamma) *
        (qStop : ENNReal) ^ (2 * g) := by
    calc
      (qStop : ENNReal) ^ (-2 * betaPrime) =
          (qStop : ENNReal) ^ (-2 * gamma + 2 * g) := by
        congr 1
        dsimp [g]
        ring
      _ = (qStop : ENNReal) ^ (-2 * gamma) *
          (qStop : ENNReal) ^ (2 * g) :=
        ENNReal.rpow_add (-2 * gamma) (2 * g) hqE0 hqEtop
  have hdeltaCombine :
      (delta : ENNReal) ^ (-eM) *
          (delta : ENNReal) ^ (-(1 - betaPrime) * zD) *
          (delta : ENNReal) ^ (-zQ) *
          (delta : ENNReal) ^ (2 * zeta * g / 5) =
        (delta : ENNReal) ^
          (-eM - (1 - betaPrime) * zD - zQ +
            2 * zeta * g / 5) := by
    rw [← ENNReal.rpow_add (-eM) (-(1 - betaPrime) * zD)
      hdeltaE0 hdeltaEtop]
    rw [← ENNReal.rpow_add
      (-eM + -(1 - betaPrime) * zD) (-zQ) hdeltaE0 hdeltaEtop]
    rw [← ENNReal.rpow_add
      (-eM + -(1 - betaPrime) * zD + -zQ)
        (2 * zeta * g / 5) hdeltaE0 hdeltaEtop]
    congr 1
    ring
  calc
    Mactive ≤ (delta : ENNReal) ^ (-eM) *
        Delta ^ (1 - betaPrime) *
        (active.card : ENNReal) ^ betaPrime := hraw
    _ ≤ (delta : ENNReal) ^ (-eM) *
        ((CDelta : ENNReal) ^ (1 - betaPrime) *
          (delta : ENNReal) ^ (-(1 - betaPrime) * zD)) *
        ((CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) *
          kappa ^ d * (qStop : ENNReal) ^ (-2 * betaPrime) * QA ^ h) := by
      gcongr
    _ = (CDelta : ENNReal) ^ (1 - betaPrime) * (CQ : ENNReal) *
        ((delta : ENNReal) ^ (-eM) *
          (delta : ENNReal) ^ (-(1 - betaPrime) * zD) *
          (delta : ENNReal) ^ (-zQ)) *
        kappa ^ d *
        ((qStop : ENNReal) ^ (-2 * gamma) *
          (qStop : ENNReal) ^ (2 * g)) * QA ^ h := by
      rw [hqfactor]
      ac_rfl
    _ ≤ (CDelta : ENNReal) ^ (1 - betaPrime) * (CQ : ENNReal) *
        ((delta : ENNReal) ^ (-eM) *
          (delta : ENNReal) ^ (-(1 - betaPrime) * zD) *
          (delta : ENNReal) ^ (-zQ)) *
        kappa ^ d *
        ((qStop : ENNReal) ^ (-2 * gamma) *
          (delta : ENNReal) ^ (2 * zeta * g / 5)) * QA ^ h := by
      gcongr
    _ = (CDelta : ENNReal) ^ (1 - betaPrime) * (CQ : ENNReal) *
        (delta : ENNReal) ^
          (-eM - (1 - betaPrime) * zD - zQ +
            2 * zeta * (gamma - betaPrime) / 5) *
        (retainedShareV5W58 active complete) ^
          (betaPrime + gamma / 2 - 1) *
        (qStop : ENNReal) ^ (-2 * gamma) *
        (normalizedQV5W58 qStop active) ^ (1 - gamma / 2) := by
      dsimp [QA, kappa, d, h]
      rw [← hdeltaCombine]
      dsimp [g]
      ac_rfl

end

end Kakeya.ml1Boot.W58QuotientAwareQV5
