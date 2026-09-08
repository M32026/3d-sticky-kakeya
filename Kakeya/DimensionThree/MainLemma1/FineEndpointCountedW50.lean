module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.W45FullLevelBodyInj
public import Kakeya.DimensionThree.MainLemma1.Rescaling.UniformEveryScale

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50EndpointCounted

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/- A pairwise essentially distinct leaf family has injectively indexed convex bodies. -/
theorem body_injOn_of_pairwiseED_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    (hdelta0 : 0 < delta)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)) :
    Set.InjOn (fun i => (T i).toConvexSpaceBody) (s : Set iota) := by
  have hcar := injOn_carrier_of_pairwise_essentiallyDistinct
    (E := E) hdelta0 s (fun i => (T i).toTube) hED
  intro i hi j hj hbody
  apply hcar hi hj
  exact congrArg (fun K : ConvexSpaceBody E => K.carrier) hbody

/- At the terminal level the representative parent map is injective on every retained leaf
   family, even when the hierarchy itself had duplicate bodies.  The proof uses the leaf-to-node
   carrier equality before deduplication and the representative body equality after deduplication. -/
theorem counted_terminal_parent_injOn_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {N : Nat} {C : NNReal}
    (hN : 0 < N)
    (U : Tube.UniformTubeSet s (fun i => (T i).toTube) N C)
    (hdelta0 : 0 < delta)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    {t : Finset iota} {pTau repTau : iota -> iota}
    (hpTauRep : forall i, i ∈ s -> pTau i = repTau (U.cover.assign N i))
    (hrep : forall j, j ∈ U.cover.indexSet N ->
      repTau j ∈ t ∧
        (U.cover.tube N (repTau j)).toConvexSpaceBody =
          (U.cover.tube N j).toConvexSpaceBody) :
    Set.InjOn pTau (s : Set iota) := by
  have hbody := body_injOn_of_pairwiseED_w50
    (E := E) hdelta0 hED
  intro i hi j hj hp
  apply hbody hi hj
  have hai : U.cover.assign N i ∈ U.cover.indexSet N :=
    U.cover.assign_mem N le_rfl i hi
  have haj : U.cover.assign N j ∈ U.cover.indexSet N :=
    U.cover.assign_mem N le_rfl j hj
  have hleaf_i : (T i).toConvexSpaceBody =
      (U.cover.tube N (pTau i)).toConvexSpaceBody := by
    calc
      (T i).toConvexSpaceBody =
          (W44FullNode.fullNodeFamily T hN U (U.cover.assign N i)).toConvexSpaceBody :=
        W44FullNode.leaf_body_eq_assigned_fullNode T hN U hi
      _ = (U.cover.tube N (U.cover.assign N i)).toConvexSpaceBody := by
        apply ConvexSpaceBody.ext
        exact W44FullNode.fullNodeFamily_carrier T hN U _
      _ = (U.cover.tube N (repTau (U.cover.assign N i))).toConvexSpaceBody :=
        (hrep (U.cover.assign N i) hai).2.symm
      _ = (U.cover.tube N (pTau i)).toConvexSpaceBody := by
        rw [hpTauRep i hi]
  have hleaf_j : (T j).toConvexSpaceBody =
      (U.cover.tube N (pTau j)).toConvexSpaceBody := by
    calc
      (T j).toConvexSpaceBody =
          (W44FullNode.fullNodeFamily T hN U (U.cover.assign N j)).toConvexSpaceBody :=
        W44FullNode.leaf_body_eq_assigned_fullNode T hN U hj
      _ = (U.cover.tube N (U.cover.assign N j)).toConvexSpaceBody := by
        apply ConvexSpaceBody.ext
        exact W44FullNode.fullNodeFamily_carrier T hN U _
      _ = (U.cover.tube N (repTau (U.cover.assign N j))).toConvexSpaceBody :=
        (hrep (U.cover.assign N j) haj).2.symm
      _ = (U.cover.tube N (pTau j)).toConvexSpaceBody := by
        rw [hpTauRep j hj]
  exact hleaf_i.trans ((congrArg
    (fun q => (U.cover.tube N q).toConvexSpaceBody) hp).trans hleaf_j.symm)

/- Exact endpoint fine bound for a counted/deduplicated packet.  No flatness threshold or
   Frostman callback is used: terminal ED makes the selected fibre have cardinality at most one. -/
theorem endpoint_fine_bound_counted_w50
    {p : Params} {gamma : Real} {m : Nat} {delta theta : NNReal}
    {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {tTau : Finset iota} {pTau repTau : iota -> iota}
    {tTheta tc : Finset iota} {TTheta : iota -> Tube theta E}
    {pTheta : iota -> iota} {kF lM : iota}
    {Yf Ym : iota -> ShadedTube delta E}
    {Yc : iota -> ShadedTube theta E}
    {beta gammaZero : Real} (hp : p.Spec beta gammaZero)
    (hm : m < p.N) (hN : 0 < p.N)
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {C : NNReal}
    (U : Tube.UniformTubeSet s (fun i => (T i).toTube) p.N C)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (hpTauRep : forall i, i ∈ s -> pTau i = repTau (U.cover.assign p.N i))
    (hrep : forall j, j ∈ U.cover.indexSet p.N ->
      repTau j ∈ tTau ∧
        (U.cover.tube p.N (repTau j)).toConvexSpaceBody =
          (U.cover.tube p.N j).toConvexSpaceBody)
    {sf : Finset iota} (hsf : sf ⊆ s)
    (hfineNe : (fibre sf pTau kF).Nonempty) :
    ShadedBody.multiplicity (fibre sf pTau kF)
        (fun i => (Yf i).toShadedBody) <=
      (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) *
        ((delta / Tube.gridScale delta p.N p.N : NNReal) : ENNReal) ^ (-2 * gamma) *
        (((fibre sf pTau kF).card : ENNReal) *
          ((delta / Tube.gridScale delta p.N p.N : NNReal) : ENNReal) ^ (2 : Nat)) ^
            (1 - gamma / 2) := by
  have hpInj : Set.InjOn pTau (s : Set iota) :=
    counted_terminal_parent_injOn_w50 hN U hdelta0 hED hpTauRep hrep
  have hcard : (fibre sf pTau kF).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' : i ∈ sf ∧ pTau i = kF := by
      simpa [fibre, Finset.mem_filter] using hi
    have hj' : j ∈ sf ∧ pTau j = kF := by
      simpa [fibre, Finset.mem_filter] using hj
    exact hpInj (hsf hi'.1) (hsf hj'.1) (hi'.2.trans hj'.2.symm)
  have hmult : ShadedBody.multiplicity (fibre sf pTau kF)
      (fun i => (Yf i).toShadedBody) ≤ (1 : ENNReal) :=
    (ShadedBody.multiplicity_le_card (fibre sf pTau kF)
      (fun i => (Yf i).toShadedBody)).trans (by exact_mod_cast hcard)
  have hcardEq : (fibre sf pTau kF).card = 1 :=
    Nat.le_antisymm hcard (Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr hfineNe))
  have hetaMono : p.η 0 ≤ p.η m :=
    hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _))
      (Set.mem_Iic.mpr hm.le) (Nat.zero_le _)
  have heta : 0 ≤ p.η m := hp.etaZeroPos.le.trans hetaMono
  have hetaPos : 0 < p.η m := hp.etaZeroPos.trans_le hetaMono
  have heps : 0 ≤ p.ε' := by
    rw [hp.epsPrimeEq]
    linarith [hp.etaZeroPos]
  have hpow : (1 : ENNReal) ≤
      (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) := by
    apply ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
    · exact_mod_cast hdelta0
    · exact_mod_cast hdelta1
    linarith
  have hratio : (delta / Tube.gridScale delta p.N p.N : NNReal) = 1 := by
    rw [Tube.gridScale_self delta hN]
    exact div_self (ne_of_gt hdelta0)
  rw [hratio]
  simpa [hcardEq] using hmult.trans hpow

#print axioms body_injOn_of_pairwiseED_w50
#print axioms counted_terminal_parent_injOn_w50
#print axioms endpoint_fine_bound_counted_w50

end
end Kakeya.ml1Boot.W50EndpointCounted
