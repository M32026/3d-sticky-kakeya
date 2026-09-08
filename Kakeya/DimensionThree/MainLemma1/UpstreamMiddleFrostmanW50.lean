module

public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddlePaymentsW50
public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddlePaymentHelpersW50
public import Kakeya.DimensionThree.MainLemma1.ExactCountedMiddleW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50UpstreamMiddleFrostman

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

local instance : DecidableEq (ConvexSpaceBody E) := Classical.decEq _

/-- The first refinement retains a global share of the raw level even when
the product uses counted body representatives. -/
theorem activeParents_card_share_of_countedDedup_upstream_w50 [Nontrivial E]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} (T : iota -> ShadedTube delta E)
    {N b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s (fun i => (T i).toTube) N C) (hb : b <= N)
    {tTau : Finset iota} {pTau repTau : iota -> iota}
    (htTau : tTau ⊆ U.cover.indexSet b)
    (hpTauRep : ∀ i ∈ s, pTau i = repTau (U.cover.assign b i))
    (hrepTau : ∀ j ∈ U.cover.indexSet b,
      repTau j ∈ tTau /\
        (U.cover.tube b (repTau j)).toConvexSpaceBody =
          (U.cover.tube b j).toConvexSpaceBody)
    {theta : NNReal} {tTheta : Finset iota}
    {TTheta : iota -> Tube theta E} {pTheta : iota -> iota}
    {M : Nat} {tm sf : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N b) E}
    {Zf : iota -> ShadedTube delta E} {uCell : Finset iota} {v0 : E}
    {tc sm : Finset iota} {Zc : iota -> ShadedTube theta E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N b) E} {kF lM : iota}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 s T
      tTau (U.cover.tube b) pTau tTheta TTheta pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM)
    {r : ENNReal} (hret : r * (s.card : ENNReal) <= (sf.card : ENNReal)) :
    r * ((U.cover.indexSet b).card : ENNReal) <=
      (C : ENNReal) ^ 3 * (tm.card : ENNReal) := by
  classical
  let rawActive : Finset iota :=
    (U.cover.indexSet b).filter fun j => repTau j ∈ tm
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hfac.fine_nonempty
    exact ⟨i, hfac.fine_subset (Finset.mem_filter.mp hi).1⟩
  have hrawSub : rawActive ⊆ U.cover.indexSet b := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hmaps : ∀ i ∈ sf, U.cover.assign b i ∈ rawActive := by
    intro i hi
    have his : i ∈ s := hfac.fine_subset hi
    refine Finset.mem_filter.mpr ⟨U.cover.assign_mem b hb i his, ?_⟩
    rw [← hpTauRep i his]
    exact hfac.fine_maps i hi
  have hactive : ∃ j ∈ rawActive,
      (fibre sf (U.cover.assign b) j).Nonempty := by
    obtain ⟨i, hi⟩ := hfac.fine_nonempty
    have hisf : i ∈ sf := (Finset.mem_filter.mp hi).1
    refine ⟨U.cover.assign b i, hmaps i hisf, i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hisf, rfl⟩
  have houter : r * ((U.cover.indexSet b).card : ENNReal) <=
      (C : ENNReal) ^ 2 * (rawActive.card : ENNReal) := by
    exact W50UpstreamMiddlePayments.activeParents_card_share_of_uniform_upstream_w50
      (fun i => (T i).toTube) U hb hrawSub hfac.fine_subset hmaps hactive hret
  have hrawCard : (rawActive.card : ENNReal) <=
      (C : ENNReal) * (tm.card : ENNReal) := by
    simpa [rawActive] using
      W50UpstreamMiddlePayments.card_rawNodes_over_active_reps_le_upstream_w50
        U hb hs htTau hfac.mid_subset hrepTau
  calc
    r * ((U.cover.indexSet b).card : ENNReal) <=
        (C : ENNReal) ^ 2 * (rawActive.card : ENNReal) := houter
    _ <= (C : ENNReal) ^ 2 * ((C : ENNReal) * (tm.card : ENNReal)) := by
      gcongr
    _ = (C : ENNReal) ^ 3 * (tm.card : ENNReal) := by ring

/-- The ball cell and the second refinement retain a global share of the
active middle nodes. -/
theorem middle_global_card_share_upstream_w50 [Nontrivial E]
    {delta tau theta : NNReal} (htau0 : 0 < tau) (htau1 : tau <= 1)
    {iota kappa : Type u} [DecidableEq kappa]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {tTau : Finset kappa} {TTau : kappa -> Tube tau E} {pTau : iota -> kappa}
    {tTheta : Finset kappa} {TTheta : kappa -> Tube theta E}
    {pTheta : kappa -> kappa}
    {M : Nat} (hM : 0 < M) {tm : Finset kappa} {sf : Finset iota}
    {ZTau : kappa -> ShadedTube tau E} {Zf : iota -> ShadedTube delta E}
    {uCell : Finset kappa} {v0 : E} {tc sm : Finset kappa}
    {Zc : kappa -> ShadedTube theta E} {Zm : kappa -> ShadedTube tau E}
    {kF lM : kappa}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50
      s T tTau TTau pTau tTheta TTheta pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    (((((factorOneScale.C uCell.card tau)⁻¹ : NNReal) : ENNReal) *
        (4 * (M : ENNReal))⁻¹) *
        ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)) *
      (tm.card : ENNReal) <= (sm.card : ENNReal) := by
  let D : ENNReal := 4 * (M : ENNReal)
  let c2 : ENNReal := (((factorOneScale.C uCell.card tau)⁻¹ : NNReal) : ENNReal)
  have hD0 : D ≠ 0 := by
    dsimp [D]
    exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hM.ne')
  have hDtop : D ≠ ⊤ := by
    dsimp [D]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top M)
  have hcell : D⁻¹ * (∑ k ∈ tm, volume (ZTau k).shade) <=
      ∑ k ∈ uCell, volume ((ZTau k).translate v0).shade := by
    calc
      D⁻¹ * (∑ k ∈ tm, volume (ZTau k).shade) <=
          D⁻¹ * (D * ∑ k ∈ uCell,
            volume ((ZTau k).translate v0).shade) := by
        gcongr
        simpa [D] using hfac.cell_mass
      _ = ∑ k ∈ uCell, volume ((ZTau k).translate v0).shade := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]
  have hmass : (c2 * D⁻¹) * (∑ k ∈ tm, volume (ZTau k).shade) <=
      ∑ k ∈ sm, volume (Zm k).shade := by
    calc
      (c2 * D⁻¹) * (∑ k ∈ tm, volume (ZTau k).shade) =
          c2 * (D⁻¹ * ∑ k ∈ tm, volume (ZTau k).shade) := by ring
      _ <= c2 * ∑ k ∈ uCell,
          volume ((ZTau k).translate v0).shade := by gcongr
      _ <= ∑ k ∈ sm, volume (Zm k).shade := by
        simpa [c2] using hfac.middle_refinement.2
  have hshare :=
    W50UpstreamMiddlePayments.card_share_of_mass_retention_upstream_w50
      htau0 htau1 ZTau Zm
      (show tm.Nonempty from ⟨kF, hfac.fine_mem⟩) hmass
  simpa [D, c2, mul_assoc] using hshare

/-- The complete raw level has a globally retained share in the active middle
family after both product refinements and counted fine-parent deduplication. -/
theorem middle_fixed_global_card_share_upstream_w50 [Nontrivial E]
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} [DecidableEq iota]
    {s : Finset iota} (T : iota -> ShadedTube delta E)
    {N b : Nat} {C : NNReal} (hC : 1 <= C)
    (U : Tube.UniformTubeSet s (fun i => (T i).toTube) N C) (hb : b <= N)
    {tTau : Finset iota} {pTau repTau : iota -> iota}
    (htTau : tTau ⊆ U.cover.indexSet b)
    (hpTauRep : ∀ i ∈ s, pTau i = repTau (U.cover.assign b i))
    (hrepTau : ∀ j ∈ U.cover.indexSet b,
      repTau j ∈ tTau /\
        (U.cover.tube b (repTau j)).toConvexSpaceBody =
          (U.cover.tube b j).toConvexSpaceBody)
    {theta : NNReal} {tTheta : Finset iota}
    {TTheta : iota -> Tube theta E} {pTheta : iota -> iota}
    {M : Nat} (hM : 0 < M) {tm sf : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N b) E}
    {Zf : iota -> ShadedTube delta E} {uCell : Finset iota} {v0 : E}
    {tc sm : Finset iota} {Zc : iota -> ShadedTube theta E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N b) E} {kF lM : iota}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 s T
      tTau (U.cover.tube b) pTau tTheta TTheta pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    ((((((factorOneScale.C uCell.card (Tube.gridScale delta N b))⁻¹ : NNReal) :
          ENNReal) * (4 * (M : ENNReal))⁻¹) *
          ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)) *
        ((C : ENNReal) ^ 3)⁻¹ *
        ((((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
          ShadedBody.fullness s (fun i => (T i).toShadedBody))) *
        ((U.cover.indexSet b).card : ENNReal) <= (sm.card : ENNReal) := by
  let r1 : ENNReal :=
    (((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
      ShadedBody.fullness s (fun i => (T i).toShadedBody)
  let r2 : ENNReal :=
    (((factorOneScale.C uCell.card (Tube.gridScale delta N b))⁻¹ : NNReal) :
        ENNReal) * (4 * (M : ENNReal))⁻¹ *
      ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)
  let C3 : ENNReal := (C : ENNReal) ^ 3
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hfac.fine_nonempty
    exact ⟨i, hfac.fine_subset (Finset.mem_filter.mp hi).1⟩
  have hret1 : r1 * (s.card : ENNReal) <= (sf.card : ENNReal) := by
    simpa [r1] using
      W50UpstreamMiddlePayments.card_share_of_tube_refinement_upstream_w50
        hdelta0 hdelta1 T Zf hs hfac.fine_tube hfac.fine_refinement
  have houter : r1 * ((U.cover.indexSet b).card : ENNReal) <=
      C3 * (tm.card : ENNReal) := by
    simpa [C3] using activeParents_card_share_of_countedDedup_upstream_w50
      T U hb htTau hpTauRep hrepTau hfac hret1
  have hmiddle : r2 * (tm.card : ENNReal) <= (sm.card : ENNReal) := by
    simpa [r2, mul_assoc] using middle_global_card_share_upstream_w50
      (Tube.gridScale_pos hdelta0 N b)
      (Tube.gridScale_le_one hdelta1 N b) hM hfac
  have hC0 : C3 ≠ 0 := by
    dsimp [C3]
    exact pow_ne_zero 3
      (ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hC).ne')
  have hCtop : C3 ≠ ⊤ := by
    dsimp [C3]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  calc
    ((r2 * C3⁻¹) * r1) * ((U.cover.indexSet b).card : ENNReal) =
        (r2 * C3⁻¹) *
          (r1 * ((U.cover.indexSet b).card : ENNReal)) := by ring
    _ <= (r2 * C3⁻¹) * (C3 * (tm.card : ENNReal)) := by gcongr
    _ = r2 * (tm.card : ENNReal) := by
      rw [mul_assoc r2, ← mul_assoc C3⁻¹ C3,
        ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
    _ <= (sm.card : ENNReal) := hmiddle

#print axioms activeParents_card_share_of_countedDedup_upstream_w50
#print axioms middle_global_card_share_upstream_w50
#print axioms middle_fixed_global_card_share_upstream_w50

end
end Kakeya.ml1Boot.W50UpstreamMiddleFrostman
