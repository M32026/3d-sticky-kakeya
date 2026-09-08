module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50EndpointCore

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- At `tau = delta` with the identity fine parent map, the fine analytic
factor is a singleton and hence is bounded without a flatness threshold. -/
theorem endpoint_fine_bound_w50 [Nontrivial E]
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

#print axioms endpoint_fine_bound_w50

end
end Kakeya.ml1Boot.W50EndpointCore
