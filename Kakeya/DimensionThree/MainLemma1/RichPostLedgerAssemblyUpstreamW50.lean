module

public import Kakeya.DimensionThree.MainLemma1.B3PostCertificateCoreW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50RichPostLedgerAssemblyUpstream

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-!
The rich-branch post assembly is upstream of `B3EndToEnd`.  Its proof is the
same scalar/cardinality assembly as the auxiliary bridge, but its result uses
the canonical `B3PostCertificate` declaration supplied by the cycle-free core
module.
-/
theorem b3PostCertificate_of_richFactor_rawCardLoss_upstream_w50
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    {gamma : Real} {m : Nat}
    {delta tau theta : NNReal} (hdelta1 : delta <= 1)
    {iota : Type u} [DecidableEq iota]
    {s sPrime level core : Finset iota}
    {V : iota -> ShadedTube delta E}
    {tTau : Finset iota} {VTau : iota -> Tube tau E}
    {pTau : iota -> iota}
    {tTheta : Finset iota} {VTheta : iota -> Tube theta E}
    {pTheta : iota -> iota}
    {kF lM : iota}
    {Yf : iota -> ShadedTube delta E}
    {Ym : iota -> ShadedTube tau E}
    {tThetaAct : Finset iota} {Yc : iota -> ShadedTube theta E}
    {lamF lamM lamC : NNReal} {Lfact Lcard : ENNReal}
    (hfactor : IsTwoScaleFactors Lfact Lcard s V
      tTau VTau pTau tTheta VTheta pTheta
      kF Yf lamF lM Ym lamM tThetaAct Yc lamC)
    (hmiddleCore : fibre tTau pTheta lM = core)
    (hcoreLevel : core <= level)
    {assign : iota -> iota}
    (hcarry : ∀ k ∈ level, ∃ i ∈ sPrime, assign i = k)
    (hcardPrime : (sPrime.card : Real) <=
      (delta : Real) ^ (-(7 : Real)))
    (hbase : Lfact <=
      (factorTwoScales.C s.card delta core.card tau : ENNReal))
    (hanalytic : AnalyticEndgameW27.IsTwoScaleAnalyticBounds
      gamma (p.η m) (p.η m + 2 * p.ε')
      s pTau kF Yf tTau pTheta lM Ym tThetaAct Yc) :
    B3PostCertificate (E := E) (p := p) (γ := gamma) (m := m)
      1 s tTau pTau kF Yf tTheta pTheta lM Ym tThetaAct Yc Lfact := by
  have hcoreNe : core.Nonempty := by
    rw [<- hmiddleCore]
    exact hfactor.mid_nonempty
  have hlevelCard : level.card <= sPrime.card := by
    apply Finset.card_le_card_of_surjOn assign
    intro k hk
    obtain ⟨i, hi, hik⟩ := hcarry k hk
    exact ⟨i, hi, hik⟩
  have hcoreCardNat : core.card <= sPrime.card :=
    (Finset.card_le_card hcoreLevel).trans hlevelCard
  have hcoreCard : (core.card : Real) <=
      (delta : Real) ^ (-(7 : Real)) := by
    have hcast : (core.card : Real) <= (sPrime.card : Real) := by
      exact_mod_cast hcoreCardNat
    exact hcast.trans hcardPrime
  have hledger : Lfact <=
      ((((1 : NNReal) * factorTwoScales.C s.card delta core.card tau : NNReal) :
          ENNReal)) * (delta : ENNReal) ^ (-p.ε') :=
    hbase.trans (factorTwoScales_C_le_exact_upstream_w50 hp hdelta1 1 le_rfl
      s.card core.card)
  exact ⟨core.card, Finset.card_pos.mpr hcoreNe, hcoreCard,
    hledger, hanalytic⟩

#print axioms b3PostCertificate_of_richFactor_rawCardLoss_upstream_w50

end
end Kakeya.ml1Boot.W50RichPostLedgerAssemblyUpstream
end
