module

public import Kakeya.DimensionThree.MainLemma1.EndpointPacketCoarseModuleW48

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W48EndpointPacketHierarchyModuleBridgeSafe

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-!
This is the setup-safe packet boundary for the endpoint coarse consumer.  It
contains exactly the fields which are needed after the hierarchy packet has
been assembled: the selected singleton certificate and the radius-four (or
radius-`R`) parent containment.  In particular, it deliberately does not
mention the historical `EndpointHierarchySelectedPacket`, whose source file
is not a Lean `module` and therefore cannot be imported by `CaseTwo`.
-/
structure EndpointSelectedCoarseSetupW48
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace Real E]
      [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (iota : Type u) [DecidableEq iota]
    (delta sigma rho : NNReal) (R : Real) where
  c : ENNReal
  L : ENNReal
  amb : Finset iota
  act : Finset iota
  act' : Finset iota
  V : iota → ShadedTube sigma E
  Z' : iota → ShadedTube sigma E
  pMap : iota → iota
  p : iota
  k0 : iota
  Vrho : iota → Tube rho E
  tAct : Finset iota
  Zrho : iota → ShadedTube rho E
  lamP : NNReal
  lamF : NNReal
  selected : IsOneScaleSelected c L amb act V ({p} : Finset iota) Vrho pMap
    act' Z' tAct Zrho k0 lamP lamF
  parentBall : (Vrho p).carrier ⊆ Metric.closedBall (0 : E) R

/-!
Apply the module-safe singleton consumer to a packet whose construction is
performed by the caller.  This theorem is the replacement for the old bridge:
all hierarchy-specific fields stay on the producer side, while `CaseTwo` only
imports this declaration and supplies the two retained fields above.
-/
set_option maxHeartbeats 16000000 in
theorem eventually_endpoint_selected_coarse_setup_w48
    (hdim : Module.finrank Real E = 3) {gamma : Real}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hKF : FrostmanEstimate.{u} E gamma)
    (e : Real) (he : 0 < e) (R : Real) (hR : 1 ≤ R) :
    ∃ etaS > (0 : Real), ∃ M : Nat, 0 < M ∧
      ∀ Lf : NNReal, 1 ≤ Lf → ∀ n0 A : Real, 0 ≤ n0 → 0 < A →
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ rho : NNReal, delta ≤ rho → rho ≤ 1 →
          ∀ {iota : Type u} [DecidableEq iota] {sigma : NNReal},
          ∀ (D : EndpointSelectedCoarseSetupW48 E iota delta sigma rho R),
            volume (ConvexSpaceBody.closedBall (0 : E) R
              (le_trans zero_le_one hR)).carrier /
                volume (D.Vrho D.p).carrier ≤
              (Lf : ENNReal) * (delta : ENNReal) ^ (-n0) →
            (2 : ENNReal) * (delta : ENNReal) ^ etaS ≤
              (D.lamP : ENNReal) →
            (2 * (M : ENNReal) * (Lf : ENNReal)) *
                (delta : ENNReal) ^ (-n0 - e) ≤
              (delta : ENNReal) ^ (-4 * A) →
            (rho : Real) ≤ 1 / 4 →
            ShadedBody.multiplicity D.tAct
                (fun l => (D.Zrho l).toShadedBody) ≤
              (delta : ENNReal) ^ (-4 * A) * (rho : ENNReal) ^ (-2 * gamma) *
                ((D.tAct.card : ENNReal) * (rho : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2) := by
  obtain ⟨etaS, hetaS, M, hM, hcore⟩ :=
    Kakeya.ml1Boot.W48EndpointPacketCoarseModule.eventually_selected_singleton_coarse_module_w48
      (E := E) hdim hgamma0 hgamma1 hKF e he R hR
  refine ⟨etaS, hetaS, M, hM, ?_⟩
  intro Lf hLf n0 A hn0 hA
  filter_upwards [hcore Lf hLf n0 A hn0 hA,
      self_mem_nhdsWithin, eventually_le_one_nhdsGT]
    with delta hdeltaCore hdelta0 hdelta1
  intro rho hdeltaRho hrho1 iota _ sigma D hratio hrich habsorb hrho4
  exact hdeltaCore rho hdeltaRho hrho1 D.selected D.parentBall
    hratio hrich habsorb hrho4

end
end Kakeya.ml1Boot.W48EndpointPacketHierarchyModuleBridgeSafe

#print axioms Kakeya.ml1Boot.W48EndpointPacketHierarchyModuleBridgeSafe.eventually_endpoint_selected_coarse_setup_w48

end
