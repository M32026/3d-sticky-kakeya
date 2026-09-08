module

public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.DimensionThree.MainLemma1.WZCanonicalClasses
public import Kakeya.Factoring.HonestFibreBridge

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W48EndpointModuleSafe

noncomputable section
set_option maxHeartbeats 12000000

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-!
  The packet boundary used by the endpoint WZ consumers.  It deliberately has
  no dependency on the legacy `WeakCoarseFibre` file: a downstream producer
  can fill these fields from its hierarchy witness, while an upstream module
  can import this declaration without importing `CaseTwo`.

  `source` is the one fibre on which the WZ estimate is run.  `ambient` is the
  complete parent-family carrier.  `parent_constant` records that the chosen
  parent map is constant on the ambient carrier, which is the exact condition
  needed to turn hierarchy containment into the single-parent tube input of
  the no-ED middle consumer.
-/
structure EndpointHierarchySelectedPacket
    {iota : Type u} [DecidableEq iota]
    {kappa : Type w} [DecidableEq kappa]
    {delta tau rho : NNReal}
    (source ambient : Finset iota)
    (Ttau : iota -> ShadedTube tau E)
    (parentSet : Finset kappa)
    (Trho : kappa -> Tube rho E)
    (pMap : iota -> kappa) (parent : kappa)
    (zFr zQ etaIn : Real) (CFr CQ : NNReal) where
  source_nonempty : source.Nonempty
  source_subset : source ⊆ ambient
  parent_mem : parent ∈ parentSet
  parent_family :
    IsParentFamily source (fun i => (Ttau i).toTube)
      parentSet Trho pMap
  parent_constant : ∀ i ∈ ambient, pMap i = parent
  ambient_containment : ∀ i ∈ ambient,
    (Ttau i).carrier ⊆ (Trho parent).carrier
  source_eq_fibre : source = fibre ambient pMap parent
  fullness_pos :
    0 < fullness source (fun i => (Ttau i).toShadedBody)
  fullness_lower :
    (delta : ENNReal) ^ etaIn <=
      (fullness source (fun i => (Ttau i).toShadedBody) : ENNReal)
  source_frostman :
    frostmanConstIn source
        (fun i => (Ttau i).toConvexSpaceBody)
        (Trho parent).toConvexSpaceBody <=
      (CFr : ENNReal) * (delta : ENNReal) ^ (-zFr)
  q_lower :
    (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
      (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
        (source.card : ENNReal)
  q_upper :
    (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
        (source.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)

/- The parent family and the explicit ambient containment are both retained:
   the former is used by coarse assembly, the latter by the WZ middle call. -/
theorem EndpointHierarchySelectedPacket.parent_containment
    {iota : Type u} [DecidableEq iota]
    {kappa : Type w} [DecidableEq kappa]
    {delta tau rho : NNReal}
    {source ambient : Finset iota}
    {Ttau : iota -> ShadedTube tau E}
    {parentSet : Finset kappa} {Trho : kappa -> Tube rho E}
    {pMap : iota -> kappa} {parent : kappa}
    {zFr zQ etaIn : Real} {CFr CQ : NNReal}
    (P : EndpointHierarchySelectedPacket (delta := delta) source ambient Ttau parentSet Trho
      pMap parent zFr zQ etaIn CFr CQ) :
    ∀ i ∈ source,
      (Ttau i).toConvexSpaceBody <= (Trho (pMap i)).toConvexSpaceBody := by
  intro i hi
  apply (SetLike.coe_subset_coe (A := ConvexSpaceBody E)
    (S := (Ttau i).toConvexSpaceBody)
    (T := (Trho (pMap i)).toConvexSpaceBody)).mpr
  have hparent := P.parent_constant i (P.source_subset hi)
  rw [hparent]
  change (Ttau i).carrier ⊆ (Trho parent).carrier
  exact P.ambient_containment i (P.source_subset hi)

/- This is the exact tuple consumed by the split-universe WZ interface.  It
   exposes every source/Frostman/Q field, rather than hiding one in an
   existential callback. -/
theorem EndpointHierarchySelectedPacket.toWZInput
    {iota : Type u} [DecidableEq iota]
    {kappa : Type w} [DecidableEq kappa]
    {delta tau rho : NNReal}
    {source ambient : Finset iota}
    {Ttau : iota -> ShadedTube tau E}
    {parentSet : Finset kappa} {Trho : kappa -> Tube rho E}
    {pMap : iota -> kappa} {parent : kappa}
    {zFr zQ etaIn : Real} {CFr CQ : NNReal}
    (P : EndpointHierarchySelectedPacket (delta := delta) source ambient Ttau parentSet Trho
      pMap parent zFr zQ etaIn CFr CQ) :
    source.Nonempty ∧ source ⊆ ambient ∧
      (∀ i ∈ ambient, (Ttau i).carrier ⊆ (Trho parent).carrier) ∧
      0 < fullness source (fun i => (Ttau i).toShadedBody) ∧
      (delta : ENNReal) ^ etaIn <=
        (fullness source (fun i => (Ttau i).toShadedBody) : ENNReal) ∧
      frostmanConstIn source
          (fun i => (Ttau i).toConvexSpaceBody)
          (Trho parent).toConvexSpaceBody <=
        (CFr : ENNReal) * (delta : ENNReal) ^ (-zFr) ∧
      (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
        (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
          (source.card : ENNReal) ∧
      (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
          (source.card : ENNReal) <=
        (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) := by
  exact ⟨P.source_nonempty, P.source_subset, P.ambient_containment,
    P.fullness_pos, P.fullness_lower, P.source_frostman,
    P.q_lower, P.q_upper⟩

/- A constructor-facing producer interface.  The producer is an eventual
   packet witness, not a hidden analytic premise; all quantitative fields are
   visible in the returned packet. -/
def EndpointHierarchySelectedProducer
    {iota : Type u} [DecidableEq iota]
    {kappa : Type w} [DecidableEq kappa]
    {tau rho : NNReal}
    (source ambient : Finset iota)
    (Ttau : iota -> ShadedTube tau E)
    (parentSet : Finset kappa) (Trho : kappa -> Tube rho E)
    (pMap : iota -> kappa) (parent : kappa)
    (zFr zQ etaIn : Real) (CFr CQ : NNReal) : Prop :=
  ∀ delta : NNReal,
    0 < delta ->
      EndpointHierarchySelectedPacket (delta := delta) source ambient Ttau parentSet Trho
        pMap parent zFr zQ etaIn CFr CQ

end
end Kakeya.ml1Boot.W48EndpointModuleSafe

end

#print axioms Kakeya.ml1Boot.W48EndpointModuleSafe.EndpointHierarchySelectedPacket.toWZInput
