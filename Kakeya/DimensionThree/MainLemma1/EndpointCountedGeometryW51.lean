module

public import Kakeya.DimensionThree.MainLemma1.CaseTwoUpstreamRawFactorW50
public import Kakeya.DimensionThree.MainLemma1.W44FullNodeTransport
public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W51EndpointRetained

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Simultaneous translation preserves essential distinctness. -/
theorem essentiallyDistinct_translate_w51 {K L : ConvexSpaceBody E} (v0 : E)
    (h : IsEssentiallyDistinct K.carrier L.carrier) :
    IsEssentiallyDistinct (ConvexSpaceBody.translate K v0).carrier
      (ConvexSpaceBody.translate L v0).carrier := by
  change IsEssentiallyDistinct ((v0 + ·) '' K.carrier) ((v0 + ·) '' L.carrier)
  unfold IsEssentiallyDistinct at *
  have hinj : Function.Injective ((v0 + ·) : E -> E) := add_right_injective v0
  rw [← Set.image_inter hinj,
    MeasureTheory.measure_image_add, MeasureTheory.measure_image_add,
    MeasureTheory.measure_image_add]
  exact h

/-- At `b = N`, the actual representative-valued middle fibre returned by the
counted producer inherits pairwise essential distinctness from the original
leaf family.  The conclusion uses exactly `pTheta`, `sm`, `lM`, and `Zm` from
the direct-factor packet. -/
theorem endpoint_counted_middle_pairwiseED_w51
    {iota : Type u} [DecidableEq iota]
    {delta : NNReal} {s sPrime : Finset iota}
    (T : iota -> ShadedTube delta E) (hsPrimeS : sPrime ⊆ s)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    {N a : Nat} (hN : 0 < N) {C : NNReal}
    (U : Tube.UniformTubeSet sPrime (fun i => (T i).toTube) N C)
    {tTau tTheta : Finset iota} {pTau pTheta : iota -> iota}
    {M : Nat} {tm sf : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {Zf : iota -> ShadedTube delta E}
    {uCell : Finset iota} {v0 : E} {tc sm : Finset iota}
    {Zc : iota -> ShadedTube (Tube.gridScale delta N a) E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {kF lM : iota}
    (htTau : tTau ⊆ U.cover.indexSet N)
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 sPrime T
      tTau (U.cover.tube N) pTau tTheta (U.cover.tube a) pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    ((fibre sm pTheta lM : Finset iota) : Set iota).Pairwise
      (fun k k' => IsEssentiallyDistinct (Zm k).carrier (Zm k').carrier) := by
  have hsPrimeNe : sPrime.Nonempty := by
    obtain ⟨i, hi⟩ := hfac.fine_nonempty
    exact ⟨i, hfac.fine_subset (Finset.mem_filter.mp hi).1⟩
  have hnodeED : ((U.cover.indexSet N : Finset iota) : Set iota).Pairwise
      (fun k k' => IsEssentiallyDistinct
        (U.cover.tube N k).carrier (U.cover.tube N k').carrier) := by
    intro k hk k' hk' hkk'
    obtain ⟨i, hi, hiAssign⟩ :=
      W50Upstream.raw_nodes_carry_leaf_upstream_w50 U le_rfl hsPrimeNe k hk
    obtain ⟨i', hi', hiAssign'⟩ :=
      W50Upstream.raw_nodes_carry_leaf_upstream_w50 U le_rfl hsPrimeNe k' hk'
    have hii' : i ≠ i' := by
      intro heq
      subst i'
      exact hkk' (hiAssign.symm.trans hiAssign')
    have hed := hED (hsPrimeS hi) (hsPrimeS hi') hii'
    change IsEssentiallyDistinct (T i).carrier (T i').carrier at hed
    have hcar : (T i).carrier = (U.cover.tube N k).carrier := by
      have hleaf := W44FullNode.leaf_carrier_eq_assigned_fullNode T hN U hi
      rw [W44FullNode.fullNodeFamily_carrier, hiAssign] at hleaf
      exact hleaf
    have hcar' : (T i').carrier = (U.cover.tube N k').carrier := by
      have hleaf := W44FullNode.leaf_carrier_eq_assigned_fullNode T hN U hi'
      rw [W44FullNode.fullNodeFamily_carrier, hiAssign'] at hleaf
      exact hleaf
    rwa [hcar, hcar'] at hed
  intro k hk k' hk' hkk'
  have hkTau : k ∈ tTau :=
    hfac.mid_subset (hfac.cell_subset
      (hfac.middle_subset (Finset.mem_filter.mp hk).1))
  have hkTau' : k' ∈ tTau :=
    hfac.mid_subset (hfac.cell_subset
      (hfac.middle_subset (Finset.mem_filter.mp hk').1))
  have hedNode := hnodeED (htTau hkTau) (htTau hkTau') hkk'
  have hed := essentiallyDistinct_translate_w51 v0 hedNode
  have hcar := congrArg
    (fun W : Tube (Tube.gridScale delta N N) E => W.carrier)
    (hfac.middle_tube k)
  have hcar' := congrArg
    (fun W : Tube (Tube.gridScale delta N N) E => W.carrier)
    (hfac.middle_tube k')
  rwa [hcar, hcar']

/-- The actual selected middle fibre is contained in the translated actual
coarse parent.  This is a direct consequence of the retained parent family and
the direct-factor fields, with no `IsCoarseNodeParents` premise. -/
theorem endpoint_counted_middle_contained_actual_parent_w51
    {iota : Type u} [DecidableEq iota]
    {delta : NNReal} {sPrime : Finset iota}
    (T : iota -> ShadedTube delta E)
    {N a : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet sPrime (fun i => (T i).toTube) N C)
    {tTau tTheta : Finset iota} {pTau pTheta : iota -> iota}
    (hparentTheta : IsParentFamily tTau (U.cover.tube N)
      tTheta (U.cover.tube a) pTheta)
    {M : Nat} {tm sf : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {Zf : iota -> ShadedTube delta E}
    {uCell : Finset iota} {v0 : E} {tc sm : Finset iota}
    {Zc : iota -> ShadedTube (Tube.gridScale delta N a) E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {kF lM : iota}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 sPrime T
      tTau (U.cover.tube N) pTau tTheta (U.cover.tube a) pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    forall k, k ∈ fibre sm pTheta lM ->
      (Zm k).carrier ⊆ ((U.cover.tube a lM).translate v0).carrier := by
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  have hkTau : k ∈ tTau :=
    hfac.mid_subset (hfac.cell_subset (hfac.middle_subset hk'.1))
  have hle : (U.cover.tube N k).toConvexSpaceBody <=
      (U.cover.tube a lM).toConvexSpaceBody := by
    simpa only [hk'.2] using hparentTheta.le_parent k hkTau
  have htranslated := translate_le_translate v0 hle
  have hmiddle := congrArg
    (fun W : Tube (Tube.gridScale delta N N) E => W.toConvexSpaceBody)
    (hfac.middle_tube k)
  change (Zm k).toConvexSpaceBody <=
    ((U.cover.tube a lM).translate v0).toConvexSpaceBody
  rw [hmiddle]
  exact htranslated

/-- Body injectivity for the exact actual middle witness at the endpoint. -/
theorem endpoint_counted_middle_body_inj_w51
    {iota : Type u} [DecidableEq iota]
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {s sPrime : Finset iota}
    (T : iota -> ShadedTube delta E) (hsPrimeS : sPrime ⊆ s)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    {N a : Nat} (hN : 0 < N) {C : NNReal}
    (U : Tube.UniformTubeSet sPrime (fun i => (T i).toTube) N C)
    {tTau tTheta : Finset iota} {pTau pTheta : iota -> iota}
    {M : Nat} {tm sf : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {Zf : iota -> ShadedTube delta E}
    {uCell : Finset iota} {v0 : E} {tc sm : Finset iota}
    {Zc : iota -> ShadedTube (Tube.gridScale delta N a) E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {kF lM : iota}
    (htTau : tTau ⊆ U.cover.indexSet N)
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 sPrime T
      tTau (U.cover.tube N) pTau tTheta (U.cover.tube a) pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    Set.InjOn (fun k => (Zm k).toConvexSpaceBody)
      ((fibre sm pTheta lM : Finset iota) : Set iota) := by
  exact injOn_toConvexSpaceBody_of_pairwise_essDistinct
    (Tube.gridScale_pos hdelta0 N N)
    (Tube.gridScale_le_one hdelta1 N N)
    (fun k => (Zm k).toTube)
    (endpoint_counted_middle_pairwiseED_w51 T hsPrimeS hED hN U htTau hfac)

#print axioms endpoint_counted_middle_pairwiseED_w51
#print axioms endpoint_counted_middle_contained_actual_parent_w51
#print axioms endpoint_counted_middle_body_inj_w51

end
end Kakeya.ml1Boot.W51EndpointRetained

end
