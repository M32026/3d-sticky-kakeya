import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredPreparationABI
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.VolumePopularResidue
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedGlobalBinPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23CommonEndpointGraph

/-!
# Anchored finite graph and sharp geometry
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

private lemma anchored_nat_le_ceil_add_one
    {n : ℕ} {X : ENNReal} (hX : X ≠ ⊤) (hn : (n : ENNReal) ≤ X) :
    n ≤ Nat.ceil X.toReal + 1 := by
  have hreal : (n : ℝ) ≤ X.toReal := by
    rw [← ENNReal.toReal_natCast n]
    exact (ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top n) hX).mpr hn
  have hceil : n ≤ Nat.ceil X.toReal := by
    exact_mod_cast hreal.trans (Nat.le_ceil X.toReal)
  omega

/-- Construction-independent local-bin adapter.  All anchor geometry is
carried by `localInput`; no ambient plane map is reconstructed. -/
theorem pureWZ2_anchoredLocalBinPackage
    {rho sigma : ℝ} {fineC targetC : ENNReal}
    {cells : Finset (ℤ × ℤ × ℤ)} {g : ℝ → ℝ}
    (localInput : WZ1Lemma23HeterogeneousLocalBinInput
      rho sigma fineC cells g)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hgLip : LipschitzOnWith 64 g Set.univ)
    (hgBound : ∀ y, |g y| ≤ 2)
    (hconstant : 35 * fineC ≤ 19 * targetC)
    (htargetTop : targetC ≠ ⊤) :
    Nonempty (WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) targetC cells) := by
  let X : ENNReal := 19 * targetC *
    Kakeya.realRpowENN (Real.sqrt rho / rho) (1 - sigma)
  have hXtop : X ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) htargetTop)
    (by simp [Kakeya.realRpowENN])
  let localBinBound := Nat.ceil X.toReal + 1
  refine ⟨{
    g := g
    g_lipschitz := hgLip
    g_bounded := hgBound
    localBinBound := localBinBound
    localBinBound_eq := rfl
    local_bins := ?_
  }⟩
  intro y hy
  have hraw := wz1_lemma23_actual_local_bins_at_heterogeneous
    fineC cells g localInput hrho hrhoOne y hy
  apply anchored_nat_le_ceil_add_one hXtop
  calc
    _ ≤ 35 * fineC *
        Kakeya.realRpowENN (Real.sqrt rho / rho) (1 - sigma) := hraw
    _ ≤ 19 * targetC *
        Kakeya.realRpowENN (Real.sqrt rho / rho) (1 - sigma) := by gcongr
    _ = X := rfl

structure PureWZ2AnchoredFiniteGraphData
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    (prep : PureWZ2AnchoredGraphPreparationData input)
    (localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells) where
  heightPopular : PureWZ2HeightVolumePopularData shadow rho
  popularSource : PureWZ2VolumePopularResidueData
    prep.windowed.global heightPopular
  rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global
  raw_residue_eq : rawResidue = popularSource.residue
  popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue
  graph : WZ1Lemma23WindowedPreparedGraph prep.windowed
  graph_residue_eq : graph.residue = popularResidue.residue
  heightFiberCost_eq : graph.residue.heightFiberCost = 2

theorem PureWZ2AnchoredGraphPreparationData.prepareFiniteGraph
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    (prep : PureWZ2AnchoredGraphPreparationData input)
    (localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells)
    (hvolumePos : 0 < volume shadow.union) :
    Nonempty (PureWZ2AnchoredFiniteGraphData prep localBins) := by
  have hvolumeTop : volume shadow.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono input.shadow_ball)
  rcases pureWZ2_heightVolumePopularity shadow rho input.rho_pos
      input.shadow_ball hvolumePos hvolumeTop with ⟨heightPopular⟩
  rcases heightPopular.toVolumePopularResidue prep.windowed.global
      input.rho_le_one input.shadow_ball with ⟨popularSource⟩
  let rawResidue := popularSource.residue
  rcases rawResidue.regularizeHeights popularSource.cells_nonempty with
    ⟨popularResidue⟩
  rcases wz1_lemma23_y_residue_prepared_package prep.windowed.global
      popularResidue.residue localBins with ⟨graphPackage⟩
  let graph : WZ1Lemma23WindowedPreparedGraph prep.windowed := {
    localBins := localBins
    residue := popularResidue.residue
    graph := graphPackage
    vertex_separation := graphPackage.vertex_separation
    vertex_bounds := graphPackage.vertex_bounds_of_coord
      input.rho_le_one prep.shadow_coordinate
  }
  exact ⟨{
    heightPopular := heightPopular
    popularSource := popularSource
    rawResidue := rawResidue
    raw_residue_eq := rfl
    popularResidue := popularResidue
    graph := graph
    graph_residue_eq := rfl
    heightFiberCost_eq := popularResidue.heightFiberCost_eq
  }⟩

structure PureWZ2AnchoredSharpGeometry
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    (finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins) where
  localized : WZ1Lemma23LocalizedGlobalBinPackage prep.windowed.global
  sharp : WZ1Lemma23LocalizedPreparedPackage prep.windowed localized
    finiteGraph.graph.residue finiteGraph.graph.localBins
  geometry : WZ1Lemma23LocalizedPreparedGeometry sharp

theorem PureWZ2AnchoredFiniteGraphData.toSharpGeometry
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    (finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins) :
    Nonempty (PureWZ2AnchoredSharpGeometry finiteGraph) := by
  rcases wz1_lemma23_localized_global_bin_package_of_coord_of_exact
      prep.windowed.global input.rho_le_one prep.shadow_coordinate
      prep.exactAD
      input.constant_ne_top prep.localization.center
      prep.localization.localization with ⟨localized, _⟩
  rcases wz1_lemma23_localized_prepared_package prep.windowed localized
      finiteGraph.graph.residue finiteGraph.graph.localBins with ⟨sharp⟩
  rcases wz1_lemma23_localized_prepared_geometry_of_coord
      input.rho_le_one prep.shadow_coordinate sharp with ⟨geometry⟩
  exact ⟨{ localized := localized, sharp := sharp, geometry := geometry }⟩

structure PureWZ2AnchoredTheorem22ReadyGraph
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    (sharp : PureWZ2AnchoredSharpGeometry finiteGraph) where
  common : WZ1Lemma23UnitBallGraph rho sharp.sharp.normalized.F
    (wz1Lemma23CommonLocalVertices rho sharp.sharp.selectedLocal.g
      finiteGraph.graph.residue.cells)
    (wz1Lemma23CommonLocalVertices rho sharp.sharp.selectedLocal.g
      finiteGraph.graph.residue.cells)
    sharp.sharp.normalized.H
  ready : WZ1Lemma23Theorem22ReadyGraph rho theoremEta common
  heightFiberCost_eq : finiteGraph.graph.residue.heightFiberCost = 2

theorem PureWZ2AnchoredSharpGeometry.toReadyGraph
    {delta rho sigma theoremEta volumeLoss constantLoss extraLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    (sharp : PureWZ2AnchoredSharpGeometry finiteGraph)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCOne : (1 : ENNReal) ≤ C)
    (hCpower : C.toReal ≤ Real.rpow rho (-constantLoss))
    (hvolume : ENNReal.ofReal
        (Real.rpow rho (1 + sigma / 2 + volumeLoss)) ≤ volume shadow.union)
    (hextraPower : (finiteGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow rho (-extraLoss))
    (hedgeAbsorb :
      Real.rpow (wz1Lemma23Theorem22Scale rho) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow rho
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho) (-theoremEta)) :
    Nonempty (PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp) := by
  have hcoord := prep.shadow_coordinate
  have hedgeReal :
      Real.rpow (wz1Lemma23Theorem22Scale rho) (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ℝ) := by
    apply hedgeAbsorb.trans
    exact sharp.sharp.power_edge_bound_of_coord input.rho_le_one
      hsigma hsigmaOne hcoord hCOne input.constant_ne_top
      volumeLoss constantLoss extraLoss hvolume hCpower hextraPower
  have hedgeNormalized :
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (sharp.sharp.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast : (sharp.sharp.normalized.H.card : ENNReal) =
        ENNReal.ofReal (sharp.sharp.normalized.H.card : ℝ) := by norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeUnit :
      Kakeya.realRpowENN (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (sharp.geometry.unitBall.H.card : ENNReal) := by
    rw [sharp.geometry.unitBall.edge_card]
    exact hedgeNormalized
  rcases sharp.geometry.toCommonEndpointReadyGraph input.rho_le_one hcoord
      hedgeUnit hKatzTao with ⟨common, ready⟩
  exact ⟨{
    common := common
    ready := Classical.choice ready
    heightFiberCost_eq := finiteGraph.heightFiberCost_eq
  }⟩

/-- Full-grain-free Alternative-A projection entrance.  This is deliberately
indexed by the anchored ready graph itself, so no graph/witness cast is
possible at the boundary. -/
def PureWZ2AnchoredAlternativeAProjectionInput
    {delta rho sigma theoremEta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := rho) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {sharp : PureWZ2AnchoredSharpGeometry finiteGraph}
    (ready : PureWZ2AnchoredTheorem22ReadyGraph
      (theoremEta := theoremEta) sharp)
    (epsilon : ℝ) : Prop :=
  WZ1Proposition8_9AlternativeAUnion ready.ready.deltaGraph epsilon
    ready.common.F ready.common.G₁ ready.common.G₁

end Kakeya.Assouad

end
