import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# Bounded separated actual graph for windowed WZ1 Lemma 23 data

This module assembles the closed preparation chain on one paper-faithful
height window:

* the faithful local full-grain family produces the local-bin package;
* the actual global cells are restricted to one separated y-residue class;
* the actual four-cycle graph is rebuilt on that selected subset;
* the graph is normalized at scale `sqrt rho`; and
* all three normalized vertex classes are separated and lie in fixed balls.

The output retains the actual cells, cycles, edges, translated slice values,
and cardinality lower chain through the packages it contains.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The complete actual finite graph preparation after imposing the paper's
height window and the actual y-residue selection.
-/
structure WZ1Lemma23WindowedPreparedGraph
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C) where
  localBins :
    WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C windowed.global.cells
  residue :
    WZ1Lemma23YResiduePackage windowed.global
  graph :
    WZ1Lemma23YResiduePreparedPackage
      windowed.global residue localBins
  vertex_separation :
    graph.prepared.normalized.F.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      graph.prepared.normalized.G₁.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      graph.prepared.normalized.G₂.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3)
  vertex_bounds :
    (∀ point ∈ graph.prepared.normalized.F,
        dist point 0 ≤ 2) ∧
      (∀ point ∈ graph.prepared.normalized.G₁,
        dist point 0 ≤ 5) ∧
      ∀ point ∈ graph.prepared.normalized.G₂,
        dist point 0 ≤ 5

/--
Assemble the bounded separated actual graph from the faithful local-cell
family on the same windowed global-slice cells.
-/
theorem wz1_lemma23_windowed_prepared_graph
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 12 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 10)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (family :
      WZ1Lemma23LocalCellFamily
        (rho := rho) (sigma := sigma) (eta := eta)
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains) :
    Nonempty (WZ1Lemma23WindowedPreparedGraph windowed) := by
  rcases
      wz1_lemma23_local_bin_package
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains
        hdelta_rho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall habsorb family with
    ⟨localBins, _⟩
  rcases
      wz1_lemma23_y_residue_package
        windowed.global hrho_one with
    ⟨residue, _hresidueCells, _hresidueExtra⟩
  rcases
      wz1_lemma23_y_residue_prepared_package
        windowed.global residue localBins with
    ⟨graph⟩
  exact
    ⟨{ localBins := localBins
       residue := residue
       graph := graph
       vertex_separation := graph.vertex_separation
       vertex_bounds :=
         graph.vertex_bounds hrho_one hball }⟩

/--
Assemble the same prepared graph from the generalized local-cell family.
The output structure is unchanged because the slope and tilt constants are
used only to construct its local-bin package.
-/
theorem wz1_lemma23_windowed_prepared_graph_generalized
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (family :
      WZ1Lemma23LocalCellFamilyGeneralized
        (rho := rho) (sigma := sigma) (eta := eta)
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains) :
    Nonempty (WZ1Lemma23WindowedPreparedGraph windowed) := by
  rcases
      wz1_lemma23_local_bin_package_generalized
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains
        hdelta_rho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall20 habsorb family with
    ⟨localBins, _⟩
  rcases
      wz1_lemma23_y_residue_package
        windowed.global hrho_one with
    ⟨residue, _hresidueCells, _hresidueExtra⟩
  rcases
      wz1_lemma23_y_residue_prepared_package
        windowed.global residue localBins with
    ⟨graph⟩
  exact
    ⟨{ localBins := localBins
       residue := residue
       graph := graph
       vertex_separation := graph.vertex_separation
       vertex_bounds :=
         graph.vertex_bounds hrho_one hball }⟩

/-- Assemble the generalized prepared graph under the literal paper
coordinate crop instead of the historical unit-ball carrier hypothesis. -/
theorem wz1_lemma23_windowed_prepared_graph_generalized_of_coord
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (hcoord : ∀ point ∈ Y.union, ∀ i : Fin 3, |point i| ≤ 1)
    (family :
      WZ1Lemma23LocalCellFamilyGeneralized
        (rho := rho) (sigma := sigma) (eta := eta)
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains) :
    Nonempty (WZ1Lemma23WindowedPreparedGraph windowed) := by
  rcases
      wz1_lemma23_local_bin_package_generalized
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains
        hdelta_rho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall20 habsorb family with
    ⟨localBins, _⟩
  rcases wz1_lemma23_y_residue_package windowed.global hrho_one with
    ⟨residue, _hresidueCells, _hresidueExtra⟩
  rcases
      wz1_lemma23_y_residue_prepared_package
        windowed.global residue localBins with
    ⟨graph⟩
  exact
    ⟨{ localBins := localBins
       residue := residue
       graph := graph
       vertex_separation := graph.vertex_separation
       vertex_bounds :=
         graph.vertex_bounds_of_coord hrho_one hcoord }⟩

end

end Kakeya.Assouad
