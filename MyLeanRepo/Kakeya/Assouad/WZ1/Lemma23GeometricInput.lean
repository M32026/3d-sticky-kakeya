import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23Theorem22ReadyGraph

/-!
# Unified geometric input for the actual WZ1 Lemma 23 graph

All finite graph assembly after the paper height-window restriction is now
closed.  This module isolates the three geometric inputs still owed by the
upstream one-scale argument:

* the retained volume of the complete-cell window;
* radius-`sqrt rho` localization inside one global grain on every selected
  exact slice; and
* the faithful local-cell/full-grain incidence family.

From these inputs, the closed constructors build the localized global bins,
select an actual y-residue class, construct the local bins, assemble the
actual four-cycle graph, normalize it, and produce the final Theorem 22-ready
unit-ball graph.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The radius-`sqrt rho` global-grain localization input on the genuine exact
slices selected by the global package.
-/
structure WZ1Lemma23GlobalLocalizationInput
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C) where
  center : ℤ → ℝ
  localization :
    ∀ heightIndex ∈ globalPackage.heightIndices,
      scalarProjection
          (globalGrainDirection
            (globalPackage.sourceSlope
              (globalPackage.selectedHeight heightIndex)))
          (horizontalSlice Y.union
            (globalPackage.selectedHeight heightIndex)) ⊆
        Metric.closedBall
          (center heightIndex) (Real.sqrt rho)

/--
The three paper-level geometric inputs remaining after the complete-cell
height window and exact-slice package have been fixed.
-/
structure WZ1Lemma23GeometricInput
    {delta rho sigma eta volumeLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localGrains : WZ1LocalGrainData Y sigma C) where
  window_volume :
    ENNReal.ofReal
        (Real.rpow rho
          (1 + sigma / 2 + volumeLoss)) ≤
      MeasureTheory.volume Y.union
  global_localization :
    WZ1Lemma23GlobalLocalizationInput windowed.global
  local_cell_family :
    WZ1Lemma23LocalCellFamily
      (rho := rho) (sigma := sigma) (eta := eta)
      Y C windowed.global.sourceSlope
      windowed.global.cells localGrains

/--
The geometric input carrying the generalized local-cell family.  The window
volume and global localization interfaces are unchanged.
-/
structure WZ1Lemma23GeometricInputGeneralized
    {delta rho sigma eta volumeLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localGrains : WZ1LocalGrainData Y sigma C) where
  window_volume :
    ENNReal.ofReal
        (Real.rpow rho
          (1 + sigma / 2 + volumeLoss)) ≤
      MeasureTheory.volume Y.union
  global_localization :
    WZ1Lemma23GlobalLocalizationInput windowed.global
  local_cell_family :
    WZ1Lemma23LocalCellFamilyGeneralized
      (rho := rho) (sigma := sigma) (eta := eta)
      Y C windowed.global.sourceSlope
      windowed.global.cells localGrains

/--
The two closed small-scale absorptions needed to pass from the explicit
Lemma 23 constants to the final Theorem 22 graph scale.
-/
structure WZ1Lemma23Theorem22Absorption
    (rho theoremEta volumeLoss constantLoss : ℝ) where
  edge :
    Real.rpow (wz1Lemma23Theorem22Scale rho)
        (theoremEta - 3) ≤
      (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
        Real.rpow rho
          (-3 / 2 + 4 * volumeLoss + 4 * constantLoss)
  katzTao :
    (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale rho) (-theoremEta)

/--
The edge and Katz--Tao constants are simultaneously absorbed below one
source-scale threshold.
-/
theorem wz1_lemma23_theorem22_absorption
    (theoremEta volumeLoss constantLoss : ℝ)
    (htheoremEta : 0 < theoremEta)
    (hbudget :
      8 * (volumeLoss + constantLoss) < theoremEta) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        WZ1Lemma23Theorem22Absorption
          rho theoremEta volumeLoss constantLoss := by
  rcases
      wz1_lemma23_theorem22_threshold_absorption
        theoremEta volumeLoss constantLoss hbudget with
    ⟨edgeScale, hedgeScale, hedgeScaleOne, hedge⟩
  rcases
      wz1_lemma23_katzTao_constant_absorption
        theoremEta htheoremEta with
    ⟨katzScale, hkatzScale, _, hkatz⟩
  refine
    ⟨min edgeScale katzScale,
      lt_min hedgeScale hkatzScale,
      (min_le_left edgeScale katzScale).trans hedgeScaleOne,
      ?_⟩
  intro rho hrho hrhoSmall
  exact
    { edge :=
        hedge rho hrho
          (hrhoSmall.trans
            (min_le_left edgeScale katzScale))
      katzTao :=
        hkatz rho hrho
          (hrhoSmall.trans
            (min_le_right edgeScale katzScale)) }

/--
The complete dependency-carrying output of the Lemma 23 construction.  Its
edge set is still the faithful actual four-cycle edge set, transported only
by the proved injective normalizations.
-/
structure WZ1Lemma23Theorem22ReadyOutput
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (theoremEta : ℝ) where
  localized :
    WZ1Lemma23LocalizedGlobalBinPackage windowed.global
  residue :
    WZ1Lemma23YResiduePackage windowed.global
  localBins :
    WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C windowed.global.cells
  prepared :
    WZ1Lemma23LocalizedPreparedPackage
      windowed localized residue localBins
  geometry :
    WZ1Lemma23LocalizedPreparedGeometry prepared
  ready :
    WZ1Lemma23Theorem22ReadyGraph
      rho theoremEta geometry.unitBall

/--
Build the complete Theorem 22-ready actual graph from the three unified
geometric inputs and the explicit numerical hypotheses.
-/
theorem WZ1Lemma23GeometricInput.toTheorem22ReadyOutput
    {delta rho sigma eta volumeLoss constantLoss theoremEta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localGrains : WZ1LocalGrainData Y sigma C}
    (input :
      WZ1Lemma23GeometricInput
        (eta := eta) (volumeLoss := volumeLoss)
        windowed localGrains)
    (absorption :
      WZ1Lemma23Theorem22Absorption
        rho theoremEta volumeLoss constantLoss)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hglobal :
      HasGlobalSlabAD
        Y windowed.global.sourceSlope sigma C)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤)
    (hCeta :
      C ≤ Kakeya.realRpowENN rho (-eta))
    (hCpower :
      C.toReal ≤ Real.rpow rho (-constantLoss))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 12 * Real.sqrt rho ≤ 1)
    (hlocalAbsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 10) :
    Nonempty
      (WZ1Lemma23Theorem22ReadyOutput
        windowed theoremEta) := by
  rcases
      wz1_lemma23_localized_global_bin_package
        windowed.global hdelta_rho hrho_one hball
        hglobal hCtop
        input.global_localization.center
        input.global_localization.localization with
    ⟨localized, _⟩
  rcases
      wz1_lemma23_y_residue_package
        windowed.global hrho_one with
    ⟨residue, _hresidueCells, hresidueExtra⟩
  rcases
      wz1_lemma23_local_bin_package
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains
        hdelta_rho hrho_one hsigma hsigma_one
        heta heta_sigma hCtop hCeta
        hPlanarSmall hrootSmall hlocalAbsorb
        input.local_cell_family with
    ⟨localBins, _⟩
  rcases
      wz1_lemma23_localized_prepared_package
        windowed localized residue localBins with
    ⟨prepared⟩
  rcases
      wz1_lemma23_localized_prepared_geometry
        hrho_one hball prepared with
    ⟨geometry⟩
  have hpower :=
    prepared.power_edge_bound
      hrho_one hsigma hsigma_one hball
      hC hCtop volumeLoss constantLoss
      0 input.window_volume hCpower (by simp [hresidueExtra])
  have hreal :
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (prepared.normalized.H.card : ℝ) := by
    apply absorption.edge.trans
    simpa using hpower
  have hENN :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (prepared.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast :
        (prepared.normalized.H.card : ENNReal) =
          ENNReal.ofReal
            (prepared.normalized.H.card : ℝ) := by
      norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hreal
  have hedge :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (geometry.unitBall.H.card : ENNReal) := by
    rw [geometry.unitBall.edge_card]
    exact hENN
  rcases
      geometry.toTheorem22ReadyGraph
        theoremEta hedge absorption.katzTao with
    ⟨ready⟩
  exact
    ⟨{ localized := localized
       residue := residue
       localBins := localBins
       prepared := prepared
       geometry := geometry
       ready := ready }⟩

/--
Build the unchanged Theorem 22-ready output from the generalized slope/tilt
chain.  The generalized planar fullness leaf is closed separately while the
legacy slope-`1 / 10` public theorem remains available.
-/
theorem WZ1Lemma23GeometricInputGeneralized.toTheorem22ReadyOutput
    {delta rho sigma eta volumeLoss constantLoss theoremEta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localGrains : WZ1LocalGrainData Y sigma C}
    (input :
      WZ1Lemma23GeometricInputGeneralized
        (eta := eta) (volumeLoss := volumeLoss)
        windowed localGrains)
    (absorption :
      WZ1Lemma23Theorem22Absorption
        rho theoremEta volumeLoss constantLoss)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hglobal :
      HasGlobalSlabAD
        Y windowed.global.sourceSlope sigma C)
    (hC : 1 ≤ C) (hCtop : C ≠ ⊤)
    (hCeta :
      C ≤ Kakeya.realRpowENN rho (-eta))
    (hCpower :
      C.toReal ≤ Real.rpow rho (-constantLoss))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (hlocalAbsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14) :
    Nonempty
      (WZ1Lemma23Theorem22ReadyOutput
        windowed theoremEta) := by
  rcases
      wz1_lemma23_localized_global_bin_package
        windowed.global hdelta_rho hrho_one hball
        hglobal hCtop
        input.global_localization.center
        input.global_localization.localization with
    ⟨localized, _⟩
  rcases
      wz1_lemma23_y_residue_package
        windowed.global hrho_one with
    ⟨residue, _hresidueCells, hresidueExtra⟩
  rcases
      wz1_lemma23_local_bin_package_generalized
        Y C windowed.global.sourceSlope
        windowed.global.cells localGrains
        hdelta_rho hrho_one hsigma hsigma_one
        heta heta_sigma hCtop hCeta
        hPlanarSmall hrootSmall20 hlocalAbsorb
        input.local_cell_family with
    ⟨localBins, _⟩
  rcases
      wz1_lemma23_localized_prepared_package
        windowed localized residue localBins with
    ⟨prepared⟩
  rcases
      wz1_lemma23_localized_prepared_geometry
        hrho_one hball prepared with
    ⟨geometry⟩
  have hpower :=
    prepared.power_edge_bound
      hrho_one hsigma hsigma_one hball
      hC hCtop volumeLoss constantLoss
      0 input.window_volume hCpower (by simp [hresidueExtra])
  have hreal :
      Real.rpow (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (prepared.normalized.H.card : ℝ) := by
    apply absorption.edge.trans
    simpa using hpower
  have hENN :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (prepared.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast :
        (prepared.normalized.H.card : ENNReal) =
          ENNReal.ofReal
            (prepared.normalized.H.card : ℝ) := by
      norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hreal
  have hedge :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (geometry.unitBall.H.card : ENNReal) := by
    rw [geometry.unitBall.edge_card]
    exact hENN
  rcases
      geometry.toTheorem22ReadyGraph
        theoremEta hedge absorption.katzTao with
    ⟨ready⟩
  exact
    ⟨{ localized := localized
       residue := residue
       localBins := localBins
       prepared := prepared
       geometry := geometry
       ready := ready }⟩

end

end Kakeya.Assouad
