import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeterogeneousLocalBins

/-!
# Genuine-source local input for CommonBin

This is the anchored CommonBin entrance adapter.  Coarse graph cells keep
their geometric representatives, while every analytic witness and normal is
evaluated on the literal supplied current shading.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceCommonBinAnchoredLocalReceipt
    {delta sigma inputLoss rho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    (current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent)
    (C : ENNReal) (cells : Finset (ℤ × ℤ × ℤ)) (g : ℝ → ℝ) where
  coarseRepresentative : (ℤ × ℤ × ℤ) → Point3
  fineWitness : (ℤ × ℤ × ℤ) →
    {point : Point3 // point ∈ current.grain.shading.union}
  anchor : ℤ → {point : Point3 // point ∈ current.grain.shading.union}
  coarse_representative_index :
    ∀ idx ∈ cells,
      wz1Lemma23CellIndex rho (coarseRepresentative idx) = idx
  coarse_fine_close :
    ∀ idx ∈ cells,
      dist (coarseRepresentative idx) (fineWitness idx : Point3) ≤ 2 * rho
  fine_witness_in_anchor_ball :
    ∀ y (_hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ idx (_hidx : idx ∈ cells), idx.2.1 = y →
        dist (fineWitness idx : Point3) (anchor y : Point3) ≤ Real.sqrt rho
  normal_first :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      1 / 4 ≤
        |current.grain.localGrains.planeMap (anchor y) (0 : Fin 3)|
  graph_eq :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      g (wz1Lemma23SnappedYValue rho y) =
        current.grain.localGrains.planeMap (anchor y) (2 : Fin 3) /
          current.grain.localGrains.planeMap (anchor y) (0 : Fin 3)
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  constant_absorption :
    Kakeya.realRpowENN delta (-inputLoss) ≤ C
  constant_ne_top : C ≠ ⊤

namespace PureWZ2SourceCommonBinAnchoredLocalReceipt

variable
    {delta sigma inputLoss rho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {C : ENNReal} {cells : Finset (ℤ × ℤ × ℤ)} {g : ℝ → ℝ}

/-- Build the already-general heterogeneous local-bin input without any
plane map on a coarse union. -/
noncomputable def toHeterogeneousLocalBinInput
    (receipt : PureWZ2SourceCommonBinAnchoredLocalReceipt
      (rho := rho) current C cells g) :
    WZ1Lemma23HeterogeneousLocalBinInput rho sigma (2 * C) cells g where
  fineCarrier := current.grain.shading.union
  coarseRepresentative := receipt.coarseRepresentative
  fineWitness := fun idx => receipt.fineWitness idx
  anchor := fun y => receipt.anchor y
  normal := fun y => current.grain.localGrains.planeMap (receipt.anchor y)
  fine_witness_mem := fun idx _ => (receipt.fineWitness idx).property
  coarse_representative_index := receipt.coarse_representative_index
  coarse_fine_close := receipt.coarse_fine_close
  fine_witness_in_anchor_ball := receipt.fine_witness_in_anchor_ball
  normal_unit := by
    intro y _hy
    exact current.grain.localGrains.planeMap_unit _
  normal_vertical := by
    intro y _hy
    exact current.grain.planeMap_vertical_bound _
  normal_first := receipt.normal_first
  graph_eq := receipt.graph_eq
  fine_local_ad := by
    intro y _hy
    have hpaper :=
      current.grain.localGrains.local_ad rho receipt.delta_le_rho
        receipt.rho_le_one (receipt.anchor y)
    have habsorbed := hpaper.mono_const receipt.constant_absorption
      receipt.constant_ne_top
    have hbounded :
        scalarProjection
            (current.grain.localGrains.planeMap (receipt.anchor y))
            (current.grain.shading.union ∩
              Metric.closedBall (receipt.anchor y : Point3)
                (Real.sqrt rho)) ⊆
          Set.Icc (-4 : ℝ) 4 := by
      apply scalarProjection_paperShading_subset_Icc
      · exact current.grain.localGrains.planeMap_unit _
      · exact Set.inter_subset_left
    exact habsorbed.toIsADSet1 hbounded

end PureWZ2SourceCommonBinAnchoredLocalReceipt

end Kakeya.Assouad

end
