import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PreparedNormalizedPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YResiduePackage

/-!
# Prepared Lemma 23 graph on the selected actual y-residue cells

This module transports the already constructed local graph and local-bin
bound from the full global-slice cell family to the literal y-residue subset.
It then runs the closed four-cycle, tripartite-edge, and normalization
constructions on exactly that selected subset.
-/

namespace Kakeya.Assouad

noncomputable section

/--
Restrict a local-bin package to a subset of its actual cells.

The local graph and numerical bound are unchanged.  Only the finite cell
family and its occupied bin sets shrink.
-/
def WZ1Lemma23LocalBinPackage.restrict
    {rho sigma : ℝ} {C : ENNReal}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (package :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C cells)
    (selected : Finset (ℤ × ℤ × ℤ))
    (hselected : selected ⊆ cells) :
    WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C selected :=
  { g := package.g
    g_lipschitz := package.g_lipschitz
    g_bounded := package.g_bounded
    localBinBound := package.localBinBound
    localBinBound_eq := package.localBinBound_eq
    local_bins := by
      intro y hy
      have hyCells :
          y ∈ wz1Lemma23SnappedYLayers cells :=
        wz1Lemma23_snappedYLayers_mono hselected hy
      exact
        (Finset.card_le_card
            (wz1Lemma23_snappedLocalBinsAt_mono
              rho package.g y hselected)).trans
          (package.local_bins y hyCells) }

@[simp]
lemma WZ1Lemma23LocalBinPackage.restrict_g
    {rho sigma : ℝ} {C : ENNReal}
    {cells selected : Finset (ℤ × ℤ × ℤ)}
    (package :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C cells)
    (hselected : selected ⊆ cells) :
    (package.restrict selected hselected).g = package.g :=
  rfl

@[simp]
lemma WZ1Lemma23LocalBinPackage.restrict_localBinBound
    {rho sigma : ℝ} {C : ENNReal}
    {cells selected : Finset (ℤ × ℤ × ℤ)}
    (package :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C cells)
    (hselected : selected ⊆ cells) :
    (package.restrict selected hselected).localBinBound =
      package.localBinBound :=
  rfl

/--
The complete normalized actual graph after the y-residue selection.
-/
structure WZ1Lemma23YResiduePreparedPackage
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (residuePackage :
      WZ1Lemma23YResiduePackage globalPackage)
    (localPackage :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C globalPackage.cells) where
  selectedLocal :
    WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C residuePackage.cells
  selectedLocal_g :
    selectedLocal.g = localPackage.g
  selectedLocal_bound :
    selectedLocal.localBinBound = localPackage.localBinBound
  prepared :
    WZ1Lemma23PreparedNormalizedPackage
      rho globalPackage.extendedSlope selectedLocal.g
      residuePackage.cells selectedLocal.localBinBound
      globalPackage.globalBinBound
  edge_card :
    prepared.normalized.H.card = prepared.actual.H.card

/--
Build the actual four-cycle graph and its normalized image on the selected
y-residue cells.
-/
theorem wz1_lemma23_y_residue_prepared_package
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (residuePackage :
      WZ1Lemma23YResiduePackage globalPackage)
    (localPackage :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C globalPackage.cells) :
    Nonempty
      (WZ1Lemma23YResiduePreparedPackage
        globalPackage residuePackage localPackage) := by
  let selectedLocal :=
    localPackage.restrict
      residuePackage.cells residuePackage.cells_subset
  rcases
      wz1_lemma23_actual_tripartite_package
        rho globalPackage.extendedSlope selectedLocal.g
        residuePackage.cells selectedLocal.localBinBound
        globalPackage.globalBinBound globalPackage.rho_pos
        selectedLocal.local_bins residuePackage.global_bins with
    ⟨baseHeightIndex, baseGlobalBin, actual, habundance⟩
  rcases actual.normalize globalPackage.rho_pos with
    ⟨normalized, hsourceF, hsourceG₁, hsourceG₂,
      hsourceH, hsourceValues⟩
  have hcard : normalized.H.card = actual.H.card := by
    rw [normalized.card_eq, hsourceH]
  let prepared :
      WZ1Lemma23PreparedNormalizedPackage
        rho globalPackage.extendedSlope selectedLocal.g
        residuePackage.cells selectedLocal.localBinBound
        globalPackage.globalBinBound :=
    { baseHeightIndex := baseHeightIndex
      baseGlobalBin := baseGlobalBin
      actual := actual
      normalized := normalized
      normalized_sourceF := hsourceF
      normalized_sourceG₁ := hsourceG₁
      normalized_sourceG₂ := hsourceG₂
      normalized_sourceH := hsourceH
      normalized_sourceValues := hsourceValues
      abundance := by
        rw [hcard]
        exact habundance }
  exact
    ⟨{ selectedLocal := selectedLocal
       selectedLocal_g := rfl
       selectedLocal_bound := rfl
       prepared := prepared
       edge_card := by simpa [prepared] using hcard }⟩

end

end Kakeya.Assouad
