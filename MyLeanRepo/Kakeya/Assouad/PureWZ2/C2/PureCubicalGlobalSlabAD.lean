import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.ADFiniteUnion
import MyLeanRepo.Kakeya.Assouad.WZ1.ADPerturbation
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry

/-!
# Global-slab AD from the literal cubical Pure WZ2 input

Proposition 6.4 uses the proof of WZ Corollary 5.6 verbatim.  Its first
geometric step is the global-grain localization of WZ Lemma 5.5, which is a
three-dimensional statement on source slabs.  The Pure WZ2 input records the
paper's exact horizontal-slice AD estimate instead.

For a whole-cell paper shading the two formulations are related by the
literal geometry used in the paper.  A source slab of thickness `2 * delta`
meets at most five paper height layers.  Move every point to the midpoint of
its own whole `delta`-cell, apply the exact-slice estimate there, and pay one
`delta` perturbation.  This file records precisely that bridge; no
cross-height continuation is asserted for an arbitrary measurable shading.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

attribute [local instance] Classical.propDecidable

/-- Midpoint height of the paper `delta`-cell with vertical index `layer`. -/
def pureWZ2PaperLayerMidpoint (delta : ℝ) (layer : ℤ) : ℝ :=
  ((layer : ℝ) + 1 / 2) * delta

/-- A total in-domain height attached to a paper layer.  Occupied layers use
their actual midpoint; the fallback is needed only for the other members of
the fixed five-layer indexing set. -/
def pureWZ2PaperLayerSampleHeight (delta : ℝ) (layer : ℤ) : ℝ :=
  if pureWZ2PaperLayerMidpoint delta layer ∈ Set.Icc (-1 : ℝ) 1 then
    pureWZ2PaperLayerMidpoint delta layer
  else 0

theorem pureWZ2PaperLayerSampleHeight_mem
    (delta : ℝ) (layer : ℤ) :
    pureWZ2PaperLayerSampleHeight delta layer ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases h : pureWZ2PaperLayerMidpoint delta layer ∈ Set.Icc (-1 : ℝ) 1
  · simpa [pureWZ2PaperLayerSampleHeight, h] using h
  · simp [pureWZ2PaperLayerSampleHeight, h]

/-- A point of a whole paper cell can be moved vertically to the midpoint of
that same cell without leaving its carrier. -/
theorem pureWZ2PaperLayerMidpoint_mem_of_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    {point : Point3} (hpoint : point ∈ shading.union) :
    let layer := (wz1PaperGridIndex delta point).2.2
    point3 (point 0) (point 1)
        (pureWZ2PaperLayerMidpoint delta layer) ∈ shading.union := by
  let cell := wz1PaperGridIndex delta point
  let layer := cell.2.2
  rcases hpoint with ⟨index, hcarrier⟩
  have hpointCell : point ∈ wz1PaperGridCube delta cell :=
    (mem_wz1PaperGridCube delta cell point).mpr rfl
  have hbox := hpointCell
  rw [wz1PaperGridCube_eq_Ico hdelta cell] at hbox
  have hmidLower :
      (cell.2.2 : ℝ) * delta ≤ pureWZ2PaperLayerMidpoint delta layer := by
    dsimp only [pureWZ2PaperLayerMidpoint, layer]
    nlinarith
  have hmidUpper :
      pureWZ2PaperLayerMidpoint delta layer <
        ((cell.2.2 : ℝ) + 1) * delta := by
    dsimp only [pureWZ2PaperLayerMidpoint, layer]
    nlinarith
  have hmidCell :
      point3 (point 0) (point 1)
          (pureWZ2PaperLayerMidpoint delta layer) ∈
        wz1PaperGridCube delta cell := by
    rw [wz1PaperGridCube_eq_Ico hdelta cell]
    simpa [point3] using
      And.intro hbox.1
        (And.intro hbox.2.1
          (And.intro hbox.2.2.1
            (And.intro hbox.2.2.2.1
              (And.intro hmidLower hmidUpper))))
  exact ⟨index, hcubical index point hcarrier hmidCell⟩

/-- On an occupied whole cell, the total sample height is its genuine cell
midpoint and remains in the cropped height interval. -/
theorem pureWZ2PaperLayerSampleHeight_eq_of_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta)
    {point : Point3} (hpoint : point ∈ shading.union) :
    let layer := (wz1PaperGridIndex delta point).2.2
    pureWZ2PaperLayerSampleHeight delta layer =
      pureWZ2PaperLayerMidpoint delta layer := by
  dsimp only
  let layer := (wz1PaperGridIndex delta point).2.2
  let midpointPoint := point3 (point 0) (point 1)
    (pureWZ2PaperLayerMidpoint delta layer)
  have hmidpoint : midpointPoint ∈ shading.union := by
    exact pureWZ2PaperLayerMidpoint_mem_of_cubical
      hcubical hdelta hpoint
  have haxis := shading_union_subset_axisBox hmidpoint
  have hheight :
      pureWZ2PaperLayerMidpoint delta layer ∈ Set.Icc (-1 : ℝ) 1 := by
    have habs : |midpointPoint (2 : Fin 3)| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using haxis.2.2
    simpa [midpointPoint, point3, abs_le] using habs
  rw [pureWZ2PaperLayerSampleHeight, if_pos hheight]

/-- A point in the source `delta`-slab about `z` has one of the five paper
height-layer indices centered at `floor (z / delta)`. -/
theorem pureWZ2PaperLayer_mem_five_of_mem_slab
    {delta z : ℝ} (hdelta : 0 < delta)
    {point : Point3}
    (hpoint : point (2 : Fin 3) ∈ Set.Icc (z - delta) (z + delta)) :
    (wz1PaperGridIndex delta point).2.2 ∈
      Finset.Icc (Int.floor (z / delta) - 2)
        (Int.floor (z / delta) + 2) := by
  let layer := (wz1PaperGridIndex delta point).2.2
  let centerLayer := Int.floor (z / delta)
  have hcenterLower : (centerLayer : ℝ) ≤ z / delta :=
    Int.floor_le (z / delta)
  have hcenterUpper : z / delta < (centerLayer : ℝ) + 1 :=
    Int.lt_floor_add_one (z / delta)
  have hlowerDiv : (z - delta) / delta ≤ point 2 / delta :=
    (div_le_div_iff_of_pos_right hdelta).2 hpoint.1
  have hupperDiv : point 2 / delta ≤ (z + delta) / delta :=
    (div_le_div_iff_of_pos_right hdelta).2 hpoint.2
  have hlowerReal : ((centerLayer - 2 : ℤ) : ℝ) ≤ point 2 / delta := by
    push_cast
    have hdeltaNe : delta ≠ 0 := hdelta.ne'
    rw [sub_div, div_self hdeltaNe] at hlowerDiv
    linarith
  have hupperReal : point 2 / delta < ((centerLayer + 3 : ℤ) : ℝ) := by
    push_cast
    have hdeltaNe : delta ≠ 0 := hdelta.ne'
    rw [add_div, div_self hdeltaNe] at hupperDiv
    linarith
  have hlower : centerLayer - 2 ≤ layer := by
    change centerLayer - 2 ≤ Int.floor (point 2 / delta)
    exact Int.le_floor.mpr hlowerReal
  have hupperStrict : layer < centerLayer + 3 := by
    change Int.floor (point 2 / delta) < centerLayer + 3
    exact Int.floor_lt.mpr hupperReal
  exact Finset.mem_Icc.mpr ⟨hlower, by omega⟩

/-- For a whole-cell paper shading, exact-slice global AD implies the
height-dependent source-slab certificate used by WZ Lemma 5.5.  The constant
`400 = 8 * 5 * 10` records respectively the one-`delta` perturbation, the
five possible paper height layers, and the paper-to-internal AD bridge. -/
theorem pureWZ2_cubical_exactSlice_globalSlabAD
    {delta sigma : ℝ}
    {paperFamily : Kakeya.Streamlined.TubeFamily delta}
    {paperShading : WZ1PaperTubeShading paperFamily}
    {ordinaryFamily : Kakeya.Streamlined.TubeFamily delta}
    (ordinaryShading : Kakeya.Streamlined.TubeShading ordinaryFamily)
    (hunion : ordinaryShading.union = paperShading.union)
    (hcubical : WZ1PaperIsCubicalShading paperShading)
    (slope : ℝ → ℝ)
    (hslopeLipschitz :
      LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1))
    (hslopeBound : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |slope z| ≤ 3)
    (C : ENNReal)
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice ordinaryShading.union z))
        delta (1 - sigma) (10 * C)) :
    HasGlobalSlabAD ordinaryShading slope sigma (400 * C) := by
  have hdelta : 0 < delta := (hexact 0 (by norm_num)).1
  intro z hz
  let centerLayer := Int.floor (z / delta)
  let layers : Finset ℤ :=
    Finset.Icc (centerLayer - 2) (centerLayer + 2)
  let sampleHeight : ℤ → ℝ := pureWZ2PaperLayerSampleHeight delta
  let piece : ℤ → Set ℝ := fun layer =>
    scalarProjection (globalGrainDirection (slope (sampleHeight layer)))
      (horizontalSlice ordinaryShading.union (sampleHeight layer))
  have hlayersNonempty : layers.Nonempty := by
    refine ⟨centerLayer, ?_⟩
    simp [layers]
  have hpieceAD : ∀ layer ∈ layers,
      IsADSet1 (piece layer) delta (1 - sigma) (10 * C) := by
    intro layer _hlayer
    exact hexact (sampleHeight layer)
      (pureWZ2PaperLayerSampleHeight_mem delta layer)
  have hpiecesBounded :
      (⋃ layer ∈ layers, piece layer) ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value hvalue
    rcases Set.mem_iUnion₂.mp hvalue with ⟨layer, hlayer, hvalue⟩
    exact (hpieceAD layer hlayer).2.2.2.2.1 hvalue
  have hfinite := IsADSet1_finite_union
    hlayersNonempty hpieceAD hpiecesBounded
  have hlayersCard : layers.card = 5 := by
    dsimp only [layers]
    have hcard :
        ((Finset.Icc (centerLayer - 2) (centerLayer + 2)).card : ℤ) =
          centerLayer + 2 + 1 - (centerLayer - 2) :=
      Int.card_Icc_of_le _ _ (by omega)
    have hcardFive :
        ((Finset.Icc (centerLayer - 2) (centerLayer + 2)).card : ℤ) = 5 := by
      rw [hcard]
      ring
    exact_mod_cast hcardFive
  have hfinite' :
      IsADSet1 (⋃ layer ∈ layers, piece layer)
        delta (1 - sigma) (5 * (10 * C)) := by
    simpa [hlayersCard] using hfinite
  have htargetBounded :
      globalGrainProjection slope
          (globalGrainSlab ordinaryShading.union z delta) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hpaper : point ∈ paperShading.union := by
      rw [← hunion]
      exact hpoint.1.1
    have hbox := shading_union_subset_axisBox hpaper
    have h0 : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := hslopeBound (point 2) hpoint.2
    have hformula :
        inner ℝ point (globalGrainDirection (slope (point 2))) =
          point 0 + slope (point 2) * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point (globalGrainDirection (slope (point 2))) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + slope (point 2) * point 1| ≤
          |point 0| + |slope (point 2)| * |point 1| := by
        calc
          _ ≤ |point 0| + |slope (point 2) * point 1| := abs_add_le _ _
          _ = _ := by rw [abs_mul]
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hclose : ∀ value ∈ globalGrainProjection slope
        (globalGrainSlab ordinaryShading.union z delta),
      ∃ sourceValue ∈ ⋃ layer ∈ layers, piece layer,
        |value - sourceValue| ≤ delta := by
    rintro value ⟨point, hpoint, rfl⟩
    let cell := wz1PaperGridIndex delta point
    let layer := cell.2.2
    let rawHeight := pureWZ2PaperLayerMidpoint delta layer
    let selectedHeight := sampleHeight layer
    have hpaper : point ∈ paperShading.union := by
      rw [← hunion]
      exact hpoint.1.1
    have hsampleEq : selectedHeight = rawHeight := by
      exact pureWZ2PaperLayerSampleHeight_eq_of_cubical
        hcubical hdelta hpaper
    let samplePoint : Point3 := point3 (point 0) (point 1) rawHeight
    have hsamplePaper : samplePoint ∈ paperShading.union := by
      exact pureWZ2PaperLayerMidpoint_mem_of_cubical
        hcubical hdelta hpaper
    have hsampleOrdinary : samplePoint ∈ ordinaryShading.union := by
      rw [hunion]
      exact hsamplePaper
    have hsampleHeight : samplePoint (2 : Fin 3) = selectedHeight := by
      simp [samplePoint, point3, hsampleEq]
    have hlayer : layer ∈ layers := by
      exact pureWZ2PaperLayer_mem_five_of_mem_slab hdelta hpoint.1.2
    let sourceValue := inner ℝ samplePoint
      (globalGrainDirection (slope selectedHeight))
    have hsourceValue : sourceValue ∈ ⋃ layer ∈ layers, piece layer := by
      apply Set.mem_iUnion₂.mpr
      refine ⟨layer, hlayer, ?_⟩
      refine ⟨samplePoint, ⟨hsampleOrdinary, hsampleHeight⟩, rfl⟩
    have hpointCell : point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have hcellBox := hpointCell
    rw [wz1PaperGridCube_eq_Ico hdelta cell] at hcellBox
    have hheightClose : |point 2 - selectedHeight| ≤ delta := by
      rw [hsampleEq]
      dsimp only [rawHeight, pureWZ2PaperLayerMidpoint, layer, cell]
      rw [abs_le]
      constructor <;> nlinarith [hcellBox.2.2.2.2.1, hcellBox.2.2.2.2.2]
    have hpointHeight : point 2 ∈ Set.Icc (-1 : ℝ) 1 := hpoint.2
    have hselectedHeight : selectedHeight ∈ Set.Icc (-1 : ℝ) 1 := by
      dsimp only [selectedHeight, sampleHeight]
      exact pureWZ2PaperLayerSampleHeight_mem delta layer
    have hslopeClose :
        |slope (point 2) - slope selectedHeight| ≤ delta := by
      have hlip := hslopeLipschitz.dist_le_mul
        (point 2) hpointHeight selectedHeight hselectedHeight
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      exact hlip.trans hheightClose
    have hy : |point 1| ≤ 1 := by
      have hbox := shading_union_subset_axisBox hpaper
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    refine ⟨sourceValue, hsourceValue, ?_⟩
    have hformula :
        inner ℝ point (globalGrainDirection (slope (point 2))) -
            sourceValue =
          (slope (point 2) - slope selectedHeight) * point 1 := by
      dsimp only [sourceValue, samplePoint]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
      ring
    rw [hformula, abs_mul]
    calc
      |slope (point 2) - slope selectedHeight| * |point 1| ≤
          delta * 1 := mul_le_mul hslopeClose hy (abs_nonneg _) hdelta.le
      _ = delta := by ring
  have hperturbed := hfinite'.perturb_by_delta hclose htargetBounded
  have hconstant :
      (8 : ENNReal) * (5 * (10 * C)) = 400 * C := by ring
  rwa [hconstant] at hperturbed

/-- Paper-literal version of the whole-cell slice-to-slab bridge.  The two
factors of ten are exactly the declared conversions between the public
interval AD predicate and the bounded internal predicate. -/
theorem PureWZ2BoundedLipschitzGlobalGrainData.paperGlobalSlabAD
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2BoundedLipschitzGlobalGrainData shading sigma C)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection data.slope
          (globalGrainSlab shading.union z delta))
        delta (1 - sigma) (4000 * C) := by
  let shadow := pureWZ2ActiveCellShading shading hdelta
  have hunion : shadow.union = shading.union :=
    pureWZ2ActiveCellShading_union shading hdelta hcubical
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (data.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma) (10 * C) :=
    data.activeCellShadow_exactAD hdelta hcubical hbridge data.slope_bound
  have hslab : HasGlobalSlabAD shadow data.slope sigma (400 * C) :=
    pureWZ2_cubical_exactSlice_globalSlabAD shadow hunion hcubical data.slope
      data.slope_lipschitz data.slope_bound C hexact
  intro z hz
  have hinternal : IsADSet1
      (globalGrainProjection data.slope
        (globalGrainSlab shading.union z delta))
      delta (1 - sigma) (400 * C) := by
    simpa [hunion] using hslab z hz
  have hconstantTop : 400 * C ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (data.paper_ad ⟨0, by norm_num⟩).2.2.2.2.1
  have hpaper := hbridge.2 _ delta (1 - sigma) (400 * C)
    hdelta hdeltaOne hconstantTop hinternal
  convert hpaper using 1 <;> ring

end Kakeya.Assouad

end
