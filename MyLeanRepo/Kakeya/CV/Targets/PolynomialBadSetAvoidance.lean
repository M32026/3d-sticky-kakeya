import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.PolynomialBadSetCover
import MyLeanRepo.Kakeya.CV.BadSetAtomCardinality
import MyLeanRepo.Kakeya.CV.AntipodalSignSeparation
import MyLeanRepo.Kakeya.CV.FiniteDyadicPolynomialBadSetDecomposition
import MyLeanRepo.Kakeya.CV.FinitePaletteTranslatePacking
import MyLeanRepo.Kakeya.CV.UniformFiniteBisectionStability
import MyLeanRepo.Kakeya.CV.StableEllipsoidPaletteBandFiniteness
import MyLeanRepo.Kakeya.CV.PolynomialBadSetAvoidance.Helpers
import MyLeanRepo.Kakeya.CV.PolynomialBadSetAvoidance.AssemblyHelpers
import MyLeanRepo.Kakeya.CV.UnitSphereHausdorffArea
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Proof of polynomial bad-set avoidance

Assembles all geometric and analytic leaves into the final Borsuk--Ulam
avoidance argument.
-/

noncomputable section


open MeasureTheory TopCat Finset
open scoped BigOperators ENNReal NNReal Real

namespace Kakeya.CV

theorem polynomial_badSet_avoidance.{u}
    (hNormSphere : NormalizedPolynomialSphereStatement)
    (hMollSurface : ConcreteMollifiedSurfaceStatement)
    (hMollVis : ConcreteMollifiedVisibilityStatement)
    (hCont : ConcreteVisibilityHomotheticContinuityStatement)
    (hFinDyadic : FiniteDyadicPolynomialBadSetDecompositionStatement)
    (hBandFinite : StableEllipsoidPaletteBandFinitenessStatement)
    (hPalettePacking : FinitePaletteTranslatePackingStatement)
    (hPrincipalAxesRep : PrincipalAxesRepresentationStatement)
    (hUniformBisection : UniformFiniteBisectionStabilityStatement.{0})
    (hMollManyBisects : PrincipalAxesMollifiedManyBisectionsStatement.{0})
    (hManyBisects : PrincipalAxesManyBisectionsStatement.{0})
    (hGeneric : GenericPolynomialRegularityStatement)
    (hSquarefree : SquarefreeSingularSetNullStatement)
    (hCylinder : PolynomialCylinderEstimateStatement)
    (hDirectionalBudget : PrincipalAxesMollifiedDirectionalBudgetStatement)
    (hVolumeComp : CenteredHomotheticVolumeComparisonStatement)
    (hSelectionStability : EllipsoidSelectionStabilityStatement)
    (hSignSep : AntipodalSignSeparationStatement)
    (hAtomCard : BadSetAtomCardinalityStatement.{u, 0, 0})
    (hBadSetCover : PolynomialBadSetCoverStatement.{u}) :
    PolynomialBadSetAvoidanceConclusion.{u} := by

  -- ============================================================
  -- Step 1: Extract global palette and constants
  -- ============================================================
  rcases hFinDyadic with ⟨α, N, net, colour, hα, hN, hcentered, hseparation, hDecomp⟩
  rcases hPalettePacking with ⟨C_pack, hC_pack_pos, hPack⟩
  rcases hMollManyBisects hManyBisects hGeneric hSquarefree hCylinder with
    ⟨C_mb, hC_mb_pos, hManyBisects⟩

  -- ============================================================
  -- Step 2: Choose geometric constants
  -- ============================================================
  let R : ℝ := α

  let sphereArea : ENNReal := codimensionOneMeasure 3 (unitSphere 3)
  let ballVol : ENNReal := volume (unitBall 3)

  have hballVol_pos : 0 < ballVol := volume_unitBall_pos
  have hballVol_ne_top : ballVol ≠ ⊤ := volume_unitBall_lt_top.ne

  have h_sphereArea_pos : 0 < sphereArea := by
    have h1 : ENNReal.ofReal (Real.pi / 4) * sphereArea =
        (3 : ℝ≥0∞) * ballVol := unitSphere_standardArea_eq_three_mul_volume
    have h2 : 0 < (3 : ℝ≥0∞) * ballVol := by positivity
    have h3 : 0 < ENNReal.ofReal (Real.pi / 4) * sphereArea := by rw [h1] <;> exact h2
    have h4 : 0 < ENNReal.ofReal (Real.pi / 4) := by
      exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
    by_contra h5
    have h6 : sphereArea = 0 := by simpa using h5
    rw [h6] at h3
    simp at h3 <;> exact h2.ne' h3
  have h_sphereArea_ne_top : sphereArea ≠ ⊤ := by
    have h1 : ENNReal.ofReal (Real.pi / 4) * sphereArea = (3 : ℝ≥0∞) * ballVol :=
      unitSphere_standardArea_eq_three_mul_volume
    have h2 : (3 : ℝ≥0∞) * ballVol ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hballVol_ne_top
    have h3 : ENNReal.ofReal (Real.pi / 4) * sphereArea ≠ ⊤ := by rw [h1] <;> exact h2
    by_contra h4
    rw [h4] at h3
    have h5 : ENNReal.ofReal (Real.pi / 4) ≠ 0 := by
      have h51 : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
      have h52 : 0 < ENNReal.ofReal (Real.pi / 4) := ENNReal.ofReal_pos.mpr h51
      exact h52.ne'
    simp [h5] at h3 <;> exact h2 h3

  let denom : ENNReal :=
    (3 : ℝ≥0∞) * (C_mb : ℝ≥0∞) * ENNReal.ofReal α * (C_pack : ℝ≥0∞) * ballVol

  have hdenom_pos : 0 < denom := by
    dsimp only [denom]
    have hα_pos : 0 < α := by linarith
    have h1 : 0 < (3 : ℝ≥0∞) := by norm_num
    have h2 : 0 < (C_mb : ℝ≥0∞) := by exact_mod_cast hC_mb_pos
    have h3 : 0 < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα_pos
    have h4 : 0 < (C_pack : ℝ≥0∞) := by exact_mod_cast hC_pack_pos
    positivity
  have hdenom_ne_zero : denom ≠ 0 := hdenom_pos.ne'
  have hdenom_ne_top : denom ≠ ⊤ := by
    dsimp only [denom]
    have h1 : (C_mb : ℝ≥0∞) ≠ ⊤ := by simp
    have h2 : (C_pack : ℝ≥0∞) ≠ ⊤ := by simp
    have h3 : ((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp) h1
    have h4 : (((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞)) * ENNReal.ofReal α) ≠ ⊤ := by
      exact ENNReal.mul_ne_top h3 ENNReal.ofReal_ne_top
    have h5 : ((((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞)) * ENNReal.ofReal α) * (C_pack : ℝ≥0∞)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top h4 h2
    exact ENNReal.mul_ne_top h5 hballVol_ne_top

  let threshold : ENNReal := sphereArea / denom

  have hthreshold_pos : 0 < threshold :=
    ENNReal.div_pos h_sphereArea_pos.ne' hdenom_ne_top
  have hthreshold_ne_top : threshold ≠ ⊤ :=
    ENNReal.div_ne_top h_sphereArea_ne_top hdenom_ne_zero

  let thresholdReal : ℝ := threshold.toReal
  have hthresholdReal_pos : 0 < thresholdReal :=
    ENNReal.toReal_pos hthreshold_pos.ne' hthreshold_ne_top
  have hthreshold_ofReal : ENNReal.ofReal thresholdReal = threshold :=
    ENNReal.ofReal_toReal hthreshold_ne_top

  let ηMax : ℝ := thresholdReal / 2
  let η : ℝ := min ηMax 1 / (8 * max R 1)
  have hη_pos : 0 < η := by positivity
  have hη_le_one : η ≤ 1 := by
    have hden : 1 ≤ 8 * max R 1 := by nlinarith [le_max_right R 1]
    have hnum_nonneg : 0 ≤ min ηMax 1 := by positivity
    have h : min ηMax 1 / (8 * max R 1) ≤ min ηMax 1 := by
      apply div_le_self hnum_nonneg hden
    linarith [min_le_right ηMax 1]
  have hη_small : ENNReal.ofReal η < threshold := by
    have h1 : η < thresholdReal := by
      have h2 : min (thresholdReal / 2) 1 ≤ thresholdReal / 2 := min_le_left _ _
      have h3 : min (thresholdReal / 2) 1 / (8 * max R 1) ≤ thresholdReal / 2 / 8 := by
        gcongr <;> nlinarith [le_max_right R 1]
      have h4 : thresholdReal / 2 / 8 < thresholdReal := by
        have h5 : 0 < thresholdReal := hthresholdReal_pos
        linarith
      linarith
    have h5 : ENNReal.ofReal η < ENNReal.ofReal thresholdReal := by
      rw [ENNReal.ofReal_lt_ofReal_iff hthresholdReal_pos]
      exact h1
    rw [hthreshold_ofReal] at h5
    exact h5

  -- Cvis chosen so that C_pack * α^3 * η^{-3} * Cvis^3 ≤ 1
  let Cvis : ℝ := η / (2 * (C_pack : ℝ) * α^3 + 1)
  have hCvis_pos : 0 < Cvis := by positivity

  let Ccount : ℝ := (N : ℝ) * (8 / 7)
  have hCcount_pos : 0 < Ccount := by
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    positivity

  refine' ⟨Ccount, Cvis, hCcount_pos, hCvis_pos, _⟩

  intro Cube _ k P center M hPdim_pos hDimMargin
  classical

  -- ============================================================
  -- Step 3: Define levels and palette bands (independent of ε)
  -- ============================================================
  let B_vis : ℝ := Real.rpow (volume (unitBall 3)).toReal (-1 / 3 : ℝ)
  have hB_vis_pos : 0 < B_vis := by
    apply Real.rpow_pos_of_pos
    exact ENNReal.toReal_pos volume_unitBall_pos.ne' volume_unitBall_lt_top.ne

  let bandThreshold : ℝ := B_vis / (α * max R 1)
  have hbandThreshold_pos : 0 < bandThreshold := by
    dsimp only [bandThreshold]
    have h1 : 0 < α := by linarith
    have h2 : 0 < max R 1 := by positivity
    positivity

  let levels : Cube → ℕ := fun q =>
    if h : 0 < (M q : ℝ) then
      Nat.find (exists_dyadic_level_below (Cvis * (M q : ℝ)) bandThreshold hbandThreshold_pos)
    else 0

  have hlevels_prop : ∀ q, 0 < (M q : ℝ) →
      Real.rpow 2 (-(levels q : ℝ)) * (Cvis * (M q : ℝ)) < bandThreshold := by
    intro q hM
    dsimp only [levels]
    rw [dif_pos hM]
    exact Nat.find_spec (exists_dyadic_level_below (Cvis * (M q : ℝ)) bandThreshold hbandThreshold_pos)

  let volLower (q : Cube) (r : ℕ) : ℝ :=
    α^(-3 : ℝ) * (2 : ℝ)^(3 * r) * (Cvis * (M q : ℝ))^(-3 : ℝ)

  let band (q : Cube) (r : ℕ) : Set EllipsoidParameter :=
    {E | 0 < (M q : ℝ) ∧ E ∈ net ∧
      ellipsoidCarrier E ⊆ Metric.closedBall 0 R ∧
      ENNReal.ofReal (volLower q r) ≤ volume (ellipsoidCarrier E)}

  have hseparation' : ∀ E₁ ∈ net, ∀ E₂ ∈ net,
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt 0 (α ^ 3) (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂ := by
    intro E₁ hE₁ E₂ hE₂ hcol hclose
    exact hseparation E₁ E₂ hE₁ hE₂ hcol hclose

  have hband_finite : ∀ q r, (band q r).Finite := by
    intro q r
    by_cases hM : 0 < (M q : ℝ)
    · have hvl_pos : 0 < volLower q r := by
        dsimp only [volLower]; positivity
      have hsub : band q r ⊆ {E : EllipsoidParameter | E ∈ net ∧
          ellipsoidCarrier E ⊆ Metric.closedBall 0 R ∧
          ENNReal.ofReal (volLower q r) ≤ volume (ellipsoidCarrier E)} := by
        intro E hE
        exact ⟨hE.2.1, hE.2.2.1, hE.2.2.2⟩
      have hfin : Set.Finite {E : EllipsoidParameter | E ∈ net ∧
          ellipsoidCarrier E ⊆ Metric.closedBall 0 R ∧
          ENNReal.ofReal (volLower q r) ≤ volume (ellipsoidCarrier E)} :=
        hBandFinite α N net colour hα hcentered hseparation' R (volLower q r)
          (by linarith) hvl_pos
      exact Set.Finite.subset hfin hsub
    · have h_empty : band q r = ∅ := by
        ext E
        simp [band, hM]
        <;> tauto
      rw [h_empty]
      exact Set.finite_empty

  let palette : Set EllipsoidParameter :=
    ⋃ q ∈ (Finset.univ : Finset Cube), ⋃ r ∈ Finset.range (levels q), band q r

  have hpalette_finite : palette.Finite := by
    have h1 : ∀ q, (⋃ r ∈ Finset.range (levels q), band q r).Finite := by
      intro q
      have hfin : (Finset.range (levels q) : Set ℕ).Finite := Finset.finite_toSet _
      exact hfin.biUnion (fun r _ => hband_finite q r)
    have h_eq : palette = ⋃ q ∈ (Finset.univ : Finset Cube), (⋃ r ∈ Finset.range (levels q), band q r) := by
      ext E
      simp [palette, Finset.mem_univ]
      <;> tauto
    rw [h_eq]
    exact (Finset.finite_toSet (Finset.univ : Finset Cube)).biUnion (fun q _ => h1 q)

  have h_in_palette : ∀ q r, r ∈ Finset.range (levels q) → ∀ E ∈ band q r, E ∈ palette := by
    intro q r hr E hE
    have h1 : E ∈ (⋃ r' ∈ Finset.range (levels q), band q r') := by
      apply Set.mem_iUnion₂.mpr
      exact ⟨r, hr, hE⟩
    exact Set.mem_iUnion₂.mpr ⟨q, Finset.mem_univ q, h1⟩

  have hpalette_centered : ∀ E ∈ palette, E.1 = 0 := by
    intro E hE
    rcases Set.mem_iUnion₂.mp hE with ⟨q, _, hq⟩
    rcases Set.mem_iUnion₂.mp hq with ⟨r, _, hEband⟩
    exact hcentered E hEband.2.1

  have hpalette_outer : ∀ E ∈ palette, ellipsoidCarrier E ⊆ Metric.closedBall 0 R := by
    intro E hE
    rcases Set.mem_iUnion₂.mp hE with ⟨q, _, hq⟩
    rcases Set.mem_iUnion₂.mp hq with ⟨r, _, hEband⟩
    exact hEband.2.2.1

  -- ============================================================
  -- Step 4: Apply palette translate packing
  -- ============================================================
  have hηMax_pos : 0 < ηMax := by
    dsimp only [ηMax]
    linarith [hthresholdReal_pos]
  rcases hPack palette hpalette_finite hpalette_centered R ηMax
    (by linarith) hηMax_pos hpalette_outer with ⟨hη_pack, hηle, htranslate⟩

  choose n z hz_subset hz_disjoint hz_lower hz_upper using
    fun (E : EllipsoidParameter) (hE : E ∈ palette) (c : Point 3) =>
      htranslate E hE c

  -- Wrapper functions that don't require proof arguments
  let n' (E : EllipsoidParameter) (c : Point 3) : ℕ :=
    if h : E ∈ palette then n E h c else 0
  let z' (E : EllipsoidParameter) (c : Point 3) (j : ℕ) : Point 3 :=
    if h : E ∈ palette then
      if hj : j < n E h c then z E h c ⟨j, hj⟩ else 0
    else 0

  -- ============================================================
  -- Step 5: Define atom type
  -- ============================================================
  let bandColour (q : Cube) (r : ℕ) (θ : Fin N) : Set EllipsoidParameter :=
    {E ∈ band q r | colour E = θ}

  have hbandColour_finite : ∀ q r θ, (bandColour q r θ).Finite :=
    fun q r θ => (hband_finite q r).subset (fun E hE => hE.1)

  let maxTranslates (q : Cube) (r : Fin (levels q)) (θ : Fin N) : ℕ :=
    if h : (bandColour q (r : ℕ) θ).Nonempty then
      let bfinset := (hbandColour_finite q (r : ℕ) θ).toFinset
      bfinset.attach.sup (fun Evar : {E // E ∈ bfinset} =>
        n' Evar.val (center q))
    else 0

  let Atom (q : Cube) (r : Fin (levels q)) (θ : Fin N) : Type :=
    Fin (maxTranslates q r θ)

  -- ============================================================
  -- Step 6: Collect all regions and get ε from uniform stability
  -- ============================================================
  let paletteFinset : Finset EllipsoidParameter := hpalette_finite.toFinset

  let allRegionsFinset : Finset (Set (Point 3)) :=
    paletteFinset.biUnion (fun E =>
      (Finset.univ : Finset Cube).biUnion (fun q =>
        (Finset.range (n' E (center q))).image
          (fun j => scaledEllipsoid E.2 η (z' E (center q) j))))

  let RegionIdx : Type := {s : Set (Point 3) // s ∈ allRegionsFinset}
  let _regionFintype : Fintype RegionIdx := allRegionsFinset.fintypeCoeSort
  let regions : RegionIdx → Set (Point 3) := fun i => i.1

  have hregions_meas : ∀ i, MeasurableSet (regions i) := by
    intro i
    have hmem : i.1 ∈ allRegionsFinset := i.2
    have h1 : ∃ (E : EllipsoidParameter), E ∈ paletteFinset ∧
        i.1 ∈ (Finset.univ : Finset Cube).biUnion (fun q : Cube =>
          (Finset.range (n' E (center q))).image
            (fun j => scaledEllipsoid E.2 η (z' E (center q) j))) :=
      Finset.mem_biUnion.mp hmem
    rcases h1 with ⟨E, hE, hmem2⟩
    have h2 : ∃ (q : Cube), q ∈ (Finset.univ : Finset Cube) ∧
        i.1 ∈ (Finset.range (n' E (center q))).image
          (fun j => scaledEllipsoid E.2 η (z' E (center q) j)) :=
      Finset.mem_biUnion.mp hmem2
    rcases h2 with ⟨q, _, hmem3⟩
    have h3 : ∃ (j : ℕ), j ∈ Finset.range (n' E (center q)) ∧
        scaledEllipsoid E.2 η (z' E (center q) j) = i.1 :=
      Finset.mem_image.mp hmem3
    rcases h3 with ⟨j, _, h_eq⟩
    change MeasurableSet i.1
    rw [← h_eq]
    exact scaledEllipsoid_measurableSet E.2 η (z' E (center q) j)
  have hregions_fin : ∀ i, volume (regions i) < ⊤ := by
    intro i
    have hmem : i.1 ∈ allRegionsFinset := i.2
    have h1 : ∃ (E : EllipsoidParameter), E ∈ paletteFinset ∧
        i.1 ∈ (Finset.univ : Finset Cube).biUnion (fun q : Cube =>
          (Finset.range (n' E (center q))).image
            (fun j => scaledEllipsoid E.2 η (z' E (center q) j))) :=
      Finset.mem_biUnion.mp hmem
    rcases h1 with ⟨E, hE, hmem2⟩
    have h2 : ∃ (q : Cube), q ∈ (Finset.univ : Finset Cube) ∧
        i.1 ∈ (Finset.range (n' E (center q))).image
          (fun j => scaledEllipsoid E.2 η (z' E (center q) j)) :=
      Finset.mem_biUnion.mp hmem2
    rcases h2 with ⟨q, _, hmem3⟩
    have h3 : ∃ (j : ℕ), j ∈ Finset.range (n' E (center q)) ∧
        scaledEllipsoid E.2 η (z' E (center q) j) = i.1 :=
      Finset.mem_image.mp hmem3
    rcases h3 with ⟨j, _, h_eq⟩
    change volume i.1 < ⊤
    rw [← h_eq]
    exact scaledEllipsoid_volume_lt_top E.2 η (z' E (center q) j)

  rcases hUniformBisection k P (ι := RegionIdx) regions hregions_meas hregions_fin with
    ⟨ε, hε_pos, hStable⟩

  -- ============================================================
  -- Step 7: Apply dyadic decomposition with ε for each cube
  -- ============================================================
  let selected : Cube → CoefficientSpace P.dim → EllipsoidParameter := fun q =>
    if h : 0 < (M q : ℝ) then
      Classical.choose (hDecomp k P ε (center q) (Cvis * (M q : ℝ))
        hε_pos (mul_pos hCvis_pos h))
    else fun _ => (0, 1)

  let selected_levels : Cube → ℕ := fun q =>
    if h : 0 < (M q : ℝ) then
      Classical.choose (Classical.choose_spec (hDecomp k P ε (center q)
        (Cvis * (M q : ℝ)) hε_pos (mul_pos hCvis_pos h)))
    else 0

  have h_layer_bounded : ∀ q (x : CoefficientSpace P.dim) (r : ℕ),
      x ∈ concretePolynomialBadLayer P ε (unitCube (center q)) (Cvis * (M q : ℝ)) r →
      r < levels q := by
    intro q x r hr
    by_cases hM : 0 < (M q : ℝ)
    · by_contra hnot
      have hle : levels q ≤ r := Nat.le_of_not_gt hnot
      have hpow_le : Real.rpow 2 (-(r : ℝ)) ≤ Real.rpow 2 (-(levels q : ℝ)) :=
        dyadic_rpow_antitone hle
      have h1 : Real.rpow 2 (-(r : ℝ)) * (Cvis * (M q : ℝ)) < bandThreshold := by
        calc
          Real.rpow 2 (-(r : ℝ)) * (Cvis * (M q : ℝ))
            ≤ Real.rpow 2 (-(levels q : ℝ)) * (Cvis * (M q : ℝ)) :=
              mul_le_mul_of_nonneg_right hpow_le (by positivity)
          _ < bandThreshold := hlevels_prop q hM
      have hvis_le : concreteMollifiedVisibility P ε x (unitCube (center q)) ≤
          Real.rpow 2 (-(r : ℝ)) * (Cvis * (M q : ℝ)) := hr.2
      have hbandThreshold_le_Bvis : bandThreshold ≤ B_vis := by
        dsimp only [bandThreshold]
        have h3 : 1 ≤ α * max R 1 := by
          have h4 : 1 < α := hα
          have h5 : 1 ≤ max R 1 := le_max_right R 1
          nlinarith
        exact div_le_self hB_vis_pos.le h3
      have hvis_lt_Bvis : concreteMollifiedVisibility P ε x (unitCube (center q)) < B_vis := by
        calc
          concreteMollifiedVisibility P ε x (unitCube (center q))
            ≤ Real.rpow 2 (-(r : ℝ)) * (Cvis * (M q : ℝ)) := hvis_le
          _ < bandThreshold := h1
          _ ≤ B_vis := hbandThreshold_le_Bvis
      have hbody := hMollVis k P (unitCube (center q)) (center q) ε x
          (unitCube_measurableSet (center q)) (unitCube_subset_closedBall (center q)) hε_pos
      have hB_vis_le : B_vis ≤ concreteMollifiedVisibility P ε x (unitCube (center q)) :=
        concreteMollifiedVisibility_unitBall_lower hbody.1
      exact not_le.mpr hvis_lt_Bvis hB_vis_le
    · have hM_nonpos : (M q : ℝ) ≤ 0 := by linarith
      have hCM_nonpos : Cvis * (M q : ℝ) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hM_nonpos
      have h_empty : concretePolynomialBadLayer P ε (unitCube (center q))
          (Cvis * (M q : ℝ)) r = ∅ :=
        badLayer_empty_when_M_nonpos hCM_nonpos
      rw [h_empty] at hr
      exact False.elim hr

  let hDecompSpec (q : Cube) (hM : 0 < (M q : ℝ)) :=
    Classical.choose_spec (Classical.choose_spec (hDecomp k P ε (center q) (Cvis * (M q : ℝ))
      hε_pos (mul_pos hCvis_pos hM)))

  let sel (q : Cube) (hM : 0 < (M q : ℝ)) :=
    Classical.choose (hDecomp k P ε (center q) (Cvis * (M q : ℝ))
      hε_pos (mul_pos hCvis_pos hM))

  have hsel_eq : ∀ (q : Cube) (hM : 0 < (M q : ℝ)) (x : CoefficientSpace P.dim),
      selected q x = sel q hM x := by
    intro q hM x
    unfold selected
    rw [dif_pos hM]
    <;> rfl

  have hselected_even : ∀ q, 0 < (M q : ℝ) →
      ∀ x, selected q (-x) = selected q x := by
    intro q hM
    have hspec := hDecompSpec q hM
    intro x
    have h1 : selected q (-x) = sel q hM (-x) := hsel_eq q hM (-x)
    have h2 : selected q x = sel q hM x := hsel_eq q hM x
    rw [h1, h2]
    exact hspec.1 x

  have hselected_close : ∀ q, 0 < (M q : ℝ) → ∀ x,
      x ∈ concretePolynomialBadSet P ε (unitCube (center q)) (Cvis * (M q : ℝ)) →
      0 < concreteMollifiedVisibility P ε x (unitCube (center q)) →
      selected q x ∈ net ∧
      AreHomotheticallyCloseAt 0 α
        (concreteMollifiedVisibilityBody P ε x (unitCube (center q)))
        (ellipsoidCarrier (selected q x)) := by
    intro q hM
    have hspec := hDecompSpec q hM
    intro x hbad hvis
    have h1 : selected q x = sel q hM x := hsel_eq q hM x
    rw [h1]
    exact hspec.2.1 x hbad hvis

  have hdecomp_eq : ∀ q, 0 < (M q : ℝ) →
      {x | x ∈ concretePolynomialBadSet P ε (unitCube (center q)) (Cvis * (M q : ℝ)) ∧
        0 < concreteMollifiedVisibility P ε x (unitCube (center q))} =
      ⋃ r : Fin (selected_levels q), ⋃ θ : Fin N,
        {x | x ∈ concretePolynomialBadLayer P ε (unitCube (center q))
          (Cvis * (M q : ℝ)) (r : ℕ) ∧ colour (selected q x) = θ} := by
    intro q hM
    have hspec := hDecompSpec q hM
    have h1 : selected q = sel q hM := by
      funext x; exact hsel_eq q hM x
    have h2 : selected_levels q =
        Classical.choose (Classical.choose_spec (hDecomp k P ε (center q)
          (Cvis * (M q : ℝ)) hε_pos (mul_pos hCvis_pos hM))) := by
      unfold selected_levels
      rw [dif_pos hM]
      <;> rfl
    rw [h1, h2]
    exact hspec.2.2

  -- ============================================================
  -- Step 8: Define selectedRegion and D for each atom
  -- ============================================================
  let I := Σ (q : Cube), Σ (r : Fin (levels q)), Σ (θ : Fin N), Atom q r θ

  let selectedRegion (i : I) (x : CoefficientSpace P.dim) : Set (Point 3) :=
    let q := i.1
    let j := i.2.2.2
    let E := selected q x
    scaledEllipsoid E.2 η (z' E (center q) (j : ℕ))

  let D (i : I) : Set (CoefficientSpace P.dim) :=
    let q := i.1
    let r := i.2.1
    let θ := i.2.2.1
    let j := i.2.2.2
    {x | x ∈ normalizedPolynomialParameters P ∧
      x ∈ concretePolynomialBadLayer P ε (unitCube (center q))
        (Cvis * (M q : ℝ)) (r : ℕ) ∧
      colour (selected q x) = θ ∧
      (j : ℕ) < n' (selected q x) (center q) ∧
      ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion i x)}

  -- ============================================================
  -- Step 9: Define bad set and prove cover
  -- ============================================================
  let bad : Set (CoefficientSpace P.dim) :=
    {x | x ∈ normalizedPolynomialParameters P ∧
      ∃ q : Cube, concreteMollifiedVisibility P ε x (unitCube (center q)) ≤
        Cvis * (M q : ℝ)}

  -- Factored properties for sign class cover
  have hD_antipodal_all : ∀ (i : I), ∀ x, x ∈ D i → -x ∈ D i := by
    intro i x hx
    have hx_norm2 : x ∈ normalizedPolynomialParameters P := hx.1
    have hneg_norm : -x ∈ normalizedPolynomialParameters P := by
      simpa [normalizedPolynomialParameters, Metric.mem_sphere] using hx_norm2
    have hvis_even : concreteMollifiedVisibility P ε (-x) (unitCube (center i.1)) =
        concreteMollifiedVisibility P ε x (unitCube (center i.1)) := by
      have hbody := concreteMollifiedVisibilityBody_even P ε hε_pos (unitCube (center i.1)) x
      rw [concreteMollifiedVisibility, concreteMollifiedVisibility, hbody]
    have hlayer : x ∈ concretePolynomialBadLayer P ε (unitCube (center i.1))
        (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) := hx.2.1
    have hneg_layer : -x ∈ concretePolynomialBadLayer P ε (unitCube (center i.1))
        (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) := by
      simpa [concretePolynomialBadLayer, hvis_even] using hlayer
    have hsel_even : selected i.1 (-x) = selected i.1 x := by
      by_cases hM : 0 < (M i.1 : ℝ)
      · exact hselected_even i.1 hM x
      · have h1 : selected i.1 = fun _ => (0, 1) := by
          funext y; unfold selected; rw [dif_neg hM]
        rw [h1]
    have hbisect_even : ∀ (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3)),
        PolynomialBisects (-p) s ↔ PolynomialBisects p s := by
      intro p s
      have h1 : {y : Point 3 | polynomialValue (-p) y < 0} = {y | 0 < polynomialValue p y} := by
        ext y; simp [polynomialValue_neg] <;> linarith
      have h2 : {y : Point 3 | 0 < polynomialValue (-p) y} = {y | polynomialValue p y < 0} := by
        ext y; simp [polynomialValue_neg] <;> linarith
      simp only [PolynomialBisects, h1, h2]; exact ⟨Eq.symm, Eq.symm⟩
    have hreg : selectedRegion i (-x) = selectedRegion i x := by
      simp [selectedRegion, hsel_even]
    exact ⟨hneg_norm, hneg_layer, by rw [hsel_even]; exact hx.2.2.1,
      by rw [hsel_even]; exact hx.2.2.2.1,
      by have hnb : ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion i x) := hx.2.2.2.2
         have hpoly : parameterPolynomial P (-x) = -parameterPolynomial P x := parameterPolynomial_neg P x
         have h : PolynomialBisects (parameterPolynomial P (-x)) (selectedRegion i (-x)) ↔
             PolynomialBisects (parameterPolynomial P x) (selectedRegion i x) := by
           rw [hpoly, hreg]; exact hbisect_even (parameterPolynomial P x) (selectedRegion i x)
         exact h.not.mpr hnb⟩

  have hRegion_antipodal_all : ∀ (i : I), ∀ x, x ∈ D i → selectedRegion i (-x) = selectedRegion i x := by
    intro i x hx
    have hsel_even : selected i.1 (-x) = selected i.1 x := by
      by_cases hM : 0 < (M i.1 : ℝ)
      · exact hselected_even i.1 hM x
      · have h1 : selected i.1 = fun _ => (0, 1) := by
          funext y; unfold selected; rw [dif_neg hM]
        rw [h1]
    simp [selectedRegion, hsel_even]

  have hRegion_meas_all : ∀ (i : I), ∀ x, x ∈ D i → MeasurableSet (selectedRegion i x) := by
    intro i x hx
    let E := selected i.1 x
    have hcompact : IsCompact (selectedRegion i x) := by
      have h_eq1 : selectedRegion i x = scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) := by rfl
      rw [h_eq1]
      have h1 : IsCompact (Metric.closedBall (0 : Point 3) η) := isCompact_closedBall _ _
      have h2 : IsCompact (E.2 '' Metric.closedBall (0 : Point 3) η) :=
        h1.image E.2.toContinuousLinearEquiv.continuous
      let f : Point 3 → Point 3 := fun y => z' E (center i.1) (i.2.2.2 : ℕ) + y
      have hf : Continuous f := continuous_const_add _
      have h3 : scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) = f '' (E.2 '' Metric.closedBall (0 : Point 3) η) := by
        unfold scaledEllipsoid <;> rfl
      rw [h3]; exact h2.image hf
    exact hcompact.isClosed.measurableSet

  have hRegion_finite_all : ∀ (i : I), ∀ x, x ∈ D i → volume (selectedRegion i x) < ⊤ := by
    intro i x hx
    let E := selected i.1 x
    have h_eq1 : selectedRegion i x = scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) := by rfl
    rw [h_eq1]
    have h1 : IsCompact (Metric.closedBall (0 : Point 3) η) := isCompact_closedBall _ _
    have h2 : IsCompact (E.2 '' Metric.closedBall (0 : Point 3) η) :=
      h1.image E.2.toContinuousLinearEquiv.continuous
    let f : Point 3 → Point 3 := fun y => z' E (center i.1) (i.2.2.2 : ℕ) + y
    have hf : Continuous f := continuous_const_add _
    have h3 : scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) = f '' (E.2 '' Metric.closedBall (0 : Point 3) η) := by
      unfold scaledEllipsoid <;> rfl
    rw [h3]
    exact (h2.image hf).isBounded.measure_lt_top

  have hPoly_nonzero_all : ∀ (i : I), ∀ x, x ∈ D i → parameterPolynomial P x ≠ 0 := by
    intro i x hx
    exact parameterPolynomial_ne_zero_of_normalized hx.1

  have hcover : bad ⊆ ⋃ i : I,
      (positiveSignClass P (selectedRegion i) (D i) ∪
        (fun x => -x) '' positiveSignClass P (selectedRegion i) (D i)) := by
    intro x hx
    have hx_norm : x ∈ normalizedPolynomialParameters P := hx.1
    rcases hx.2 with ⟨q, hvis_le⟩
    by_cases hM0 : (M q : ℝ) = 0
    · -- M q = 0: bad set for this cube is empty, contradiction
      have hCM_zero : Cvis * (M q : ℝ) = 0 := by
        rw [hM0] <;> ring
      have hbad_empty : concretePolynomialBadSet P ε (unitCube (center q)) (Cvis * (M q : ℝ)) = ∅ := by
        rw [hCM_zero]
        exact concretePolynomialBadSet_zero hMollVis P ε (center q) hε_pos
      have h_x_in_badset : x ∈ concretePolynomialBadSet P ε (unitCube (center q)) (Cvis * (M q : ℝ)) := hvis_le
      rw [hbad_empty] at h_x_in_badset
      simpa using h_x_in_badset
    · -- M q > 0
      have hMq_pos : 0 < (M q : ℝ) := by
        have h1 : 0 ≤ (M q : ℝ) := by exact_mod_cast (M q).prop
        exact lt_of_le_of_ne h1 (Ne.symm hM0)
      have hCM_pos : 0 < Cvis * (M q : ℝ) := mul_pos hCvis_pos hMq_pos
      let K := concreteMollifiedVisibilityBody P ε x (unitCube (center q))
      have hU_meas : MeasurableSet (unitCube (center q)) := unitCube_measurableSet (center q)
      have hU_sub : unitCube (center q) ⊆ Metric.closedBall (center q) 1 := unitCube_subset_closedBall (center q)
      have hbody := hMollVis k P (unitCube (center q)) (center q) ε x hU_meas hU_sub hε_pos
      have hK_pos : 0 < volume K := Measure.measure_pos_of_nonempty_interior volume hbody.1.2.2
      have hK_ne_top : volume K ≠ ⊤ := hbody.1.2.1.measure_lt_top.ne
      have hvis_pos : 0 < concreteMollifiedVisibility P ε x (unitCube (center q)) := by
        have h : (volume K).toReal > 0 := ENNReal.toReal_pos hK_pos.ne' hK_ne_top
        have h2 : concreteMollifiedVisibility P ε x (unitCube (center q)) =
            Real.rpow (volume K).toReal (-1 / 3 : ℝ) := by rfl
        rw [h2]
        exact Real.rpow_pos_of_pos h _
      have hbad_set : x ∈ concretePolynomialBadSet P ε (unitCube (center q)) (Cvis * (M q : ℝ)) := hvis_le
      have hdecomp := hdecomp_eq q hMq_pos
      have h_in_set : x ∈ {x | x ∈ concretePolynomialBadSet P ε (unitCube (center q)) (Cvis * (M q : ℝ)) ∧
          0 < concreteMollifiedVisibility P ε x (unitCube (center q))} :=
        ⟨hbad_set, hvis_pos⟩
      rw [hdecomp] at h_in_set
      rcases Set.mem_iUnion.mp h_in_set with ⟨r_sel, h1⟩
      rcases Set.mem_iUnion.mp h1 with ⟨θ, h2⟩
      have hx_layer : x ∈ concretePolynomialBadLayer P ε (unitCube (center q)) (Cvis * (M q : ℝ)) (r_sel : ℕ) := h2.1
      have hcolour : colour (selected q x) = θ := h2.2
      have hr_lt_levels : (r_sel : ℕ) < levels q := h_layer_bounded q x (r_sel : ℕ) hx_layer
      let r_fin : Fin (levels q) := ⟨(r_sel : ℕ), hr_lt_levels⟩
      let E := selected q x
      have hE_net : E ∈ net := (hselected_close q hMq_pos x hbad_set hvis_pos).1
      have hE_close : AreHomotheticallyCloseAt 0 α K (ellipsoidCarrier E) :=
        (hselected_close q hMq_pos x hbad_set hvis_pos).2
      have hE_center : E.1 = 0 := hcentered E hE_net
      have hK_sub : K ⊆ unitBall 3 := fun _ hx => hx.1
      have hE_outer : ellipsoidCarrier E ⊆ Metric.closedBall 0 R := by
        have h1 : ellipsoidCarrier E ⊆ dilateAbout 0 α K := hE_close.2
        have hα_pos' : 0 < α := by linarith
        have h2 : dilateAbout 0 α K ⊆ Metric.closedBall 0 α := by
          intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          have hz2 : z ∈ unitBall 3 := hK_sub hz
          have h3 : ‖z‖ ≤ 1 := by simpa [unitBall] using hz2
          have h4 : ‖(AffineMap.homothety 0 α) z‖ ≤ α := by
            have h5 : (AffineMap.homothety 0 α) z = α • z := by
              simp [AffineMap.homothety_apply]
            rw [h5]
            have h6 : ‖α • z‖ = |α| * ‖z‖ := by
              simpa [norm_smul, Real.norm_eq_abs] using norm_smul α z
            rw [h6, abs_of_pos hα_pos']
            calc α * ‖z‖ ≤ α * 1 := mul_le_mul_of_nonneg_left h3 hα_pos'.le
              _ = α := by ring
          simpa [Metric.mem_closedBall, dist_zero_right] using h4
        have hR : R = α := by rfl
        rw [hR]
        exact subset_trans h1 h2
      have h_eq : ellipsoidCarrier E = JohnEllipsoid.ellipsoid 0 E.2 := by
        have h1 : ellipsoidCarrier E = JohnEllipsoid.ellipsoid E.1 E.2 := by rfl
        rw [h1, hE_center]
      have hE_close' : AreHomotheticallyCloseAt 0 α K (JohnEllipsoid.ellipsoid 0 E.2) := by
        rw [h_eq] at hE_close
        exact hE_close
      have hvol_comp_raw := hVolumeComp α K E.2 (by linarith) hbody.1 hE_close'
      have hvol_comp : ENNReal.ofReal (α⁻¹ ^ 3) * volume K ≤ volume (ellipsoidCarrier E) := by
        rw [h_eq]
        exact hvol_comp_raw.1
      have hvol_lower : ENNReal.ofReal (volLower q (r_sel : ℕ)) ≤ volume (ellipsoidCarrier E) :=
        dyadic_ellipsoid_volume_lower_bound
          (hx := hx_layer)
          (hM := hCM_pos)
          (hbody := hbody.1)
          (hα := hα)
          (hcomp := hvol_comp)
      have hE_in_band : E ∈ band q (r_sel : ℕ) := ⟨hMq_pos, hE_net, hE_outer, hvol_lower⟩
      have hE_in_palette : E ∈ palette :=
        h_in_palette q (r_sel : ℕ) (Finset.mem_range.mpr hr_lt_levels) E hE_in_band
      -- Many-bisections contradiction
      have h_exists_nobisect : ∃ (j : ℕ), j < n' E (center q) ∧
          ¬PolynomialBisects (parameterPolynomial P x) (scaledEllipsoid E.2 η (z' E (center q) j)) := by
        by_contra h
        push Not at h
        have h_all_bisect : ∀ j < n' E (center q),
            PolynomialBisects (parameterPolynomial P x) (scaledEllipsoid E.2 η (z' E (center q) j)) := h
        rcases hPrincipalAxesRep E.2 with ⟨A', basis, lengths, hℓ_pos, hℓ_rep, hA'_eq⟩
        let ι := Fin (n E hE_in_palette (center q))
        have h_n_eq : n' E (center q) = n E hE_in_palette (center q) := by
          dsimp only [n']; rw [dif_pos hE_in_palette]
        let translates : ι → Point 3 := z E hE_in_palette (center q)
        have h_translates_eq : ∀ (j : ι), translates j = z' E (center q) (j : ℕ) := by
          intro j
          dsimp only [translates, z']
          rw [dif_pos hE_in_palette]
          have hj' : (j : ℕ) < n E hE_in_palette (center q) := j.isLt
          rw [dif_pos hj'] <;> rfl
        have h_scaled_eq : ∀ (p : Point 3), scaledEllipsoid A' η p = scaledEllipsoid E.2 η p :=
          scaledEllipsoid_eq_of_ellipsoid_eq hη_pos hA'_eq
        have h_cuts : ∀ y ∈ Metric.ball x ε, ∀ (j : ι),
            PolynomialCutsAtLeast (parameterPolynomial P y) (scaledEllipsoid A' η (translates j)) (2 / 5 : ℝ≥0∞) := by
          intro y hy j
          rw [h_scaled_eq (translates j)]
          have hE_in_finset : E ∈ paletteFinset := by
            exact (Set.Finite.mem_toFinset hpalette_finite).mpr hE_in_palette
          have h_region_in : scaledEllipsoid E.2 η (translates j) ∈ allRegionsFinset := by
            rw [h_translates_eq j]
            refine' Finset.mem_biUnion.mpr ⟨E, hE_in_finset, _⟩
            refine' Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, _⟩
            exact Finset.mem_image.mpr ⟨(j : ℕ), Finset.mem_range.mpr (by rw [h_n_eq]; exact j.isLt), rfl⟩
          let idx : RegionIdx := ⟨scaledEllipsoid E.2 η (translates j), h_region_in⟩
          have h_bisect_raw : PolynomialBisects (parameterPolynomial P x) (scaledEllipsoid E.2 η (z' E (center q) (j : ℕ))) :=
            h_all_bisect (j : ℕ) (by rw [h_n_eq]; exact j.isLt)
          have h_eq_region : scaledEllipsoid E.2 η (translates j) = scaledEllipsoid E.2 η (z' E (center q) (j : ℕ)) :=
            congr_arg (fun p : Point 3 => scaledEllipsoid E.2 η p) (h_translates_eq j)
          have h_bisect : PolynomialBisects (parameterPolynomial P x) (scaledEllipsoid E.2 η (translates j)) := by
            rw [h_eq_region]
            exact h_bisect_raw
          exact hStable x hx_norm y hy idx h_bisect
        let bVec : Fin 3 → Point 3 := basis.toBasis
        have hloc_int : ∀ (i : Fin 3), LocallyIntegrable (coefficientSurfaceFunctional P (bVec i) (unitCube (center q))) volume :=
          fun i => (hMollSurface k P (unitCube (center q)) (center q) ε hU_meas hU_sub hε_pos).1 (bVec i)
        have h_subset : ∀ (j : ι), scaledEllipsoid A' η (translates j) ⊆ unitCube (center q) := by
          intro j
          rw [h_scaled_eq (translates j)]
          exact hz_subset E hE_in_palette (center q) j
        have h_disjoint : Pairwise (fun (i j : ι) => Disjoint (scaledEllipsoid A' η (translates i)) (scaledEllipsoid A' η (translates j))) := by
          intro i j hne
          rw [h_scaled_eq (translates i), h_scaled_eq (translates j)]
          exact hz_disjoint E hE_in_palette (center q) hne
        have h_mb_raw := hManyBisects k P (unitCube (center q)) (center q) ε x ι A' η translates basis lengths
          hU_meas hU_sub hε_pos hloc_int hη_pos hη_le_one hℓ_pos hℓ_rep h_subset h_disjoint h_cuts
        have h_close_A' : AreHomotheticallyCloseAt 0 α K (JohnEllipsoid.ellipsoid 0 A') := by
          rw [hA'_eq]
          exact hE_close'
        have h_budget : ∀ i : Fin 3, lengths i * concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q)) ≤ α :=
          hDirectionalBudget k P (unitCube (center q)) ε x α A' basis lengths (by linarith) (fun i => by linarith [hℓ_pos i]) hℓ_rep h_close_A'
        have h_budget_ennreal : ∀ i : Fin 3,
            ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) ≤ ENNReal.ofReal α := by
          intro i
          have h1 : 0 ≤ lengths i := by linarith [hℓ_pos i]
          have h3 : lengths i * concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q)) ≤ α := h_budget i
          have h4 : ENNReal.ofReal (lengths i * concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) ≤ ENNReal.ofReal α :=
            ENNReal.ofReal_le_ofReal h3
          have h5 : ENNReal.ofReal (lengths i * concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) =
              ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) := by
            rw [← ENNReal.ofReal_mul h1] <;> rfl
          rw [h5] at h4; exact h4
        have h_sum : ∑ i : Fin 3, ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) ≤
            (3 : ℝ≥0∞) * ENNReal.ofReal α := by
          calc
            _ ≤ ∑ i : Fin 3, ENNReal.ofReal α := Finset.sum_le_sum (fun i _ => h_budget_ennreal i)
            _ = (3 : ℝ≥0∞) * ENNReal.ofReal α := by simp [Finset.sum_const, Finset.card_fin] <;> ring
        have h_sum2 : (C_mb : ℝ≥0∞) * ∑ i : Fin 3, ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) ≤
            (C_mb : ℝ≥0∞) * ((3 : ℝ≥0∞) * ENNReal.ofReal α) :=
          mul_le_mul_left' h_sum (C_mb : ℝ≥0∞)
        have h_eq_sum : ∑ i : Fin 3, ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (bVec i) (unitCube (center q))) =
            ∑ i : Fin 3, ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (basis i) (unitCube (center q))) := by
          apply Finset.sum_congr rfl
          intro i _
          have h : bVec i = basis i := by
            simp [bVec] <;> rfl
          rw [h]
        have h_sum2' : (C_mb : ℝ≥0∞) * ∑ i : Fin 3, ENNReal.ofReal (lengths i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (basis i) (unitCube (center q))) ≤
            (C_mb : ℝ≥0∞) * 3 * ENNReal.ofReal α := by
          rw [←h_eq_sum]
          have h_assoc : (C_mb : ℝ≥0∞) * ((3 : ℝ≥0∞) * ENNReal.ofReal α) = (C_mb : ℝ≥0∞) * 3 * ENNReal.ofReal α := by
            rw [mul_assoc]
          rw [h_assoc] at h_sum2
          exact h_sum2
        have h_upper : ManyBisectsUpperBound (Fintype.card ι) η (∏ i, lengths i) C_mb α :=
          le_trans h_mb_raw h_sum2'
        have hprod_pos : 0 < ∏ i : Fin 3, lengths i := Finset.prod_pos (fun i _ => hℓ_pos i)
        have h_vol_formula : volume (scaledEllipsoid A' η 0) = ENNReal.ofReal (η ^ 3 * ∏ i, lengths i) * volume (unitBall 3) :=
          volume_scaledEllipsoid_determinant A' basis lengths hℓ_pos hℓ_rep η hη_pos 0
        have h_pack : volume (unitCube (center q)) / volume (scaledEllipsoid A' η 0) ≤ (C_pack : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) := by
          have h_eq_vol : volume (scaledEllipsoid A' η 0) = volume (scaledEllipsoid E.2 η 0) := by
            rw [h_scaled_eq 0]
          rw [h_eq_vol]
          simpa [ι] using hz_lower E hE_in_palette (center q)
        have hη_small' : ENNReal.ofReal η < manyBisectsThreshold C_mb C_pack α (unitCube (center q)) :=
          eta_small_manyBisects C_mb C_pack α (center q) sphereArea denom threshold rfl rfl rfl η hη_small
        exact many_bisects_contradiction (Fintype.card ι) η (∏ i, lengths i) C_mb C_pack α (unitCube (center q)) A'
          hη_pos hprod_pos (by linarith) hC_mb_pos hC_pack_pos h_upper h_vol_formula h_pack hη_small'
      rcases h_exists_nobisect with ⟨j, hj_lt, h_nobisect⟩
      let θ' := colour E
      have hθ_eq : θ' = θ := hcolour
      have hE_in_bandColour : E ∈ bandColour q (r_sel : ℕ) θ' := ⟨hE_in_band, rfl⟩
      let bfinset := (hbandColour_finite q (r_sel : ℕ) θ').toFinset
      have hE_in_bfinset : E ∈ bfinset := by
        exact (hbandColour_finite q (r_sel : ℕ) θ').mem_toFinset.mpr hE_in_bandColour
      have h_nonempty : (bandColour q (r_sel : ℕ) θ').Nonempty := ⟨E, hE_in_bandColour⟩
      have h_j_le : n' E (center q) ≤ maxTranslates q r_fin θ' := by
        dsimp only [maxTranslates]
        rw [dif_pos h_nonempty]
        let Evar : {E // E ∈ (hbandColour_finite q (r_sel : ℕ) θ').toFinset} := ⟨E, hE_in_bfinset⟩
        have hEvar : Evar ∈ (hbandColour_finite q (r_sel : ℕ) θ').toFinset.attach := by
          simpa [Finset.mem_attach] using hE_in_bfinset
        exact Finset.le_sup (f := fun (x : {E // E ∈ (hbandColour_finite q (r_sel : ℕ) θ').toFinset}) => n' x.val (center q)) hEvar
      have hj_max : j < maxTranslates q r_fin θ' := lt_of_lt_of_le hj_lt h_j_le
      let j_atom : Atom q r_fin θ' := ⟨j, hj_max⟩
      let i : I := ⟨q, ⟨r_fin, ⟨θ', j_atom⟩⟩⟩
      have h_i1 : i.1 = q := by rfl
      have h_i221 : i.2.2.1 = θ' := by rfl
      have h_i222 : (i.2.2.2 : ℕ) = j := by rfl
      have h_sel : selected i.1 x = E := by
        rw [h_i1] <;> exact hselected
      have h_colour' : colour (selected i.1 x) = i.2.2.1 := by
        exact hcolour.trans hθ_eq.symm
      have h_jlt' : (i.2.2.2 : ℕ) < n' (selected i.1 x) (center i.1) := by
        rw [h_i222, h_sel, h_i1] <;> exact hj_lt
      have h_nobisect' : ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion i x) := by
        have h_eq : selectedRegion i x = scaledEllipsoid E.2 η (z' E (center q) j) := by
          dsimp only [selectedRegion, i]
          <;> rfl
        rw [h_eq]
        exact h_nobisect
      have hx_D : x ∈ D i := by
        simp only [D, Set.mem_setOf_eq]
        exact ⟨hx_norm, hx_layer, h_colour', h_jlt', h_nobisect'⟩
      have hsign : x ∈ positiveSignClass P (selectedRegion i) (D i) ∨
          x ∈ (fun x => -x) '' positiveSignClass P (selectedRegion i) (D i) :=
        nonbisected_in_sign_class_cover (hD_antipodal_all i) (hRegion_antipodal_all i)
          (hRegion_meas_all i) (hRegion_finite_all i) (hPoly_nonzero_all i)
          hx_D h_nobisect'
      exact Set.mem_iUnion.mpr ⟨i, by cases hsign with | inl h => exact Or.inl h | inr h => exact Or.inr h⟩
  -- Step 10: Prove antipodal separation for each atom
  -- ============================================================
  have hsep : ∀ i : I,
      positiveSignClass P (selectedRegion i) (D i) ∩
        closure ((fun x => -x) '' positiveSignClass P (selectedRegion i) (D i)) = ∅ := by
    intro i
    apply hSignSep k P (selectedRegion i) (D i)
    · -- D is antipodal
      intro x hx
      have hx_norm2 : x ∈ normalizedPolynomialParameters P := hx.1
      have hneg_norm : -x ∈ normalizedPolynomialParameters P := by
        simpa [normalizedPolynomialParameters, Metric.mem_sphere] using hx_norm2
      have hvis_even : concreteMollifiedVisibility P ε (-x) (unitCube (center i.1)) =
          concreteMollifiedVisibility P ε x (unitCube (center i.1)) := by
        have hbody := concreteMollifiedVisibilityBody_even P ε hε_pos (unitCube (center i.1)) x
        rw [concreteMollifiedVisibility, concreteMollifiedVisibility, hbody]
      have hlayer : x ∈ concretePolynomialBadLayer P ε (unitCube (center i.1))
          (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) := hx.2.1
      have hneg_layer : -x ∈ concretePolynomialBadLayer P ε (unitCube (center i.1))
          (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) := by
        simpa [concretePolynomialBadLayer, hvis_even] using hlayer
      have hsel_even : selected i.1 (-x) = selected i.1 x := by
        by_cases hM : 0 < (M i.1 : ℝ)
        · exact hselected_even i.1 hM x
        · have h1 : selected i.1 = fun _ => (0, 1) := by
            funext y
            unfold selected
            rw [dif_neg hM]
          rw [h1] <;> rfl
      have hbisect_even : ∀ (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3)),
          PolynomialBisects (-p) s ↔ PolynomialBisects p s := by
        intro p s
        have h1 : {y : Point 3 | polynomialValue (-p) y < 0} = {y | 0 < polynomialValue p y} := by
          ext y; simp [polynomialValue_neg] <;> linarith
        have h2 : {y : Point 3 | 0 < polynomialValue (-p) y} = {y | polynomialValue p y < 0} := by
          ext y; simp [polynomialValue_neg] <;> linarith
        simp only [PolynomialBisects, h1, h2]
        exact ⟨Eq.symm, Eq.symm⟩
      have hreg : selectedRegion i (-x) = selectedRegion i x := by
        simp [selectedRegion, hsel_even]
      exact ⟨hneg_norm, hneg_layer, by rw [hsel_even]; exact hx.2.2.1,
        by rw [hsel_even]; exact hx.2.2.2.1,
        by
          have hnb : ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion i x) := hx.2.2.2.2
          have hpoly : parameterPolynomial P (-x) = -parameterPolynomial P x := parameterPolynomial_neg P x
          have h : PolynomialBisects (parameterPolynomial P (-x)) (selectedRegion i (-x)) ↔
              PolynomialBisects (parameterPolynomial P x) (selectedRegion i x) := by
            rw [hpoly, hreg]
            exact hbisect_even (parameterPolynomial P x) (selectedRegion i x)
          exact h.not.mpr hnb⟩
    · -- selectedRegion is antipodal
      intro x hx
      have hsel_even : selected i.1 (-x) = selected i.1 x := by
        by_cases hM : 0 < (M i.1 : ℝ)
        · exact hselected_even i.1 hM x
        · have h1 : selected i.1 = fun _ => (0, 1) := by
            funext y
            unfold selected
            rw [dif_neg hM]
          rw [h1]
          <;> rfl
      simp [selectedRegion, hsel_even]
    · -- selectedRegion is measurable
      intro x hx
      let E := selected i.1 x
      have hcompact : IsCompact (selectedRegion i x) := by
        have h1 : IsCompact (Metric.closedBall (0 : Point 3) η) := isCompact_closedBall _ _
        have h2 : IsCompact (E.2 '' Metric.closedBall (0 : Point 3) η) :=
          h1.image E.2.toContinuousLinearEquiv.continuous
        have h_eq1 : selectedRegion i x = scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) := by rfl
        let f : Point 3 → Point 3 := fun y => z' E (center i.1) (i.2.2.2 : ℕ) + y
        have hf : Continuous f := continuous_const_add _
        have h3 : scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) = f '' (E.2 '' Metric.closedBall (0 : Point 3) η) := by
          unfold scaledEllipsoid <;> rfl
        rw [h_eq1, h3]
        exact h2.image hf
      exact hcompact.isClosed.measurableSet
    · -- selectedRegion has finite volume
      intro x hx
      let E := selected i.1 x
      have h : selectedRegion i x = scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) := by rfl
      rw [h]
      have hcompact : IsCompact (scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ))) := by
        have h1 : IsCompact (Metric.closedBall (0 : Point 3) η) := isCompact_closedBall _ _
        have h2 : IsCompact (E.2 '' Metric.closedBall (0 : Point 3) η) :=
          h1.image E.2.toContinuousLinearEquiv.continuous
        let f : Point 3 → Point 3 := fun y => z' E (center i.1) (i.2.2.2 : ℕ) + y
        have hf : Continuous f := continuous_const_add _
        have h3 : scaledEllipsoid E.2 η (z' E (center i.1) (i.2.2.2 : ℕ)) = f '' (E.2 '' Metric.closedBall (0 : Point 3) η) := by
          unfold scaledEllipsoid <;> rfl
        rw [h3]
        exact h2.image hf
      exact hcompact.isBounded.measure_lt_top
    · -- parameterPolynomial P x ≠ 0 for x ∈ D
      intro x hx
      exact parameterPolynomial_ne_zero_of_normalized hx.1
    · -- ¬PolynomialBisects for x ∈ D
      intro x hx
      exact hx.2.2.2.2
    · -- sequential local constancy via hSelectionStability + hCont
      intro xseq x hxseq_in_D hx_in_D hxseq_tendsto
      have hM_pos : 0 < (M i.1 : ℝ) := by
        by_contra h
        have hM_nonpos : (M i.1 : ℝ) ≤ 0 := by linarith
        have h_empty : concretePolynomialBadLayer P ε (unitCube (center i.1))
            (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) = ∅ :=
          badLayer_empty_when_M_nonpos (show Cvis * (M i.1 : ℝ) ≤ 0 from
            mul_nonpos_of_nonneg_of_nonpos (by linarith) hM_nonpos)
        have h_x_in_layer : x ∈ concretePolynomialBadLayer P ε (unitCube (center i.1))
            (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) := hx_in_D.2.1
        rw [h_empty] at h_x_in_layer
        exact h_x_in_layer
      have h_layer_sub_bad : ∀ (y : CoefficientSpace P.dim),
          y ∈ concretePolynomialBadLayer P ε (unitCube (center i.1))
            (Cvis * (M i.1 : ℝ)) (i.2.1 : ℕ) →
          y ∈ concretePolynomialBadSet P ε (unitCube (center i.1)) (Cvis * (M i.1 : ℝ)) := by
        intro y hy
        have hle1 : concreteMollifiedVisibility P ε y (unitCube (center i.1)) ≤
            Real.rpow 2 (-(i.2.1 : ℝ)) * (Cvis * (M i.1 : ℝ)) := hy.2
        have hle2 : Real.rpow 2 (-(i.2.1 : ℝ)) * (Cvis * (M i.1 : ℝ)) ≤
            Cvis * (M i.1 : ℝ) := by
          have h : Real.rpow 2 (-(i.2.1 : ℝ)) ≤ 1 := by
            have h6 : -(i.2.1 : ℝ) ≤ 0 := by
              have h7 : (i.2.1 : ℝ) ≥ 0 := by positivity
              linarith
            exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) h6
          have hpos : 0 ≤ Cvis * (M i.1 : ℝ) := by positivity
          nlinarith
        exact le_trans hle1 hle2
      have h_close' : ∀ y ∈ D i, AreHomotheticallyCloseAt 0 α
          (concreteMollifiedVisibilityBody P ε y (unitCube (center i.1)))
          (ellipsoidCarrier (selected i.1 y)) := by
        intro y hy
        have hbad : y ∈ concretePolynomialBadSet P ε (unitCube (center i.1))
            (Cvis * (M i.1 : ℝ)) := h_layer_sub_bad y hy.2.1
        have hvis_pos : 0 < concreteMollifiedVisibility P ε y (unitCube (center i.1)) := by
          have hlower : Real.rpow 2 (-(i.2.1 : ℝ) - 1) * (Cvis * (M i.1 : ℝ)) <
              concreteMollifiedVisibility P ε y (unitCube (center i.1)) := hy.2.1.1
          have hCM_pos : 0 < Cvis * (M i.1 : ℝ) := mul_pos hCvis_pos hM_pos
          have h_rpow_pos : 0 < Real.rpow 2 (-(i.2.1 : ℝ) - 1) :=
            Real.rpow_pos_of_pos (by norm_num) _
          have hpos : 0 < Real.rpow 2 (-(i.2.1 : ℝ) - 1) * (Cvis * (M i.1 : ℝ)) :=
            mul_pos h_rpow_pos hCM_pos
          exact lt_trans hpos hlower
        exact (hselected_close i.1 hM_pos y hbad hvis_pos).2
      have h_colour' : ∀ y ∈ D i, colour (selected i.1 y) = i.2.2.1 := by
        intro y hy
        exact hy.2.2.1
      have h_selected_in_net' : ∀ y ∈ D i, selected i.1 y ∈ net := by
        intro y hy
        have hbad : y ∈ concretePolynomialBadSet P ε (unitCube (center i.1))
            (Cvis * (M i.1 : ℝ)) := h_layer_sub_bad y hy.2.1
        have hvis_pos : 0 < concreteMollifiedVisibility P ε y (unitCube (center i.1)) := by
          have hlower : Real.rpow 2 (-(i.2.1 : ℝ) - 1) * (Cvis * (M i.1 : ℝ)) <
              concreteMollifiedVisibility P ε y (unitCube (center i.1)) := hy.2.1.1
          have hCM_pos : 0 < Cvis * (M i.1 : ℝ) := mul_pos hCvis_pos hM_pos
          have h_rpow_pos : 0 < Real.rpow 2 (-(i.2.1 : ℝ) - 1) :=
            Real.rpow_pos_of_pos (by norm_num) _
          have hpos : 0 < Real.rpow 2 (-(i.2.1 : ℝ) - 1) * (Cvis * (M i.1 : ℝ)) :=
            mul_pos h_rpow_pos hCM_pos
          exact lt_trans hpos hlower
        exact (hselected_close i.1 hM_pos y hbad hvis_pos).1
      have h_ellipsoid_const : ∀ᶠ m in Filter.atTop,
          selected i.1 (xseq m) = selected i.1 x :=
        selected_ellipsoid_locally_constant
          hα hCont hSelectionStability
          h_close' h_colour' h_selected_in_net' hseparation'
          (unitCube_measurableSet (center i.1))
          (unitCube_subset_closedBall (center i.1))
          hε_pos
          xseq x hxseq_in_D hx_in_D hxseq_tendsto
      filter_upwards [h_ellipsoid_const] with m h_eq
      have h1 : selectedRegion i (xseq m) = selectedRegion i x := by
        simp [selectedRegion, h_eq]
      exact h1

  -- ============================================================
  -- Step 11: Cardinality bound
  -- ============================================================
  have hcard_atom : ∀ q (r : Fin (levels q)) (θ : Fin N),
      (Fintype.card (Atom q r θ) : ℝ≥0) ≤
        (1 / 8 : ℝ≥0) ^ (r : ℕ) * M q ^ 3 := by
    intro q r θ
    let Bound : ℝ≥0 := (1 / 8 : ℝ≥0) ^ (r : ℕ) * M q ^ 3
    have h_main : ∀ E ∈ bandColour q (r : ℕ) θ,
        (n' E (center q) : ℝ≥0) ≤ Bound := by
      intro E hE
      have hM : 0 < (M q : ℝ) := hE.1.1
      have hvolLower_pos : 0 < volLower q (r : ℕ) := by
        dsimp only [volLower]
        positivity
      have hE_band : E ∈ band q (r : ℕ) := hE.1
      have hr_in : (r : ℕ) ∈ Finset.range (levels q) :=
        Finset.mem_range.mpr r.isLt
      have hE_in_palette : E ∈ palette :=
        h_in_palette q (r : ℕ) hr_in E hE_band
      have hE_center : E.1 = 0 := hpalette_centered E hE_in_palette
      have hEllip_lower :
          volume (ellipsoidCarrier E) ≥ ENNReal.ofReal (volLower q (r : ℕ)) :=
        hE_band.2.2.2
      have hPack_bound : (n' E (center q) : ℝ≥0∞) ≤
          (C_pack : ℝ≥0∞) * volume (unitCube (center q)) /
            volume (scaledEllipsoid E.2 η 0) := by
        dsimp only [n']
        rw [dif_pos hE_in_palette]
        exact hz_upper E hE_in_palette (center q)
      exact @single_translate_bound (r := (r : ℕ)) (Mq := M q)
        hM C_pack hC_pack_pos α hα η hη_pos Cvis hCvis_pos rfl
        E hE_center (volLower q (r : ℕ)) hvolLower_pos rfl
        hEllip_lower (center q) (n' E (center q)) hPack_bound
    dsimp only [Atom, maxTranslates]
    exact card_fin_finite_set_sup_le
      (bandColour q (r : ℕ) θ)
      (hbandColour_finite q (r : ℕ) θ)
      (fun E : EllipsoidParameter => n' E (center q))
      (Classical.propDecidable (bandColour q (r : ℕ) θ).Nonempty)
      h_main
  let D_sum : ℝ≥0 := ∑ q, M q ^ 3
  have htotal_card : (Fintype.card I : ℝ≥0) ≤
      (Fintype.card (Fin N) : ℝ≥0) * ((8 : ℝ≥0) / 7) * D_sum :=
    hAtomCard Cube (Fin N) levels Atom M D_sum hcard_atom (by dsimp only [D_sum]; exact le_rfl)
  have hdim_margin' : (Fintype.card I : ℝ) < (P.dim : ℝ) :=
    dimension_margin_implies_card_lt_dim Ccount rfl htotal_card hDimMargin

  have hcard_le : Fintype.card I ≤ P.dim - 1 := by
    have h : Fintype.card I < P.dim :=
      (Nat.cast_lt (α := ℝ)).mp hdim_margin'
    exact Nat.le_sub_one_of_lt h

  -- ============================================================
  -- Step 12: Transport to sphere and apply Borsuk-Ulam
  -- ============================================================
  rcases hNormSphere k P hPdim_pos with ⟨h, hantipodal⟩

  let A_sphere (i : I) : Set (TopCat.sphere (P.dim - 1)) :=
    h '' {x : normalizedPolynomialParameters P | (x : CoefficientSpace P.dim) ∈ positiveSignClass P (selectedRegion i) (D i)}

  let bad_sphere : Set (TopCat.sphere (P.dim - 1)) :=
    h '' {x : normalizedPolynomialParameters P | (x : CoefficientSpace P.dim) ∈ bad}

  have hsep_sphere : ∀ i : I,
      A_sphere i ∩ closure (TopCat.sphereAntipodal (P.dim - 1) '' A_sphere i) = ∅ := by
    intro i
    exact sphere_separation_from_ambient (selectedRegion i) (D i)
      (fun x hx => hx.1) h hantipodal (hsep i)

  have hcover_sphere : bad_sphere ⊆
      ⋃ i : I, (A_sphere i ∪ TopCat.sphereAntipodal (P.dim - 1) '' A_sphere i) := by
    exact sphere_cover_from_ambient selectedRegion D
      (fun i x hx => hx.1) bad h hantipodal hcover

  rcases hBadSetCover (P.dim - 1) I hcard_le A_sphere bad_sphere
      hsep_sphere hcover_sphere with ⟨x_sphere, hx_not_bad⟩

  let x : CoefficientSpace P.dim := (h.symm x_sphere).1

  have hx_norm : x ∈ normalizedPolynomialParameters P :=
    (h.symm x_sphere).2

  have hx_not_bad_set : x ∉ bad := by
    intro hx
    let x' : normalizedPolynomialParameters P := ⟨x, hx_norm⟩
    have h_eq : h x' = x_sphere := h.apply_symm_apply x_sphere
    have h1 : x_sphere ∈ bad_sphere := by
      rw [←h_eq]
      exact ⟨x', hx, rfl⟩
    exact hx_not_bad h1

  have hmain : ∀ q, Cvis * (M q : ℝ) <
      concreteMollifiedVisibility P ε x (unitCube (center q)) := by
    intro q
    by_contra h
    have h' : concreteMollifiedVisibility P ε x (unitCube (center q)) ≤ Cvis * (M q : ℝ) :=
      not_lt.mp h
    have hx_bad : x ∈ bad := by
      refine' ⟨hx_norm, q, h'⟩
    exact hx_not_bad_set hx_bad

  exact ⟨ε, x, hε_pos, hx_norm, hmain⟩

end Kakeya.CV
