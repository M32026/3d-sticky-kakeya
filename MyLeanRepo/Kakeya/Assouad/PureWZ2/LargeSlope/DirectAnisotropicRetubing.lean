import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectSection6SourceInterface
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHorizontalPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperShadingOpenTop
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperAxisCenterBound

/-!
# Direct triangular retubing for Proposition 6.5

This is the first geometric output after the paper's mass-popular interval
and spatial box.  It applies the exact triangular map to the actual Node-5
source, removes only the null upper face, and cubicalizes at a reciprocal-grid
target scale.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Delete the null upper face before mapping the direct source interval to
the half-open target height window. -/
def PureWZ2DirectHorizontalPopularBoxData.openSourceShading
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :
    WZ1PaperTubeShading data.family :=
  paperShadingRemoveTopFace data.sourceShading source.d

@[simp] theorem PureWZ2DirectHorizontalPopularBoxData.openSourceShading_mass
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :
    data.openSourceShading.mass = data.sourceShading.mass :=
  paperShadingRemoveTopFace_mass data.sourceShading source.d

/-- Source local grains restricted only by the null top-face deletion. -/
def PureWZ2DirectHorizontalPopularBoxData.openSourceLocalGrains
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :
    PureWZ2LocalGrainData data.openSourceShading sigma
      (Kakeya.realRpowENN delta (-inputLoss)) :=
  data.sourceLocalGrains.restrict (fun _ => diff_subset)

/-- Source global grains restricted only by the null top-face deletion. -/
def PureWZ2DirectHorizontalPopularBoxData.openSourceGlobalGrains
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :
    PureWZ2C2GlobalGrainData data.openSourceShading sigma
      (Kakeya.realRpowENN delta (-inputLoss)) :=
  data.sourceGlobalGrains.restrict_same_constant (fun _ => diff_subset)

/-- Common center: horizontal coordinates come from the popular spatial box
and height is the midpoint of the paper's selected hundredth interval. -/
def pureWZ2DirectAnisotropicCenter
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) : Point3 :=
  point3 (data.popular.center 0) (data.popular.center 1)
    (source.c + (source.d - source.c) / 2)

/-- Global smooth witness for the affine shear.  The map reads only its
midpoint value; the transported public slope remains interval-local and may
have a nonzero intercept. -/
def pureWZ2DirectGeometrySlope
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) : SlopeFunction :=
  source.geometrySlope

/-- The complete direct exact-triangular retubing package. -/
structure PureWZ2DirectAnisotropicRetubingData
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) where
  popular : PureWZ2DirectHorizontalPopularBoxData assembly.horizontalSource
  raw : PureWZ2AnisotropicPaperRetubingData
    (targetDelta := anisotropicPaperAlignedScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d)
    popular.family popular.openSourceShading
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    (pureWZ2DirectAnisotropicCenter popular)
    assembly.horizontalSource.ordered
    assembly.horizontalSource.slopeScale_pos

/-- Construct the paper-faithful exact triangular image of the direct source. -/
theorem PureWZ2DirectSection6SourceAssembly.toDirectAnisotropicRetubing
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    Nonempty (PureWZ2DirectAnisotropicRetubingData assembly) := by
  let source := assembly.horizontalSource
  rcases source.toDirectPopularBox with ⟨popular⟩
  let sourceFamily := popular.family
  let sourceShading := popular.openSourceShading
  let g := pureWZ2DirectGeometrySlope source
  let c := source.c
  let d := source.d
  let m := source.m
  let center := pureWZ2DirectAnisotropicCenter popular
  let targetDelta := anisotropicPaperAlignedScale delta c d
  let count := anisotropicPaperAlignedCount delta c d
  let S : ℝ := 2 / (d - c)
  have hlength : d - c = assembly.rho.1 / 100 := by
    dsimp only [c, d, source]
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
  have hcd : c < d := source.ordered
  have hlengthPos : 0 < d - c := sub_pos.mpr hcd
  have hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨source.left_mem.trans hz.1,
      hz.2.trans source.right_mem⟩
  have hmidMem : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    hsub ⟨by linarith, by linarith⟩
  have hg : g.IsNormalized := by
    simpa [g, pureWZ2DirectGeometrySlope, source] using
      source.geometrySlope_normalized
  have hdc : d - c ≤ 1 / 25 := by
    rw [hlength]
    linarith [assembly.rho_tiny]
  have hrawPos : 0 < anisotropicPaperRawScale delta c d := by
    unfold anisotropicPaperRawScale
    exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
      hlengthPos
  have hrawEq : anisotropicPaperRawScale delta c d =
      1600 * delta / assembly.rho.1 := by
    unfold anisotropicPaperRawScale
    rw [hlength]
    field_simp [show assembly.rho.1 ≠ 0 by
      exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
        assembly.rho.2.1)]
    ring
  have hrawHalf : anisotropicPaperRawScale delta c d ≤ 1 / 2 := by
    rw [hrawEq, div_le_iff₀
      (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
    have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
      linarith [assembly.rho_tiny]
    nlinarith [assembly.delta_le_rho_sq,
      mul_nonneg
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
        hfactor]
  have htargetPos : 0 < targetDelta :=
    anisotropicPaperAlignedScale_pos hrawPos hrawHalf
  have hrawTarget : anisotropicPaperRawScale delta c d ≤ targetDelta :=
    anisotropicPaperRawScale_le_aligned hrawPos hrawHalf
  have hradius : S * (18 * delta) + 2 * targetDelta ≤
      6 * targetDelta := by
    have hsource : S * (18 * delta) =
        (9 / 4 : ℝ) * anisotropicPaperRawScale delta c d := by
      dsimp only [S]
      unfold anisotropicPaperRawScale
      field_simp [hlengthPos.ne']
      ring
    rw [hsource]
    nlinarith
  have hcountPos : 0 < count :=
    anisotropicPaperAlignedCount_pos hrawPos hrawHalf
  have halign : targetDelta * (count : ℝ) = 1 :=
    anisotropicPaperAlignedScale_mul_count hrawPos hrawHalf
  have hcenterTwo : center 2 = c + (d - c) / 2 := by
    simp [center, c, d, pureWZ2DirectAnisotropicCenter, point3]
  have hsourceLine : WZ1PaperIsLineClass sourceFamily := popular.line_class
  have hsourceSlab : ∀ index, popular.sourceShading.carrier index ⊆
      horizontalSlab c d := by
    intro index point hpoint
    rw [popular.source_carrier_eq] at hpoint
    rw [popular.popular.restricted_carrier] at hpoint
    exact source.source_in_interval _ hpoint.1
  have hsourceWindow : ∀ index point,
      point ∈ sourceShading.carrier index →
        |point 0 - center 0| ≤ 1 / 16 ∧
        |point 1 - center 1| ≤ 1 / 16 ∧
        c ≤ point 2 ∧ point 2 < d := by
    intro index point hpoint
    have hclosed : point ∈ popular.sourceShading.carrier index := hpoint.1
    have hpopular := hclosed
    rw [popular.source_carrier_eq, popular.popular.restricted_carrier] at hpopular
    have hbox := hpopular.2
    rw [popular.popular.box_eq] at hbox
    have hz := paperShadingRemoveTopFace_height hsourceSlab index hpoint
    refine ⟨?_, ?_, hz⟩
    · convert hbox.1 (0 : Fin 3) using 1 <;>
        simp [center, pureWZ2DirectAnisotropicCenter, point3, wz1AxisBox] <;>
        norm_num
    · convert hbox.1 (1 : Fin 3) using 1 <;>
        simp [center, pureWZ2DirectAnisotropicCenter, point3, wz1AxisBox] <;>
        norm_num
  have hcenterY : |center 1| ≤ 1 := by
    simpa [center, pureWZ2DirectAnisotropicCenter, point3]
      using popular.popular.center_mem (1 : Fin 3)
  have haxisSmall : ∀ index coordinate,
      |(wz1PaperAxisPointAtHeight (sourceFamily.tube index)
          (c + (d - c) / 2) - center) coordinate| ≤ 1 / 15 := by
    intro index coordinate
    rcases popular.source_carrier_nonempty index with ⟨point, hpoint⟩
    have hpopular := hpoint
    rw [popular.source_carrier_eq, popular.popular.restricted_carrier] at hpopular
    have hbox := hpopular.2
    rw [popular.popular.box_eq] at hbox
    let halfWidth := point3 (1 / 16) (1 / 16) ((d - c) / 2)
    have hpointBox : point ∈ wz1AxisBox center halfWidth := by
      intro coord
      fin_cases coord
      · convert hbox.1 (0 : Fin 3) using 1 <;>
          simp [center, halfWidth, pureWZ2DirectAnisotropicCenter,
            point3, wz1AxisBox] <;> norm_num
      · convert hbox.1 (1 : Fin 3) using 1 <;>
          simp [center, halfWidth, pureWZ2DirectAnisotropicCenter,
            point3, wz1AxisBox] <;> norm_num
      · have hz := hsourceSlab index hpoint
        rw [abs_le]
        constructor <;>
          simp [center, halfWidth, pureWZ2DirectAnisotropicCenter, point3] <;>
          linarith [hz.1, hz.2]
    have hheight : |center 2 - point 2| ≤ halfWidth 2 := by
      simpa [abs_sub_comm] using hpointBox (2 : Fin 3)
    have hbound := pureWZ2_paperAxis_center_coordinate_bound
      assembly.cfg.extremal.delta_pos (hsourceLine index) center halfWidth point
      (popular.sourceShading.subset_body index hpoint) hpointBox hheight
        coordinate
    have hlenTiny : d - c ≤ 1 / 640000 := by
      rw [hlength]
      linarith [assembly.rho_tiny]
    have hdeltaTiny : delta ≤ 1 / 40960000 := by
      have hrhoNonneg : 0 ≤ assembly.rho.1 :=
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
      have hrhoSquare : assembly.rho.1 ^ 2 ≤ (1 / 6400 : ℝ) ^ 2 := by
        exact (sq_le_sq₀ hrhoNonneg (by norm_num)).2 assembly.rho_tiny
      calc
        delta ≤ assembly.rho.1 ^ 2 := assembly.delta_le_rho_sq
        _ ≤ (1 / 6400 : ℝ) ^ 2 := hrhoSquare
        _ = 1 / 40960000 := by norm_num
    have hbudget : 2 * ((d - c) / 2) + 18 * delta + 1 / 16 ≤
        (1 / 15 : ℝ) := by
      nlinarith
    have hhalfCoord : halfWidth coordinate ≤ 1 / 16 := by
      fin_cases coordinate <;> simp [halfWidth, point3] <;> linarith
    have hbudget' : 2 * halfWidth 2 + 18 * delta +
        halfWidth coordinate ≤ 1 / 15 := by
      calc
        2 * halfWidth 2 + 18 * delta + halfWidth coordinate ≤
            2 * ((d - c) / 2) + 18 * delta + 1 / 16 := by
          simp only [halfWidth, point3_coord2]
          gcongr
        _ ≤ 1 / 15 := hbudget
    rw [hcenterTwo] at hbound
    exact hbound.trans hbudget'
  have hmidEq : c + (d - c) / 2 = center 2 := hcenterTwo.symm
  have hzeroX : ∀ index,
      |anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 0| ≤ 1 / 3 := by
    intro index
    have hx := haxisSmall index 0
    have hy := haxisSmall index 1
    have hcoord : anisotropicPaperTargetCenter g c d m center
          (sourceFamily.tube index) 0 =
        (wz1PaperAxisPointAtHeight (sourceFamily.tube index)
            (c + (d - c) / 2) - center) 0 +
          g (c + (d - c) / 2) *
            (wz1PaperAxisPointAtHeight (sourceFamily.tube index)
              (c + (d - c) / 2) - center) 1 := by
      simp [anisotropicPaperTargetCenter, anisotropicCenteredRescalingMap,
        anisotropicRescalingMap, point3]
      ring_nf
    rw [hcoord]
    have hgmid := (hg _ hmidMem).1
    calc
      |_ + _| ≤ |(wz1PaperAxisPointAtHeight (sourceFamily.tube index)
            (c + (d - c) / 2) - center) 0| +
          |g (c + (d - c) / 2)| *
            |(wz1PaperAxisPointAtHeight (sourceFamily.tube index)
              (c + (d - c) / 2) - center) 1| := by
        simpa [abs_mul] using abs_add_le
          ((wz1PaperAxisPointAtHeight (sourceFamily.tube index)
            (c + (d - c) / 2) - center) 0)
          (g (c + (d - c) / 2) *
            (wz1PaperAxisPointAtHeight (sourceFamily.tube index)
              (c + (d - c) / 2) - center) 1)
      _ ≤ 1 / 15 + 1 * (1 / 15) := by gcongr
      _ ≤ 1 / 3 := by norm_num
  have hzeroY : ∀ index,
      |anisotropicPaperTargetCenter g c d m center
        (sourceFamily.tube index) 1| ≤ 1 / 3 := by
    intro index
    rw [anisotropicPaperTargetCenter_coord_one, abs_mul]
    have hfactor : |m * (d - c) / 2| ≤ 1 / 50 := by
      have hfactorPos : 0 < m * (d - c) / 2 :=
        div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
      rw [abs_of_pos hfactorPos]
      nlinarith [source.slopeScale_le_one, hdc]
    have hyRelative := haxisSmall index 1
    have hyCenter : |center 1| ≤ 1 := hcenterY
    have hyAxis : |wz1PaperAxisPointAtHeight (sourceFamily.tube index)
        (c + (d - c) / 2) 1| ≤ 16 / 15 := by
      have htriangle := abs_add_le
        ((wz1PaperAxisPointAtHeight (sourceFamily.tube index)
          (c + (d - c) / 2) - center) 1) (center 1)
      simpa only [PiLp.sub_apply, sub_add_cancel] using
        htriangle.trans (by linarith)
    calc
      |m * (d - c) / 2| *
          |wz1PaperAxisPointAtHeight (sourceFamily.tube index)
            (c + (d - c) / 2) 1| ≤
        (1 / 50 : ℝ) * (16 / 15) := by gcongr
      _ ≤ 1 / 3 := by norm_num
  rcases construct_anisotropic_paper_retubing sourceFamily sourceShading
      g center hg hcd hdc source.slopeScale_pos source.slopeScale_le_one
      hsub rfl assembly.cfg.extremal.delta_pos htargetPos hradius count
      hcountPos halign hcenterTwo hsourceLine hsourceWindow hcenterY
      hzeroX hzeroY with ⟨raw⟩
  exact ⟨{ popular := popular, raw := raw }⟩

namespace PureWZ2DirectAnisotropicRetubingData

/-- The actual interval selected by the direct route stays in the normalized
source height window. -/
theorem interval_sub_unit
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    Set.Icc assembly.horizontalSource.c assembly.horizontalSource.d ⊆
      Set.Icc (-1 : ℝ) 1 := by
  intro z hz
  exact ⟨assembly.horizontalSource.left_mem.trans hz.1,
    hz.2.trans assembly.horizontalSource.right_mem⟩

/-- The constant global witness used by the affine map is normalized. -/
theorem geometrySlope_normalized
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    (pureWZ2DirectGeometrySlope assembly.horizontalSource).IsNormalized := by
  exact assembly.horizontalSource.geometrySlope_normalized

/-- Exact inverse-transpose normals have the standard uniform lower bound. -/
theorem exactNormal_lower
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    ∀ point,
      1 / ((2 / (assembly.horizontalSource.d -
          assembly.horizontalSource.c)) + 2) ≤
        ‖dPhiInvT (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (data.popular.openSourceLocalGrains.planeMap point)‖ := by
  intro point
  exact dPhiInvT_lower_bound
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    assembly.horizontalSource.c assembly.horizontalSource.d
    assembly.horizontalSource.m assembly.horizontalSource.ordered
    assembly.horizontalSource.slopeScale_pos
    assembly.horizontalSource.slopeScale_le_one
    (by
      rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
      linarith [assembly.rho_tiny])
    data.geometrySlope_normalized data.interval_sub_unit
    (data.popular.openSourceLocalGrains.planeMap point)
    (data.popular.openSourceLocalGrains.planeMap_unit point)

/-- The z-stretch of every vertical-chart source direction compensates the
worst inverse-transpose normal loss. -/
theorem direction_normal_product_lower
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    ∀ index point
      (hpoint : point ∈ data.popular.openSourceShading.carrier index),
      1 / 3 ≤
        ‖dPhiLin (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (wz1PaperDirection (data.popular.family.tube index))‖ *
        ‖dPhiInvT (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (data.popular.openSourceLocalGrains.planeMap
            ⟨point, ⟨index, hpoint⟩⟩)‖ := by
  intro index point hpoint
  let length := assembly.horizontalSource.d - assembly.horizontalSource.c
  let S : ℝ := 2 / length
  let direction := wz1PaperDirection (data.popular.family.tube index)
  let directionImage := dPhiLin
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    assembly.horizontalSource.c assembly.horizontalSource.d
    assembly.horizontalSource.m direction
  let normalImage := dPhiInvT
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    assembly.horizontalSource.c assembly.horizontalSource.d
    assembly.horizontalSource.m
    (data.popular.openSourceLocalGrains.planeMap
      ⟨point, ⟨index, hpoint⟩⟩)
  have hlength : 0 < length := by
    dsimp only [length]
    exact sub_pos.mpr assembly.horizontalSource.ordered
  have hlengthHalf : length ≤ 1 / 2 := by
    dsimp only [length]
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    linarith [assembly.rho_tiny]
  have hSFour : 4 ≤ S := by
    dsimp only [S]
    rw [le_div_iff₀ hlength]
    nlinarith [hlengthHalf]
  have hvertical : (1 / 2 : ℝ) ≤ direction 2 := by
    have hsourceVertical := data.popular.line_class index |>.vertical
    dsimp only [direction]
    unfold wz1PaperDirection
    split_ifs with hsign
    · simpa [abs_of_nonneg hsign] using hsourceVertical
    · have hnonpos : (data.popular.family.tube index).direction 2 ≤ 0 :=
        le_of_not_ge hsign
      simpa [abs_of_nonpos hnonpos] using hsourceVertical
  have hverticalAbs : (1 / 2 : ℝ) ≤ |direction 2| :=
    hvertical.trans (le_abs_self _)
  have hcoord : directionImage 2 = S * direction 2 := by
    dsimp only [directionImage]
    simp [dPhiLin, S, length, point3]
  have hdirectionLower : S / 2 ≤ ‖directionImage‖ := by
    have hcoordNorm := PiLp.norm_apply_le directionImage (2 : Fin 3)
    rw [Real.norm_eq_abs] at hcoordNorm
    have hSPos : 0 < S := by linarith
    have habs : |directionImage 2| = S * |direction 2| := by
      rw [hcoord, abs_mul, abs_of_pos hSPos]
    calc
      S / 2 = S * (1 / 2 : ℝ) := by ring
      _ ≤ S * |direction 2| := by
        exact mul_le_mul_of_nonneg_left hverticalAbs hSPos.le
      _ = |directionImage 2| := habs.symm
      _ ≤ ‖directionImage‖ := hcoordNorm
  have hnormalLower : 1 / (S + 2) ≤ ‖normalImage‖ := by
    simpa [normalImage, S, length] using
      data.exactNormal_lower
        ⟨point, ⟨index, hpoint⟩⟩
  have hfactor : (1 / 3 : ℝ) ≤ (S / 2) * (1 / (S + 2)) := by
    have hdenom : 0 < S + 2 := by linarith
    rw [show S / 2 * (1 / (S + 2)) = (S / 2) / (S + 2) by ring]
    apply (le_div_iff₀ hdenom).2
    nlinarith
  exact hfactor.trans <| mul_le_mul hdirectionLower hnormalLower
    (by positivity) (norm_nonneg _)

/-- The same product lower bound for the stored tube direction.  The paper's
positive-vertical direction differs from it by at most a sign, which is
invisible after applying the linear map and taking a norm. -/
theorem direction_normal_product_lower_raw
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    ∀ index point
      (hpoint : point ∈ data.popular.openSourceShading.carrier index),
      1 / 3 ≤
        ‖dPhiLin (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (data.popular.family.tube index).direction‖ *
        ‖dPhiInvT (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (data.popular.openSourceLocalGrains.planeMap
            ⟨point, ⟨index, hpoint⟩⟩)‖ := by
  intro index point hpoint
  have hpaper := data.direction_normal_product_lower index point hpoint
  unfold wz1PaperDirection at hpaper
  split_ifs at hpaper with hdirection
  · exact hpaper
  · have hneg :
        dPhiLin (pureWZ2DirectGeometrySlope assembly.horizontalSource)
            assembly.horizontalSource.c assembly.horizontalSource.d
            assembly.horizontalSource.m
            (-(data.popular.family.tube index).direction) =
          -dPhiLin (pureWZ2DirectGeometrySlope assembly.horizontalSource)
            assembly.horizontalSource.c assembly.horizontalSource.d
            assembly.horizontalSource.m
            (data.popular.family.tube index).direction := by
      ext coordinate
      fin_cases coordinate <;> simp [dPhiLin, point3] <;> ring
    rw [hneg, norm_neg] at hpaper
    exact hpaper

/-- Package the exact-image local plane map directly from the actual Node-5
local grains. -/
theorem toExactPlaneMapData
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    Nonempty (PureWZ2AnisotropicExactPlaneMapData data.raw
      data.popular.openSourceLocalGrains) := by
  let length := assembly.horizontalSource.d - assembly.horizontalSource.c
  have hlength : 0 < length := by
    dsimp only [length]
    exact sub_pos.mpr assembly.horizontalSource.ordered
  have hlower : 0 < 1 / (2 / length + 2) := by positivity
  have hrawPos : 0 < anisotropicPaperRawScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d := by
    unfold anisotropicPaperRawScale
    exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
      hlength
  have hrawHalf : anisotropicPaperRawScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d ≤ 1 / 2 := by
    have hlengthEq : length = assembly.rho.1 / 100 := by
      dsimp only [length]
      rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    have hrawEq : anisotropicPaperRawScale delta assembly.horizontalSource.c
        assembly.horizontalSource.d = 1600 * delta / assembly.rho.1 := by
      unfold anisotropicPaperRawScale
      change 16 * delta / length = _
      rw [hlengthEq]
      field_simp [hlength.ne']
      ring
    rw [hrawEq, div_le_iff₀
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
    have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
      linarith [assembly.rho_tiny]
    nlinarith [assembly.delta_le_rho_sq,
      mul_nonneg
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
        hfactor]
  have hsourceTarget : 3 * delta ≤
      anisotropicPaperAlignedScale delta assembly.horizontalSource.c
        assembly.horizontalSource.d := by
    have hraw := anisotropicPaperRawScale_le_aligned hrawPos hrawHalf
    unfold anisotropicPaperRawScale at hraw
    have hlengthOne : length ≤ 1 := by
      dsimp only [length]
      rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
      linarith [assembly.rho_tiny]
    have hdeltaNonneg : 0 ≤ delta := assembly.cfg.extremal.delta_pos.le
    calc
      3 * delta ≤ 16 * delta / length := by
        rw [le_div_iff₀ hlength]
        nlinarith
      _ ≤ anisotropicPaperAlignedScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d := by
        simpa [length] using hraw
  exact data.raw.toExactPlaneMapData data.popular.openSourceLocalGrains
    hlower data.exactNormal_lower data.direction_normal_product_lower
      hsourceTarget

/-- Canonical direct exact plane map with a definitionally visible
Lipschitz constant for the final isotropic scale budget. -/
def exactPlaneMapData
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    PureWZ2AnisotropicExactPlaneMapData data.raw
      data.popular.openSourceLocalGrains :=
  data.raw.exactPlaneMapData data.popular.openSourceLocalGrains
    (by
      have hlength : 0 < assembly.horizontalSource.d -
          assembly.horizontalSource.c :=
        sub_pos.mpr assembly.horizontalSource.ordered
      positivity)
    data.exactNormal_lower data.direction_normal_product_lower <| by
      have hlength : 0 < assembly.horizontalSource.d -
          assembly.horizontalSource.c :=
        sub_pos.mpr assembly.horizontalSource.ordered
      have hrawPos : 0 < anisotropicPaperRawScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d := by
        unfold anisotropicPaperRawScale
        exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
          hlength
      have hrawHalf : anisotropicPaperRawScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d ≤ 1 / 2 := by
        have hlengthEq : assembly.horizontalSource.d -
            assembly.horizontalSource.c = assembly.rho.1 / 100 := by
          rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
        have hrawEq : anisotropicPaperRawScale delta
            assembly.horizontalSource.c assembly.horizontalSource.d =
              1600 * delta / assembly.rho.1 := by
          unfold anisotropicPaperRawScale
          rw [hlengthEq]
          field_simp [show assembly.rho.1 ≠ 0 by
            exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
              assembly.rho.2.1)]
          ring
        rw [hrawEq, div_le_iff₀
          (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
        have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
          linarith [assembly.rho_tiny]
        nlinarith [assembly.delta_le_rho_sq,
          mul_nonneg
            (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
            hfactor]
      have hraw := anisotropicPaperRawScale_le_aligned hrawPos hrawHalf
      unfold anisotropicPaperRawScale at hraw
      have hlengthOne : assembly.horizontalSource.d -
          assembly.horizontalSource.c ≤ 1 := by
        rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
        linarith [assembly.rho_tiny]
      calc
        3 * delta ≤ 16 * delta /
            (assembly.horizontalSource.d - assembly.horizontalSource.c) := by
          rw [le_div_iff₀ hlength]
          nlinarith [assembly.cfg.extremal.delta_pos]
        _ ≤ anisotropicPaperAlignedScale delta
            assembly.horizontalSource.c assembly.horizontalSource.d := hraw

@[simp] theorem exactPlaneMapData_K
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    data.exactPlaneMapData.K =
      ⟨2 / (1 / (2 / (assembly.horizontalSource.d -
          assembly.horizontalSource.c) + 2)), by
            have hlength : 0 < assembly.horizontalSource.d -
                assembly.horizontalSource.c :=
              sub_pos.mpr assembly.horizontalSource.ordered
            positivity⟩ *
        ‖(dPhiInvTLinear
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m).toContinuousLinearMap‖₊ *
        1 *
        ‖(anisotropicRescalingLinearEquiv
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m assembly.horizontalSource.ordered
          assembly.horizontalSource.slopeScale_pos).symm
            |>.toContinuousLinearEquiv.toContinuousLinearMap‖₊ := by
  rfl

end PureWZ2DirectAnisotropicRetubingData

end Kakeya.Assouad

end
