import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationExactPlaneMap

/-!
# Exact family and shading under horizontal normalization

This file puts the exact combined affine image on an actual paper tube
family.  Cubical saturation and line-class cleanup remain separate: the only
geometric input required here is that each exact carrier lies in its chosen
target paper tube.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The normalized image of a nonzero direction under the combined affine
linear map is a unit vector. -/
theorem pureWZ2HorizontalNormalizedExactDirection_unit
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {direction : Point3} (hdirection : direction ≠ 0) :
    ‖pureWZ2HorizontalNormalizedExactDirection g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda direction‖ = 1 := by
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  let imageDirection := equivalence.linear direction
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    apply hdirection
    apply equivalence.linear.injective
    simpa [imageDirection] using hzero
  have hnorm : 0 < ‖imageDirection‖ := norm_pos_iff.mpr himageDirection
  change ‖(‖imageDirection‖⁻¹ : ℝ) • imageDirection‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [hnorm.ne']

/-- Affine maps carry a parametrized line by applying their linear part to
the direction. -/
theorem pureWZ2HorizontalNormalizedMap_add_smul
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (base direction : Point3) (scalar : ℝ) :
    pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda (base + scalar • direction) =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda base +
        scalar •
          (pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
            horizontalCenter lambda hcd hm hlambda).linear direction := by
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  have hmap := equivalence.map_vadd base (scalar • direction)
  rw [map_smul] at hmap
  simpa only [vadd_eq_add, add_comm, equivalence,
    pureWZ2HorizontalNormalizedAffineEquiv_apply] using hmap

/-- A target tube whose supporting line is the exact combined affine image
of the source supporting line.  The target radius remains an external
parameter, as it is fixed only by the later retubing/saturation budget. -/
def pureWZ2HorizontalNormalizedExactTube
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta) :
    Kakeya.DeltaTube targetDelta where
  base := pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
    horizontalCenter lambda source.base
  direction := pureWZ2HorizontalNormalizedExactDirection g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda source.direction
  direction_unit := pureWZ2HorizontalNormalizedExactDirection_unit
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda <| by
      intro hzero
      have hnorm := congrArg norm hzero
      rw [source.direction_unit, norm_zero] at hnorm
      norm_num at hnorm

/-- The target tube has exactly the affine-image supporting line. -/
theorem pureWZ2HorizontalNormalizedExactTube_axis
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta) :
    tubeAxisLine
        (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
          horizontalCenter lambda hcd hm hlambda source :
            Kakeya.DeltaTube targetDelta) =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda '' tubeAxisLine source := by
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  let imageDirection := equivalence.linear source.direction
  have hsourceDirection : source.direction ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    rw [source.direction_unit, norm_zero] at hnorm
    norm_num at hnorm
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    apply hsourceDirection
    apply equivalence.linear.injective
    simpa [imageDirection] using hzero
  have himageNorm : 0 < ‖imageDirection‖ :=
    norm_pos_iff.mpr himageDirection
  ext target
  constructor
  · rintro ⟨parameter, rfl⟩
    refine ⟨source.base + (parameter / ‖imageDirection‖) • source.direction,
      ⟨parameter / ‖imageDirection‖, rfl⟩, ?_⟩
    rw [pureWZ2HorizontalNormalizedMap_add_smul g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda]
    change pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda source.base +
          (parameter / ‖imageDirection‖) • imageDirection =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda source.base +
        parameter • ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [smul_smul]
    congr 2
  · rintro ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨parameter * ‖imageDirection‖, ?_⟩
    rw [pureWZ2HorizontalNormalizedMap_add_smul g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda]
    change pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda source.base + parameter • imageDirection =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda source.base +
        (parameter * ‖imageDirection‖) •
          ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [smul_smul]
    congr 2
    field_simp [himageNorm.ne']

/-- The one-to-one exact supporting-line family for the combined map. -/
def pureWZ2HorizontalNormalizedExactFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2HorizontalNormalizedExactTube g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda
      (sourceFamily.tube index)

@[simp] theorem pureWZ2HorizontalNormalizedExactFamily_tube
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (index : Fin sourceFamily.card) :
    (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
      sourceFamily g c d m anisotropicCenter horizontalCenter lambda
        hcd hm hlambda).tube index =
      pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda (sourceFamily.tube index) :=
  rfl

/-- The literal exact-image shading on the combined-map target family. -/
def pureWZ2HorizontalNormalizedExactShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index)) :
    WZ1PaperTubeShading
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda) where
  carrier index := pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
    horizontalCenter lambda '' sourceShading.carrier index
  measurable_carrier index := by
    let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
    have heq :
        pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
            horizontalCenter lambda '' sourceShading.carrier index =
          equivalence '' sourceShading.carrier index := by
      ext point
      simp only [Set.mem_image]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource,
          pureWZ2HorizontalNormalizedAffineEquiv_apply
            g c d m anisotropicCenter horizontalCenter lambda hcd hm
              hlambda source⟩
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource,
          (pureWZ2HorizontalNormalizedAffineEquiv_apply
            g c d m anisotropicCenter horizontalCenter lambda hcd hm
              hlambda source).symm⟩
    rw [heq]
    exact equivalence.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr (sourceShading.measurable_carrier index)
  subset_body index := hcarrier index

@[simp] theorem pureWZ2HorizontalNormalizedExactShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (index : Fin sourceFamily.card) :
    (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda hcarrier).carrier
        index =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda '' sourceShading.carrier index :=
  rfl

/-- The union of the exact target shading is the exact combined image of the
source union. -/
theorem pureWZ2HorizontalNormalizedExactShading_union
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index)) :
    (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda hcarrier).union =
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda sourceShading.union := by
  ext point
  constructor
  · rintro ⟨index, source, hsource, rfl⟩
    exact ⟨source, ⟨index, hsource⟩, rfl⟩
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, source, hsource, rfl⟩

/-- The exact target shading has the combined Jacobian mass identity. -/
theorem pureWZ2HorizontalNormalizedExactShading_mass
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index)) :
    (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda hcarrier).mass =
      ENNReal.ofReal (m * lambda ^ 2) * sourceShading.mass := by
  change (∑ index, volume
      (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda '' sourceShading.carrier index)) =
    ENNReal.ofReal (m * lambda ^ 2) *
      ∑ index, volume (sourceShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact volume_image_pureWZ2HorizontalNormalizedMap
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda _

/-- Regard a point of the exact target shading as a point of the literal
combined affine image.  This is an isometric identity inclusion; only the set
membership proof changes. -/
def pureWZ2HorizontalNormalizedExactShadingInclusion
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (target : {point : Point3 // point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).union}) :
    {point : Point3 // point ∈
      pureWZ2HorizontalNormalizedExactImage g c d m anisotropicCenter
        horizontalCenter lambda sourceShading.union} :=
  ⟨target, by
    rw [← pureWZ2HorizontalNormalizedExactShading_union sourceShading
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hcarrier]
    exact target.property⟩

theorem pureWZ2HorizontalNormalizedExactShadingInclusion_lipschitz
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index)) :
    LipschitzWith 1
      (pureWZ2HorizontalNormalizedExactShadingInclusion sourceShading
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simp [pureWZ2HorizontalNormalizedExactShadingInclusion, Subtype.dist_eq]

/-- The combined inverse-transpose plane map, now typed on the exact target
paper shading. -/
def pureWZ2HorizontalNormalizedExactShadingPlaneMap
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (target : {point : Point3 // point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).union}) : Point3 :=
  pureWZ2HorizontalNormalizedExactPlaneMap g c d m anisotropicCenter
    horizontalCenter lambda hcd hm hlambda sourceShading.union
      sourceLocal.planeMap
      (pureWZ2HorizontalNormalizedExactShadingInclusion sourceShading
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier target)

theorem pureWZ2HorizontalNormalizedExactShadingPlaneMap_unit
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (target : {point : Point3 // point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).union}) :
    ‖pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading sourceLocal
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hcarrier target‖ = 1 := by
  exact pureWZ2HorizontalNormalizedExactPlaneMap_unit g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda
      sourceShading.union sourceLocal.planeMap sourceLocal.planeMap_unit _

theorem pureWZ2HorizontalNormalizedExactShadingPlaneMap_lipschitz
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (lower : ℝ) (hlower : 0 < lower)
    (hnormalLower : ∀ point, lower ≤
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourceLocal.planeMap point)‖) :
    LipschitzWith
      (pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda 1
          lower hlower)
      (pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading
        sourceLocal g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda hcarrier) := by
  have hraw := pureWZ2HorizontalNormalizedExactPlaneMap_lipschitz
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
      sourceShading.union sourceLocal.planeMap 1
        sourceLocal.planeMap_lipschitz lower hlower hnormalLower
  have hinclusion :=
    pureWZ2HorizontalNormalizedExactShadingInclusion_lipschitz sourceShading
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hcarrier
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hfield := hraw.dist_le_mul
    (pureWZ2HorizontalNormalizedExactShadingInclusion sourceShading
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hcarrier first)
    (pureWZ2HorizontalNormalizedExactShadingInclusion sourceShading
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hcarrier second)
  have hdist := hinclusion.dist_le_mul first second
  calc
    dist
        (pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading
          sourceLocal g c d m anisotropicCenter horizontalCenter lambda
            hcd hm hlambda hcarrier first)
        (pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading
          sourceLocal g c d m anisotropicCenter horizontalCenter lambda
            hcd hm hlambda hcarrier second)
        ≤ (pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda 1
              lower hlower : ℝ) *
            dist
              (pureWZ2HorizontalNormalizedExactShadingInclusion sourceShading
                g c d m anisotropicCenter horizontalCenter lambda hcd hm
                  hlambda hcarrier first)
              (pureWZ2HorizontalNormalizedExactShadingInclusion sourceShading
                g c d m anisotropicCenter horizontalCenter lambda hcd hm
                  hlambda hcarrier second) := hfield
    _ ≤ (pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda 1
              lower hlower : ℝ) * (1 * dist first second) := by
          exact mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = (pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda 1
              lower hlower : ℝ) * dist first second := by ring

/-- Incidence for the exact target family follows from incidence at the
canonical source point and a positive combined direction/normal product
lower bound `q`. -/
theorem pureWZ2HorizontalNormalizedExactShadingPlaneMap_incidence_source_div
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (q : ℝ) (hq : 0 < q)
    (hproduct : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        q ≤
          ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
              (sourceFamily.tube index).direction‖ *
          ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
            (sourceLocal.planeMap ⟨point, ⟨index, hpoint⟩⟩)‖) :
    ∀ index point, ∀ hpoint : point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).carrier index,
      |inner ℝ
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index).direction
          (pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading
            sourceLocal g c d m anisotropicCenter horizontalCenter lambda
              hcd hm hlambda hcarrier ⟨point, ⟨index, hpoint⟩⟩)| ≤
        sourceDelta / q := by
  intro index point hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, heq⟩
  let target : {point : Point3 // point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).union} :=
    ⟨point, ⟨index, sourcePoint, hsourcePoint, heq⟩⟩
  let imageTarget := pureWZ2HorizontalNormalizedExactShadingInclusion
    sourceShading g c d m anisotropicCenter horizontalCenter lambda
      hcd hm hlambda hcarrier target
  let source := pureWZ2HorizontalNormalizedExactSourcePoint
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
      sourceShading.union imageTarget
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  have hsourceEq : (source : Point3) = sourcePoint := by
    apply equivalence.injective
    have hmapsource :
        pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
            horizontalCenter lambda (source : Point3) =
          (imageTarget : Point3) := by
      exact pureWZ2HorizontalNormalizedMap_exactSourcePoint g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          sourceShading.union imageTarget
    rw [show equivalence (source : Point3) = imageTarget by
      rw [pureWZ2HorizontalNormalizedAffineEquiv_apply]
      exact hmapsource]
    change (imageTarget : Point3) = equivalence sourcePoint
    rw [pureWZ2HorizontalNormalizedAffineEquiv_apply]
    exact heq.symm
  have hsourceCarrier : (source : Point3) ∈ sourceShading.carrier index := by
    rwa [hsourceEq]
  have hsourceSubtypeEq : source =
      ⟨sourcePoint, ⟨index, hsourcePoint⟩⟩ := by
    apply Subtype.ext
    exact hsourceEq
  have hdirection : (sourceFamily.tube index).direction ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    rw [(sourceFamily.tube index).direction_unit, norm_zero] at hnorm
    norm_num at hnorm
  have hsourceIncidence := sourceLocal.planeMap_incidence
    index (source : Point3) hsourceCarrier
  have hsourceBound :
      |inner ℝ (sourceFamily.tube index).direction
        (sourceLocal.planeMap source)| ≤ sourceDelta := by
    simpa only [hsourceSubtypeEq] using hsourceIncidence
  have hproductAt : q ≤
      ‖equivalence.linear (sourceFamily.tube index).direction‖ *
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourceLocal.planeMap source)‖ := by
    simpa only [equivalence, hsourceSubtypeEq] using
      hproduct index (source : Point3) hsourceCarrier
  have hresult :=
    pureWZ2HorizontalNormalizedExactPlaneMap_incidence_le_div
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
        sourceShading.union sourceLocal.planeMap sourceLocal.planeMap_unit
          imageTarget (sourceFamily.tube index).direction hdirection
            sourceDelta q hsourceBound hq hproductAt
  simpa only [pureWZ2HorizontalNormalizedExactFamily,
    pureWZ2HorizontalNormalizedExactTube,
    pureWZ2HorizontalNormalizedExactShadingPlaneMap, target, imageTarget]
    using hresult

/-- Compatibility form of
`pureWZ2HorizontalNormalizedExactShadingPlaneMap_incidence_source_div` at
`q = 1/3`. -/
theorem pureWZ2HorizontalNormalizedExactShadingPlaneMap_incidence_source
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (hproduct : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        1 / 3 ≤
          ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
              (sourceFamily.tube index).direction‖ *
          ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
            (sourceLocal.planeMap ⟨point, ⟨index, hpoint⟩⟩)‖) :
    ∀ index point, ∀ hpoint : point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).carrier index,
      |inner ℝ
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index).direction
          (pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading
            sourceLocal g c d m anisotropicCenter horizontalCenter lambda
              hcd hm hlambda hcarrier ⟨point, ⟨index, hpoint⟩⟩)| ≤
        3 * sourceDelta := by
  have hresult :=
    pureWZ2HorizontalNormalizedExactShadingPlaneMap_incidence_source_div
      sourceShading sourceLocal g c d m anisotropicCenter horizontalCenter
        lambda hcd hm hlambda hcarrier (1 / 3 : ℝ) (by norm_num) hproduct
  simpa [div_eq_mul_inv, mul_comm] using hresult

/-- The exact family, exact shading, and exact plane map remain attached to
one combined affine transformation. -/
structure PureWZ2HorizontalNormalizedExactFamilyPlaneMapData
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index)) where
  K : NNReal
  planeMap : {point : Point3 // point ∈
    (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hcarrier).union} → Point3
  planeMap_eq : planeMap =
    pureWZ2HorizontalNormalizedExactShadingPlaneMap sourceShading sourceLocal
      g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda hcarrier
  planeMap_lipschitz : LipschitzWith K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence_source :
    ∀ index point, ∀ hpoint : point ∈
      (pureWZ2HorizontalNormalizedExactShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hcarrier).carrier index,
      |inner ℝ
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index).direction
          (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 3 * sourceDelta

/-- Assemble the family/shading-typed exact plane-map package. -/
theorem pureWZ2_toHorizontalNormalizedExactFamilyPlaneMapData
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2HorizontalNormalizedExactFamily
            (targetDelta := targetDelta) sourceFamily g c d m
              anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
            index))
    (lower : ℝ) (hlower : 0 < lower)
    (hnormalLower : ∀ point, lower ≤
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
        (sourceLocal.planeMap point)‖)
    (hproduct : ∀ index point
      (hpoint : point ∈ sourceShading.carrier index),
        1 / 3 ≤
          ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
              (sourceFamily.tube index).direction‖ *
          ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda
            (sourceLocal.planeMap ⟨point, ⟨index, hpoint⟩⟩)‖) :
    Nonempty (PureWZ2HorizontalNormalizedExactFamilyPlaneMapData
      sourceShading sourceLocal g c d m anisotropicCenter horizontalCenter
        lambda hcd hm hlambda hcarrier) := by
  let K := pureWZ2HorizontalNormalizedExactPlaneMapK g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda 1 lower hlower
  exact ⟨{
    K := K
    planeMap := pureWZ2HorizontalNormalizedExactShadingPlaneMap
      sourceShading sourceLocal g c d m anisotropicCenter horizontalCenter
        lambda hcd hm hlambda hcarrier
    planeMap_eq := rfl
    planeMap_lipschitz := by
      simpa only [K] using
        pureWZ2HorizontalNormalizedExactShadingPlaneMap_lipschitz
          sourceShading sourceLocal g c d m anisotropicCenter horizontalCenter
            lambda hcd hm hlambda hcarrier lower hlower hnormalLower
    planeMap_unit :=
      pureWZ2HorizontalNormalizedExactShadingPlaneMap_unit
        sourceShading sourceLocal g c d m anisotropicCenter horizontalCenter
          lambda hcd hm hlambda hcarrier
    planeMap_incidence_source :=
      pureWZ2HorizontalNormalizedExactShadingPlaneMap_incidence_source
        sourceShading sourceLocal g c d m anisotropicCenter horizontalCenter
          lambda hcd hm hlambda hcarrier hproduct
  }⟩

end Kakeya.Assouad

end
