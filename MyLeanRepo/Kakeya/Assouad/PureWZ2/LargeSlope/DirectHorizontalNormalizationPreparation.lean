import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectCleanupRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalPopularBoxPullback

/-!
# Source preparation for the direct horizontal normalization

After the two source regularizations, the selected source family still carries
nearby CWA and both grain fields.  Its exact triangular image is the correct
place to choose the paper's two-dimensional popular box.  This file pulls that
box back through the triangular affine equivalence, so the later combined map
acts on a literal source subshading and does not apply the triangular transport
twice.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2ExternalWeightRegularizationData

/-- Source shading after the second direct regularization. -/
def directFinalSourceShading
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    WZ1PaperTubeShading data.selected.family :=
  restrictPaperShading data.selected
    (pureWZ2DirectRegularizedSourceShading retubing regularized)

/-- Every point retained by the twice-regularized direct source still lies in
the half-open selected Section-6 height interval. -/
theorem directFinalSourceShading_height_open
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    ∀ index point,
      point ∈ (directFinalSourceShading (retubing := retubing)
        (regularized := regularized) data).carrier index →
      assembly.horizontalSource.c ≤ point 2 ∧
        point 2 < assembly.horizontalSource.d := by
  intro index point hpoint
  have hsourceSlab : ∀ sourceIndex,
      retubing.popular.sourceShading.carrier sourceIndex ⊆
        horizontalSlab assembly.horizontalSource.c
          assembly.horizontalSource.d := by
    intro sourceIndex sourcePoint hsourcePoint
    rw [retubing.popular.source_carrier_eq,
      retubing.popular.popular.restricted_carrier] at hsourcePoint
    exact assembly.horizontalSource.source_in_interval _ hsourcePoint.1
  change point ∈ retubing.popular.openSourceShading.carrier
    ((regularized.toDirectNonemptySubfamily retubing).embedding
      (data.selected.embedding index)) at hpoint
  exact paperShadingRemoveTopFace_height hsourceSlab _ hpoint

/-- Closed-interval form of `directFinalSourceShading_height_open`. -/
theorem directFinalSourceShading_height
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    ∀ index point,
      point ∈ (directFinalSourceShading (retubing := retubing)
        (regularized := regularized) data).carrier index →
      point 2 ∈ Set.Icc assembly.horizontalSource.c
        assembly.horizontalSource.d := by
  intro index point hpoint
  have hheight := directFinalSourceShading_height_open data index point hpoint
  exact ⟨hheight.1, hheight.2.le⟩

/-- Local grains on exactly the source indices retained by the second direct
regularization. -/
def directFinalSourceLocalGrains
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    PureWZ2LocalGrainData
      (directFinalSourceShading (retubing := retubing)
        (regularized := regularized) data) sigma
      (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  (regularized.directRegularizedSourceLocalGrains retubing).subfamily
    data.selected

/-- Global grains on the same final source indices. -/
def directFinalSourceGlobalGrains
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    PureWZ2C2GlobalGrainData
      (directFinalSourceShading (retubing := retubing)
        (regularized := regularized) data) sigma
      (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  (retubing.popular.openSourceGlobalGrains.subfamily
      (regularized.toDirectNonemptySubfamily retubing)).subfamily data.selected

theorem directFinalSourceShading_mass_lower
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    regularized.selectedWeightLevel * data.selected.family.enncard ≤
      (directFinalSourceShading (retubing := retubing)
        (regularized := regularized) data).mass := by
  change regularized.selectedWeightLevel *
        (data.selected.family.card : ENNReal) ≤
    ∑ index : Fin data.selected.family.card,
      volume (retubing.popular.openSourceShading.carrier
        ((regularized.toDirectNonemptySubfamily retubing).embedding
          (data.selected.embedding index)))
  calc
    regularized.selectedWeightLevel *
          (data.selected.family.card : ENNReal) =
        ∑ _index : Fin data.selected.family.card,
          regularized.selectedWeightLevel := by
      simp [Finset.sum_const, mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun index _ => by
      have hband := regularized.selected_weight_band
        (data.selected.embedding index)
      change regularized.selectedWeightLevel ≤
        volume (retubing.popular.openSourceShading.carrier
          ((regularized.toDirectNonemptySubfamily retubing).embedding
            (data.selected.embedding index)))
      change regularized.selectedWeightLevel ≤ volume
        (retubing.popular.sourceShading.carrier
          ((regularized.toDirectNonemptySubfamily retubing).embedding
            (data.selected.embedding index)) \
          {point : Point3 | point 2 = assembly.horizontalSource.d})
      rw [measure_sdiff_null
        (volume_coordinate_hyperplane_zero 2
          assembly.horizontalSource.d)]
      rw [retubing.popular.source_carrier_eq]
      change regularized.selectedWeightLevel ≤ volume
        (retubing.popular.popular.restricted.carrier
          ((wz2PaperNonemptyCarrierSubfamily
            retubing.popular.popular.restricted).embedding
              (pureWZ2DirectPackedIndex retubing regularized
                (data.selected.embedding index))))
      have hembed := pureWZ2DirectPackedIndex_ambient retubing regularized
        (data.selected.embedding index)
      rw [hembed]
      exact hband.1

/-- Top-level CWA constant on the twice-regularized direct source family. -/
def directFinalSourceTopConstant
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) : ENNReal :=
  ((anisotropicPaperCleanupNormalization assembly.horizontalSource.m
      regularized.selectedWeightLevel)⁻¹ * data.retentionConstant) *
    pureWZ2DirectRegularizedSourceTopConstant retubing regularized

theorem directFinalSourceTopCWA
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    WZ2PaperConvexWolffBound data.selected.family
      (directFinalSourceTopConstant (retubing := retubing)
        (regularized := regularized) data) := by
  apply data.top_level_cwa
    (regularized.top_level_cwa assembly.cfg.top_level_cwa
      (pureWZ2DirectPopularSourceNormalization_pos
        assembly.horizontalSource).ne'
      (pureWZ2DirectPopularSourceNormalization_ne_top
        assembly.horizontalSource))
  · unfold anisotropicPaperCleanupNormalization
    exact mul_ne_zero
      (ENNReal.ofReal_pos.mpr assembly.horizontalSource.slopeScale_pos).ne'
      regularized.selectedWeightLevel_pos.ne'
  · unfold anisotropicPaperCleanupNormalization
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      regularized.selectedWeightLevel_ne_top

/-- Exact triangular retubing on the source family retained after both direct
regularizations. -/
def directFinalRaw
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :=
  (retubing.regularizedRaw regularized).subfamily data.selected

/-- Select the paper's horizontal box on the exact triangular image of the
twice-regularized direct source. -/
theorem toDirectFinalHorizontalPopularBox
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :=
  pureWZ2_horizontal_popular_box
    (directFinalRaw (retubing := retubing)
      (regularized := regularized) data).exactShading
    hwidth hwidthOne

/-- Pull the selected horizontal box back to the source before applying the
combined triangular and horizontal affine map. -/
def directHorizontalPopularSourceShading
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    WZ1PaperTubeShading data.selected.family :=
  pureWZ2HorizontalPopularPullbackShading
    (directFinalRaw (retubing := retubing)
      (regularized := regularized) data) popular

theorem directHorizontalPopularSourceShading_subshading
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    ∀ index,
      (directHorizontalPopularSourceShading data popular).carrier index ⊆
        (directFinalSourceShading (retubing := retubing)
          (regularized := regularized) data).carrier index :=
  pureWZ2HorizontalPopularPullbackShading_subshading
    (directFinalRaw (retubing := retubing)
      (regularized := regularized) data) popular

/-- The original local grains restricted to the source pullback of the
horizontal popular box. -/
def directHorizontalPopularSourceLocalGrains
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    PureWZ2LocalGrainData (directHorizontalPopularSourceShading data popular)
      sigma (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  (directFinalSourceLocalGrains (retubing := retubing)
    (regularized := regularized) data).restrict
      (directHorizontalPopularSourceShading_subshading data popular)

/-- The global grains restricted to the identical source pullback. -/
def directHorizontalPopularSourceGlobalGrains
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    PureWZ2C2GlobalGrainData
      (directHorizontalPopularSourceShading data popular) sigma
      (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  (directFinalSourceGlobalGrains (retubing := retubing)
    (regularized := regularized) data).restrict_same_constant
      (directHorizontalPopularSourceShading_subshading data popular)

/-- Local grains on the genuine source subfamily obtained after deleting
empty horizontal pullback carriers. -/
def directHorizontalPopularNonemptySourceLocalGrains
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    PureWZ2LocalGrainData
      (pureWZ2HorizontalPopularPullbackNonemptyShading
        (directFinalRaw (retubing := retubing)
          (regularized := regularized) data) popular)
      sigma (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  (directHorizontalPopularSourceLocalGrains data popular).subfamily
    (pureWZ2HorizontalPopularPullbackSourceSubfamily
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data) popular)

/-- Global grains restricted to the identical genuine source subfamily. -/
def directHorizontalPopularNonemptySourceGlobalGrains
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    PureWZ2C2GlobalGrainData
      (pureWZ2HorizontalPopularPullbackNonemptyShading
        (directFinalRaw (retubing := retubing)
          (regularized := regularized) data) popular)
      sigma (Kakeya.realRpowENN delta (-assembly.technicalLoss)) :=
  (directHorizontalPopularSourceGlobalGrains data popular).subfamily
    (pureWZ2HorizontalPopularPullbackSourceSubfamily
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data) popular)

/-- The triangular direction/normal product lower bound survives both source
regularizations, the horizontal-box pullback, and deletion of empty carriers. -/
theorem directHorizontalPopularNonemptySource_direction_normal_product_lower
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    ∀ index point
      (hpoint : point ∈
        (pureWZ2HorizontalPopularPullbackNonemptyShading
          (directFinalRaw (retubing := retubing)
            (regularized := regularized) data) popular).carrier index),
      1 / 3 ≤
        ‖dPhiLin (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          ((pureWZ2HorizontalPopularPullbackSourceSubfamily
            (directFinalRaw (retubing := retubing)
              (regularized := regularized) data) popular).family.tube
            index).direction‖ *
        ‖dPhiInvT (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          ((directHorizontalPopularNonemptySourceLocalGrains data popular).planeMap
            ⟨point, ⟨index, hpoint⟩⟩)‖ := by
  intro index point hpoint
  let raw := directFinalRaw (retubing := retubing)
    (regularized := regularized) data
  let selected := pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular
  have hsource : point ∈
      retubing.popular.openSourceShading.carrier
        ((regularized.toDirectNonemptySubfamily retubing).embedding
          (data.selected.embedding (selected.embedding index))) := by
    exact hpoint.1
  let ambientIndex :=
    (regularized.toDirectNonemptySubfamily retubing).embedding
      (data.selected.embedding (selected.embedding index))
  let ambientPoint : {point : Point3 //
      point ∈ retubing.popular.openSourceShading.union} :=
    ⟨point, ⟨ambientIndex, hsource⟩⟩
  have htube : selected.family.tube index =
      retubing.popular.family.tube ambientIndex := by
    rw [selected.tube_eq, data.selected.tube_eq,
      (regularized.toDirectNonemptySubfamily retubing).tube_eq]
  have hplane :
      (directHorizontalPopularNonemptySourceLocalGrains data popular).planeMap
          ⟨point, ⟨index, hpoint⟩⟩ =
        retubing.popular.openSourceLocalGrains.planeMap ambientPoint := by
    change retubing.popular.openSourceLocalGrains.planeMap _ =
      retubing.popular.openSourceLocalGrains.planeMap ambientPoint
    congr 1
  have hbase := retubing.direction_normal_product_lower_raw
    ambientIndex point hsource
  rw [htube, hplane]
  exact hbase

/-- The exact triangular image of the pulled-back source carrier is literally
the carrier selected by the horizontal popular box. -/
theorem directHorizontalPopularSourceShading_image
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width)
    (index : Fin data.selected.family.card) :
    anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) ''
        (directHorizontalPopularSourceShading data popular).carrier index =
      popular.restricted.carrier index :=
  pureWZ2HorizontalPopularPullbackShading_image
    (directFinalRaw (retubing := retubing)
      (regularized := regularized) data) popular index

/-- The pullback has exactly the triangular Jacobian needed to recover the
popular-box mass.  In particular, no third power of the box width appears. -/
theorem directHorizontalPopularSourceShading_mass
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    popular.restricted.mass =
      ENNReal.ofReal assembly.horizontalSource.m *
      (directHorizontalPopularSourceShading data popular).mass :=
  pureWZ2HorizontalPopularPullbackShading_mass
    (directFinalRaw (retubing := retubing)
      (regularized := regularized) data) popular

/-- The horizontal pullback retains its explicit share of the twice
regularized source mass before empty carriers are deleted. -/
theorem directHorizontalPopularSourceShading_mass_lower
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading width) :
    ENNReal.ofReal (width ^ 2 / 9) *
        (directFinalSourceShading (retubing := retubing)
          (regularized := regularized) data).mass ≤
      (directHorizontalPopularSourceShading data popular).mass :=
  pureWZ2HorizontalPopularPullbackShading_mass_lower
    (directFinalRaw (retubing := retubing)
      (regularized := regularized) data) popular

end PureWZ2ExternalWeightRegularizationData

end Kakeya.Assouad

end
