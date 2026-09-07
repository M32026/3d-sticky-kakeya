import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactImage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoverRemoveEmptyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Pulling a horizontal popular box back through the triangular map

The horizontal box is selected in exact triangular-image coordinates.  Its
preimage is the literal source shading to which the combined triangular and
horizontal map must be applied.  The carrier identity and Jacobian identity
below prevent an accidental second application of the triangular map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Source restriction obtained by pulling an exact-image horizontal box back
through the triangular affine equivalence. -/
def pureWZ2HorizontalPopularPullbackShading
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    WZ1PaperTubeShading sourceFamily where
  carrier index := sourceShading.carrier index ∩
    (anisotropicCenteredRescalingAffineEquiv g c d m anisotropicCenter
      hcd hm) ⁻¹' popular.box
  measurable_carrier index := by
    apply MeasurableSet.inter (sourceShading.measurable_carrier index)
    exact popular.box_measurable.preimage
      (anisotropicCenteredRescalingAffineEquiv g c d m anisotropicCenter
        hcd hm).toHomeomorphOfFiniteDimensional.toMeasurableEquiv.measurable
  subset_body index point hpoint := sourceShading.subset_body index hpoint.1

theorem pureWZ2HorizontalPopularPullbackShading_subshading
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    ∀ index,
      (pureWZ2HorizontalPopularPullbackShading raw popular).carrier index ⊆
        sourceShading.carrier index :=
  fun _ _ hpoint => hpoint.1

/-- Local grains restricted to the pulled-back horizontal box. -/
def PureWZ2LocalGrainData.horizontalPopularPullback
    {sourceDelta targetDelta c d m width sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    PureWZ2LocalGrainData
      (pureWZ2HorizontalPopularPullbackShading raw popular) sigma C :=
  sourceLocal.restrict
    (pureWZ2HorizontalPopularPullbackShading_subshading raw popular)

/-- Global grains restricted to the pulled-back horizontal box. -/
def PureWZ2C2GlobalGrainData.horizontalPopularPullback
    {sourceDelta targetDelta c d m width sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (sourceGlobal : PureWZ2C2GlobalGrainData sourceShading sigma C)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    PureWZ2C2GlobalGrainData
      (pureWZ2HorizontalPopularPullbackShading raw popular) sigma C :=
  sourceGlobal.restrict_same_constant
    (pureWZ2HorizontalPopularPullbackShading_subshading raw popular)

/-- The exact triangular image of the pullback carrier is the selected target
carrier. -/
theorem pureWZ2HorizontalPopularPullbackShading_image
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width)
    (index : Fin sourceFamily.card) :
    anisotropicCenteredRescalingMap g c d m anisotropicCenter ''
        (pureWZ2HorizontalPopularPullbackShading raw popular).carrier index =
      popular.restricted.carrier index := by
  let affine := anisotropicCenteredRescalingAffineEquiv
    g c d m anisotropicCenter hcd hm
  rw [popular.restricted_carrier]
  change anisotropicCenteredRescalingMap g c d m anisotropicCenter ''
      (sourceShading.carrier index ∩ affine ⁻¹' popular.box) =
    (raw.exactShading.carrier index ∩ popular.box)
  rw [raw.exactShading_carrier]
  ext point
  constructor
  · rintro ⟨source, ⟨hsource, hbox⟩, rfl⟩
    refine ⟨⟨source, hsource, rfl⟩, ?_⟩
    change affine source ∈ popular.box at hbox
    rw [anisotropicCenteredRescalingAffineEquiv_apply] at hbox
    exact hbox
  · rintro ⟨⟨source, hsource, hsourcePoint⟩, hbox⟩
    subst point
    refine ⟨source, ⟨hsource, ?_⟩, rfl⟩
    change affine source ∈ popular.box
    rw [anisotropicCenteredRescalingAffineEquiv_apply]
    exact hbox

/-- Exact triangular Jacobian identity for the pulled-back horizontal box. -/
theorem pureWZ2HorizontalPopularPullbackShading_mass
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    popular.restricted.mass = ENNReal.ofReal m *
      (pureWZ2HorizontalPopularPullbackShading raw popular).mass := by
  change (∑ index, volume (popular.restricted.carrier index)) =
    ENNReal.ofReal m * ∑ index, volume
      ((pureWZ2HorizontalPopularPullbackShading raw popular).carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [← pureWZ2HorizontalPopularPullbackShading_image raw popular index]
  exact volume_image_anisotropicCenteredRescalingMap g hcd hm
    anisotropicCenter _
    ((pureWZ2HorizontalPopularPullbackShading raw popular).measurable_carrier
      index)

/-- The source subfamily obtained by deleting the empty pullback carriers. -/
def pureWZ2HorizontalPopularPullbackSourceSubfamily
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    Kakeya.Streamlined.TubeSubfamily sourceFamily :=
  wz2PaperNonemptyCarrierSubfamily
    (pureWZ2HorizontalPopularPullbackShading raw popular)

/-- Explicit cardinality-retention factor for deleting the empty horizontal
pullback carriers. -/
def pureWZ2HorizontalPopularPullbackCardinalityLoss
    (sourceDelta width : ℝ) (sourceNormalization : ENNReal) : ENNReal :=
  (ENNReal.ofReal (width ^ 2 / 9) * sourceNormalization)⁻¹ *
    (55296 * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN sourceDelta 2)

/-- The pullback shading after deleting exactly its empty carriers. -/
def pureWZ2HorizontalPopularPullbackNonemptyShading
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    WZ1PaperTubeShading
      (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).family :=
  wz2PaperNonemptyCarrierShading
    (pureWZ2HorizontalPopularPullbackShading raw popular)

@[simp] theorem pureWZ2HorizontalPopularPullbackNonemptyShading_carrier
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width)
    (index : Fin
      (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).family.card) :
    (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).carrier index =
      (pureWZ2HorizontalPopularPullbackShading raw popular).carrier
        ((pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).embedding
          index) :=
  rfl

/-- Every retained pullback tube has an actual source point in the selected
horizontal box. -/
theorem pureWZ2HorizontalPopularPullbackNonemptyShading_carrier_nonempty
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    ∀ index,
      ((pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).carrier
        index).Nonempty := by
  intro index
  have hmem :
      (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).embedding
          index ∈
        wz2PaperNonemptyCarrierIndices
          (pureWZ2HorizontalPopularPullbackShading raw popular) :=
    Finset.orderEmbOfFin_mem
      (wz2PaperNonemptyCarrierIndices
        (pureWZ2HorizontalPopularPullbackShading raw popular)) rfl index
  exact (Finset.mem_filter.mp hmem).2

/-- Removing empty pullback carriers preserves the exact shaded mass. -/
theorem pureWZ2HorizontalPopularPullbackNonemptyShading_mass
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).mass =
      (pureWZ2HorizontalPopularPullbackShading raw popular).mass := by
  unfold pureWZ2HorizontalPopularPullbackNonemptyShading
    wz2PaperNonemptyCarrierShading
    pureWZ2HorizontalPopularPullbackSourceSubfamily
    wz2PaperNonemptyCarrierSubfamily
  rw [restrictPaperShading_fromFinset_mass]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro index _ hindex
  have hempty :
      (pureWZ2HorizontalPopularPullbackShading raw popular).carrier index = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp fun hnonempty =>
      hindex (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonempty⟩)
  simp [hempty]

/-- Pulling a horizontal popular box back through the triangular map retains
the full two-dimensional popular-box mass fraction. -/
theorem pureWZ2HorizontalPopularPullbackShading_mass_lower
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    ENNReal.ofReal (width ^ 2 / 9) * sourceShading.mass ≤
      (pureWZ2HorizontalPopularPullbackShading raw popular).mass := by
  have hmZero : ENNReal.ofReal m ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hm).ne'
  have hmTop : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hscaled : ENNReal.ofReal m *
      (ENNReal.ofReal (width ^ 2 / 9) * sourceShading.mass) ≤
    ENNReal.ofReal m *
      (pureWZ2HorizontalPopularPullbackShading raw popular).mass := by
    calc
      ENNReal.ofReal m *
          (ENNReal.ofReal (width ^ 2 / 9) * sourceShading.mass) =
        ENNReal.ofReal (width ^ 2 / 9) * raw.exactShading.mass := by
          rw [raw.exactShading_mass]
          ring
      _ ≤ popular.restricted.mass := popular.mass_lower
      _ = ENNReal.ofReal m *
          (pureWZ2HorizontalPopularPullbackShading raw popular).mass :=
        pureWZ2HorizontalPopularPullbackShading_mass raw popular
  apply (ENNReal.mul_le_mul_iff_right hmZero hmTop).mp
  simpa [mul_comm] using hscaled

/-- Pulling a horizontal popular box back through the triangular map and
deleting empty carriers retains the full two-dimensional popular-box mass
fraction.  The triangular Jacobian cancels from the two exact mass
identities. -/
theorem pureWZ2HorizontalPopularPullbackNonemptyShading_mass_lower
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    ENNReal.ofReal (width ^ 2 / 9) * sourceShading.mass ≤
      (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).mass := by
  rw [pureWZ2HorizontalPopularPullbackNonemptyShading_mass]
  exact pureWZ2HorizontalPopularPullbackShading_mass_lower raw popular

/-- The two-dimensional popular-box mass and the quadratic paper-carrier
upper bound force quantitative source-cardinality retention after deleting
empty pullbacks. -/
theorem pureWZ2HorizontalPopularPullback_cardinality_retention
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaSmall : sourceDelta ≤ 1 / 24)
    (hwidth : 0 < width)
    (sourceNormalization : ENNReal)
    (hsourceNormalizationZero : sourceNormalization ≠ 0)
    (hsourceNormalizationTop : sourceNormalization ≠ ⊤)
    (hsourceMass :
      sourceNormalization * sourceFamily.enncard ≤ sourceShading.mass)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily) :
    sourceFamily.enncard ≤
      pureWZ2HorizontalPopularPullbackCardinalityLoss
        sourceDelta width sourceNormalization *
        (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).family.enncard := by
  let selected := pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular
  let factor : ENNReal :=
    ENNReal.ofReal (width ^ 2 / 9) * sourceNormalization
  let upper : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN sourceDelta 2
  have hfactorZero : factor ≠ 0 := by
    dsimp only [factor]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      hsourceNormalizationZero
  have hfactorTop : factor ≠ ⊤ := by
    dsimp only [factor]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsourceNormalizationTop
  have hselectedMassUpper :
      (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).mass ≤
        upper * selected.family.enncard := by
    have hraw := wz2_paper_shading_mass_upper hsourceDelta
      hsourceDeltaSmall (hsourceLine.subfamily selected)
      (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular)
    exact hraw.trans_eq <| by simp [selected, upper, mul_assoc, mul_left_comm]
  have hmassLower : ENNReal.ofReal (width ^ 2 / 9) * sourceShading.mass ≤
      (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).mass :=
    pureWZ2HorizontalPopularPullbackNonemptyShading_mass_lower raw popular
  have hweighted : factor * sourceFamily.enncard ≤
      upper * selected.family.enncard := by
    calc
      factor * sourceFamily.enncard =
          ENNReal.ofReal (width ^ 2 / 9) *
            (sourceNormalization * sourceFamily.enncard) := by
        simp [factor, mul_assoc]
      _ ≤ ENNReal.ofReal (width ^ 2 / 9) *
          sourceShading.mass := by gcongr
      _ ≤ (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).mass :=
        hmassLower
      _ ≤ upper * selected.family.enncard := hselectedMassUpper
  have hcancel : sourceFamily.enncard ≤
      factor⁻¹ * (upper * selected.family.enncard) := by
    calc
      sourceFamily.enncard =
          factor⁻¹ * (factor * sourceFamily.enncard) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hfactorZero hfactorTop, one_mul]
      _ ≤ factor⁻¹ * (upper * selected.family.enncard) := by gcongr
  simpa [selected, pureWZ2HorizontalPopularPullbackCardinalityLoss, factor,
    upper, mul_assoc] using hcancel

/-- The selected triangular carrier over a retained source index is still
the exact image of the retained pullback carrier. -/
theorem pureWZ2HorizontalPopularPullbackNonemptyShading_image
    {sourceDelta targetDelta c d m width : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width)
    (index : Fin
      (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).family.card) :
    anisotropicCenteredRescalingMap g c d m anisotropicCenter ''
        (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular).carrier
          index =
      popular.restricted.carrier
        ((pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular).embedding
          index) := by
  rw [pureWZ2HorizontalPopularPullbackNonemptyShading_carrier]
  exact pureWZ2HorizontalPopularPullbackShading_image raw popular _

/-- Restrict local grains to the nonempty horizontal pullback family. -/
def PureWZ2LocalGrainData.horizontalPopularNonemptyPullback
    {sourceDelta targetDelta c d m width sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    PureWZ2LocalGrainData
      (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular) sigma C :=
  (sourceLocal.horizontalPopularPullback raw popular).subfamily
    (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular)

/-- Restrict global grains to the same nonempty horizontal pullback family. -/
def PureWZ2C2GlobalGrainData.horizontalPopularNonemptyPullback
    {sourceDelta targetDelta c d m width sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm)
    (sourceGlobal : PureWZ2C2GlobalGrainData sourceShading sigma C)
    (popular : PureWZ2HorizontalPopularBoxData raw.exactShading width) :
    PureWZ2C2GlobalGrainData
      (pureWZ2HorizontalPopularPullbackNonemptyShading raw popular) sigma C :=
  (sourceGlobal.horizontalPopularPullback raw popular).subfamily
    (pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular)

end Kakeya.Assouad

end
