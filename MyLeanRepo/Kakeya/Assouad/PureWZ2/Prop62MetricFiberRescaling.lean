import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberDescendantScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CWARescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62RescaledTopScale
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex

/-!
# Proposition 6.2 metric fibers: public rescaled nearby CWA

This record contains exactly the geometric inputs used in the paper after the
inserted metric-parent level:

* the physical metric fiber has pure nearby CWA from the old descendant
  schedule plus the inserted singleton range;
* every physical tube is covered by the metric parent in the Section 6 line
  metric;
* the source and the canonical nearby witnesses selected by its own CWA have
  the fixed separation and nested-localization geometry required by the
  literal rescaling theorem.

No arbitrary selected subfiber is substituted for the genuine metric fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62MetricFiberRescalingInput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card)
    (sourceConstant : ENNReal) where
  rho_pos : 0 < rho
  rho_le_one : rho ≤ 1
  delta_pos : 0 < delta
  scale_separation : 100 * delta ≤ rho
  sourceIndices : Finset (Fin fine.card)
  sourceIndices_eq :
    sourceIndices =
      wz2PaperFullFiberIndices fine coarse parent
  sourceIndices_nonempty : sourceIndices.Nonempty
  sourceFamily :
    Kakeya.Streamlined.TubeFamily delta
  sourceEquiv :
    Fin sourceFamily.card ≃ sourceIndices
  source_tube_eq :
    ∀ index,
      sourceFamily.tube index =
        fine.tube (sourceEquiv index).1
  source_line_class :
    WZ1PaperIsLineClass sourceFamily
  anchor_line_class :
    WZ1PaperTubeInLineClass (coarse.tube parent)
  source_covered :
    ∀ index,
      WZ1PaperTubeCovers
        (sourceFamily.tube index) (coarse.tube parent)
  source_strongly_separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          (sourceFamily.tube first)
          (sourceFamily.tube second)
  source_constant_finite :
    WZ2PaperFiniteErrorConstant sourceConstant
  target_locality :
    ∀ index,
      ‖wz2PaperTubeMidpoint
        ((wz2PaperLiteralOrdinaryRescaledFamily
          sourceFamily (coarse.tube parent) rho_pos).tube index)‖ ≤ 3
  rescaled_physical_cwa :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperLiteralOrdinaryRescaledFamily
        sourceFamily (coarse.tube parent) rho_pos).toBodyFamily
      sourceConstant
  requested_route :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ (actual : ℝ)
        (scaleData :
          WZ2PaperPureScaleCoverData
            sourceFamily actual sourceConstant),
          100 * delta ≤ actual ∧
          actual ≤ rho ∧
          requested.1 ≤ actual / rho ∧
          ENNReal.ofReal (actual / rho) <
            ((81000000 : ENNReal) * sourceConstant) *
              ENNReal.ofReal requested.1 ∧
          WZ1PaperIsLineClass scaleData.coarse ∧
          (∀ source,
            WZ1PaperTubeCovers
              (sourceFamily.tube source)
              (scaleData.coarse.tube
                (scaleData.cover.parent source))) ∧
          (∀ middle,
            WZ2PaperDilatedTubeCovers 2
              (scaleData.coarse.tube middle)
              (coarse.tube parent)) ∧
          (∀ first second, first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * actual <
              wz1PaperLineDistance
                (scaleData.coarse.tube first)
                (scaleData.coarse.tube second)) ∧
          WZ2PaperOrdinaryNestedTargetLocalization
            sourceFamily scaleData.coarse
            (coarse.tube parent) rho_pos) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal requested.1

namespace PureWZ2Prop62MetricFiberRescalingInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant)

noncomputable def literal :
    WZ2PaperLiteralUnitRescaledFamilyData
      input.sourceFamily (coarse.tube parent) input.rho_pos :=
  wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
    input.rho_pos input.rho_le_one
    input.sourceFamily (coarse.tube parent)
    input.source_line_class input.anchor_line_class input.source_covered

noncomputable def certificate :
    WZ2PaperAssouadToLiteralRescalingCertificate
      input.rho_pos
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (coarse.tube parent) input.rho_pos)
      input.literal 4000000 :=
  wz2PaperLiteralOrdinaryRescaledFamilyCertificate
    input.delta_pos input.rho_pos input.rho_le_one
    input.sourceFamily (coarse.tube parent)
    input.source_line_class input.anchor_line_class input.source_covered

theorem publicPureCWA :
    WZ2PaperPureCWAAtNearbyScales
      input.certificate.publicFamily
      ((81000000 : ENNReal) * sourceConstant) := by
  let canonicalFamily :=
    wz2PaperLiteralOrdinaryRescaledFamily
      input.sourceFamily (coarse.tube parent) input.rho_pos
  have canonical :
      WZ2PaperPureCWAAtNearbyScales
        canonicalFamily
        ((81000000 : ENNReal) * sourceConstant) :=
    by
      let targetConstant : ENNReal :=
        (81000000 : ENNReal) * sourceConstant
      have targetFinite :
          WZ2PaperFiniteErrorConstant targetConstant := by
        constructor
        · calc
            (1 : ENNReal) ≤ 81000000 := by norm_num
            _ = 81000000 * 1 := by simp
            _ ≤ 81000000 * sourceConstant := by
              gcongr
              exact input.source_constant_finite.1
        · exact ENNReal.mul_ne_top
            (by norm_num) input.source_constant_finite.2
      have targetDistinct :
          WZ2PaperOrdinaryIsEssentiallyDistinct canonicalFamily :=
        wz2PaperOrdinaryRescaled_essentiallyDistinct_of_locality
          input.rho_pos input.rho_le_one input.delta_pos
          input.scale_separation input.source_line_class
          input.anchor_line_class input.source_covered
          input.source_strongly_separated input.target_locality
      refine
        ⟨div_pos input.delta_pos input.rho_pos,
          targetFinite, targetDistinct, ?_⟩
      intro requested
      rcases input.requested_route requested with nested | topWindow
      · rcases nested with
          ⟨actual, scaleData, treeSafe, actualLe,
            requestedLe, within, middleLine, fineMiddle,
            middleAnchor, middleSeparated, localization⟩
        let raw :=
          wz2PaperPureScaleCoverData.ordinaryNestedScale
            scaleData input.rho_pos treeSafe actualLe
            input.rho_le_one (coarse.tube parent)
            input.source_line_class middleLine input.anchor_line_class
            fineMiddle input.source_covered middleAnchor
            middleSeparated localization
        have constantEq :
            max sourceConstant targetConstant = targetConstant :=
          wz2PaperPureScaleCoverData_max_eq
            input.source_constant_finite.1
        let scaleData' :
            WZ2PaperPureScaleCoverData
              canonicalFamily (actual / rho) targetConstant :=
          constantEq ▸ raw
        exact ⟨actual / rho, requestedLe, within, scaleData'⟩
      · have sourceNonempty : input.sourceFamily.Nonempty := by
          change 0 < input.sourceFamily.card
          have sourceIndicesPos : 0 < input.sourceIndices.card :=
            Finset.card_pos.mpr input.sourceIndices_nonempty
          have cardEq :
              input.sourceFamily.card = input.sourceIndices.card := by
            simpa using Fintype.card_congr input.sourceEquiv
          rwa [cardEq]
        have targetScaleLe : delta / rho ≤ 1 / 100 := by
          apply (div_le_iff₀ input.rho_pos).2
          nlinarith [input.scale_separation]
        rcases
            pureWZ2_prop62_rescaled_topScale
              (div_pos input.delta_pos input.rho_pos)
              targetScaleLe sourceNonempty input.target_locality
              input.rescaled_physical_cwa
              input.source_constant_finite.1
          with ⟨topScale⟩
        exact
          ⟨4, requested.2.2.trans (by norm_num),
            by simpa using topWindow, topScale⟩
  have publicEq :
      input.certificate.publicFamily =
        wz2PaperLiteralOrdinaryRescaledFamily
          input.sourceFamily (coarse.tube parent) input.rho_pos := by
    rfl
  exact publicEq ▸ canonical

/-- Enlarge the source CWA constant without changing the metric fiber. -/
noncomputable def mono
    {secondConstant : ENNReal}
    (constantLe : sourceConstant ≤ secondConstant)
    (secondFinite : WZ2PaperFiniteErrorConstant secondConstant) :
    PureWZ2Prop62MetricFiberRescalingInput
      cover parent secondConstant where
  rho_pos := input.rho_pos
  rho_le_one := input.rho_le_one
  delta_pos := input.delta_pos
  scale_separation := input.scale_separation
  sourceIndices := input.sourceIndices
  sourceIndices_eq := input.sourceIndices_eq
  sourceIndices_nonempty := input.sourceIndices_nonempty
  sourceFamily := input.sourceFamily
  sourceEquiv := input.sourceEquiv
  source_tube_eq := input.source_tube_eq
  source_line_class := input.source_line_class
  anchor_line_class := input.anchor_line_class
  source_covered := input.source_covered
  source_strongly_separated := input.source_strongly_separated
  source_constant_finite := secondFinite
  target_locality := input.target_locality
  rescaled_physical_cwa := by
    intro convexSet convex
    exact (input.rescaled_physical_cwa convexSet convex).trans <| by
      gcongr
  requested_route := by
    intro requested
    rcases input.requested_route requested with descendant | top
    · rcases descendant with
        ⟨actual, scaleData, actualLower, actualUpper, requestedLe,
          window, middleLine, fineMiddle, middleAnchor,
          middleSeparated, localization⟩
      exact Or.inl
        ⟨actual, scaleData.mono constantLe, actualLower, actualUpper,
          requestedLe, window.trans_le (by gcongr), middleLine,
          fineMiddle, middleAnchor, middleSeparated, localization⟩
    · exact Or.inr <| top.trans_le <| by gcongr

end PureWZ2Prop62MetricFiberRescalingInput

structure PureWZ2Prop62PublicRescalingReindexData
    {delta rho : ℝ}
    (targetFamily : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube rho)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (targetLine : WZ1PaperIsLineClass targetFamily)
    (anchorLine : WZ1PaperTubeInLineClass anchor)
    (targetCovered :
      ∀ index, WZ1PaperTubeCovers (targetFamily.tube index) anchor)
    (sourceConstant : ENNReal) where
  ambientFine : Kakeya.Streamlined.TubeFamily delta
  ambientCoarse : Kakeya.Streamlined.TubeFamily rho
  ambientCover : PureWZ2Section6Cover ambientFine ambientCoarse
  ambientParent : Fin ambientCoarse.card
  anchor_eq : ambientCoarse.tube ambientParent = anchor
  input :
    PureWZ2Prop62MetricFiberRescalingInput
      ambientCover ambientParent sourceConstant
  indexEquiv : Fin targetFamily.card ≃ Fin input.sourceFamily.card
  tube_eq :
    ∀ index,
      targetFamily.tube index =
        input.sourceFamily.tube (indexEquiv index)

namespace PureWZ2Prop62PublicRescalingReindexData

variable
    {delta rho : ℝ}
    {targetFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {rhoPos : 0 < rho}
    {rhoLeOne : rho ≤ 1}
    {targetLine : WZ1PaperIsLineClass targetFamily}
    {anchorLine : WZ1PaperTubeInLineClass anchor}
    {targetCovered :
      ∀ index, WZ1PaperTubeCovers (targetFamily.tube index) anchor}
    {sourceConstant : ENNReal}
    (data :
      PureWZ2Prop62PublicRescalingReindexData
        targetFamily anchor rhoPos rhoLeOne
        targetLine anchorLine targetCovered sourceConstant)

noncomputable def targetCertificate :
    WZ2PaperAssouadToLiteralRescalingCertificate
      rhoPos
      (WZ2PaperAssouadUnitRescalingData.ofTube anchor rhoPos)
      (wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
        rhoPos rhoLeOne targetFamily anchor
        targetLine anchorLine targetCovered)
      4000000 :=
  wz2PaperLiteralOrdinaryRescaledFamilyCertificate
    data.input.delta_pos rhoPos rhoLeOne
    targetFamily anchor targetLine anchorLine targetCovered

theorem publicPureCWA :
    WZ2PaperPureCWAAtNearbyScales
      data.targetCertificate.publicFamily
      ((81000000 : ENNReal) * sourceConstant) := by
  have sourceCWA := data.input.publicPureCWA
  have sourceAnchor :
      data.ambientCoarse.tube data.ambientParent = anchor :=
    data.anchor_eq
  have reindexed :
      WZ2PaperPureCWAAtNearbyScales
        (wz2PaperLiteralOrdinaryRescaledFamily
          targetFamily anchor rhoPos)
        ((81000000 : ENNReal) * sourceConstant) := by
    have sourceCanonical :
        WZ2PaperPureCWAAtNearbyScales
          (wz2PaperLiteralOrdinaryRescaledFamily
            data.input.sourceFamily
            (data.ambientCoarse.tube data.ambientParent)
            data.input.rho_pos)
          ((81000000 : ENNReal) * sourceConstant) := by
      have sourceEq :
          data.input.certificate.publicFamily =
            wz2PaperLiteralOrdinaryRescaledFamily
              data.input.sourceFamily
              (data.ambientCoarse.tube data.ambientParent)
              data.input.rho_pos := by
        rfl
      rw [sourceEq] at sourceCWA
      exact sourceCWA
    let publicEquiv :
        Fin
            (wz2PaperLiteralOrdinaryRescaledFamily
              targetFamily anchor rhoPos).card ≃
          Fin
            (wz2PaperLiteralOrdinaryRescaledFamily
              data.input.sourceFamily
              (data.ambientCoarse.tube data.ambientParent)
              data.input.rho_pos).card :=
      data.indexEquiv
    apply sourceCanonical.reindex publicEquiv
    intro index
    change
      wz2PaperLiteralOrdinaryRescaledTube
          (targetFamily.tube index) anchor rhoPos =
        wz2PaperLiteralOrdinaryRescaledTube
          (data.input.sourceFamily.tube (data.indexEquiv index))
          (data.ambientCoarse.tube data.ambientParent)
          data.input.rho_pos
    rw [data.tube_eq index, sourceAnchor]
  exact reindexed

end PureWZ2Prop62PublicRescalingReindexData

end Kakeya.Assouad

end
