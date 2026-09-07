import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64GeometricEDProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CubicalVolumeUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity

/-!
# Legacy Proposition 6.4 critical-floor compatibility

This module retains the older optional critical-floor wrapper and its reusable
mass lemmas.  Node 5's production output does not require a final union-volume
lower bound: final extremality now receives nonemptiness directly from the
same weighted essentially-distinct selection.  The wrapper below therefore
serves compatibility callers only.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    {output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}

/-- The normalized hierarchy has positive indexed mass. -/
theorem hierarchy_mass_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    0 < output.hierarchy.shading.mass := by
  have hunionPos : 0 < volume output.hierarchy.shading.union :=
    (by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
        Real.rpow_pos_of_pos output.source.extremal.delta_pos] :
          0 < Kakeya.realRpowENN sourceDelta
            (sigma + workLoss)).trans_le
      output.hierarchy.volume_lower
  have hunionMass : volume output.hierarchy.shading.union ≤
      output.hierarchy.shading.mass := by
    have hunionEq : output.hierarchy.shading.union =
        ⋃ index : Fin output.source.family.card,
          output.hierarchy.shading.carrier index := by
      ext point
      simp [Kakeya.Streamlined.Shading.union]
      rfl
    rw [hunionEq]
    exact MeasureTheory.measure_iUnion_fintype_le
      MeasureTheory.volume output.hierarchy.shading.carrier
  exact hunionPos.trans_le hunionMass

/-- The mass-heavy short slab has positive indexed mass. -/
theorem slab_mass_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    0 < output.prepared.slab.shading.mass := by
  have hcoefficient : 0 < ENNReal.ofReal
      (2 * output.prepared.slab.halfHeight) := by
    apply ENNReal.ofReal_pos.mpr
    nlinarith [output.prepared.slab.halfHeight_pos]
  have hleft : 0 < ENNReal.ofReal
        (2 * output.prepared.slab.halfHeight) *
      output.hierarchy.shading.mass :=
    ENNReal.mul_pos hcoefficient.ne' geometry.hierarchy_mass_pos.ne'
  have hright : 0 < 3 * output.prepared.slab.shading.mass :=
    hleft.trans_le output.prepared.slab.mass_fraction
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  simp [hzero] at hright

/-- The indexed mass of the selected common-window shading is the literal sum
over the selected ambient indices. -/
theorem selectedShading_mass
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    geometry.selectedShading.mass =
      ∑ index ∈ geometry.common.selected,
        volume (output.prepared.slab.shading.carrier index) := by
  rw [restrictPaperShading_mass]
  let equivalence := geometry.common.selected.orderIsoOfFin rfl
  calc
    (∑ index : Fin geometry.selectedSource.family.card,
        volume (output.prepared.slab.shading.carrier
          (geometry.selectedSource.embedding index))) =
        ∑ index : geometry.common.selected,
          volume (output.prepared.slab.shading.carrier index.1) :=
      Equiv.sum_comp equivalence.toEquiv
        (fun index : geometry.common.selected =>
          volume (output.prepared.slab.shading.carrier index.1))
    _ = ∑ index ∈ geometry.common.selected,
        volume (output.prepared.slab.shading.carrier index) := by
      simpa using Finset.sum_attach geometry.common.selected
        (fun index => volume
          (output.prepared.slab.shading.carrier index))

/-- The common-window subfamily selected from the short slab is nonempty in
indexed mass. -/
theorem selectedShading_mass_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    0 < geometry.selectedShading.mass := by
  have hright : 0 < 49 * geometry.selectedShading.mass := by
    rw [geometry.selectedShading_mass]
    exact geometry.slab_mass_pos.trans_le geometry.common.retained_mass
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  simp [hzero] at hright

/-- Exact affine Jacobian on the selected common-window shading. -/
theorem exactShading_mass
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    geometry.exactShading.mass =
      ENNReal.ofReal
          (1 / (output.prepared.normalization *
            output.prepared.slab.halfHeight)) *
        geometry.selectedShading.mass := by
  change (pureWZ2Proposition64ExactImageShading
    output.source.extremal.delta_pos
    output.prepared.restrictedRaw.slope output.prepared.slab.center
    output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
    output.prepared.normalization geometry.common.translation
    output.prepared.slab.halfHeight_pos output.normalization_nine
    output.prepared.normalized.anchor_value_bound geometry.scales.image_radius
    geometry.selectedSource.family geometry.selectedShading
    (output.source.line_class.subfamily geometry.selectedSource)
    (geometry.common.image_mem_axisBox output.source.extremal.delta_pos
      geometry.scales.sourceDelta_small
      output.prepared.slab.halfHeight_pos
      (by linarith [output.halfHeight_small]) output.normalization_nine
      output.prepared.normalized.anchor_value_bound output.source.line_class
      output.prepared.shading_subset_shortSlab)).mass = _
  exact pureWZ2Proposition64ExactImageShading_mass

/-- The exact affine image has positive indexed mass. -/
theorem exactShading_mass_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    0 < geometry.exactShading.mass := by
  rw [geometry.exactShading_mass]
  apply ENNReal.mul_pos
  · apply (ENNReal.ofReal_pos.mpr ?_).ne'
    have hnormalizationPos : 0 < output.prepared.normalization :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9)
        output.normalization_nine
    exact one_div_pos.mpr
      (mul_pos hnormalizationPos output.prepared.slab.halfHeight_pos)
  · exact geometry.selectedShading_mass_pos.ne'

/-- The popular-box restriction has positive indexed mass. -/
theorem popular_mass_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    0 < geometry.cleanup.popular.restricted.mass := by
  have hcoefficient : 0 < ENNReal.ofReal
      (pureWZ2Proposition64Lemma35Width ^ 3 / 27) := by
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (pow_pos geometry.scales.width_pos _) (by norm_num)
  exact
    (ENNReal.mul_pos hcoefficient.ne' geometry.exactShading_mass_pos.ne').trans_le
      geometry.cleanup.popular.mass_lower

/-- Isotropic cubical saturation retains the exact image mass with the cubic
Jacobian of the fixed similarity. -/
theorem cleanup_finalShading_mass_lower
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        geometry.cleanup.popular.restricted.mass ≤
      geometry.cleanup.finalShading.mass := by
  change ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
      geometry.cleanup.popular.restricted.mass ≤
    (pureWZ2Proposition64FullIsotropicPaperShading
      geometry.cleanup.popular.restricted geometry.cleanup.popular.center
      pureWZ2Proposition64Lemma35Scale geometry.scales.imageDelta_pos
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      geometry.scales.scale_one geometry.scales.retube_radius
      geometry.cleanup.sourceWindow).mass
  exact pureWZ2Proposition64FullIsotropicPaperShading_mass_lower
    geometry.cleanup.popular.restricted geometry.cleanup.popular.center
    pureWZ2Proposition64Lemma35Scale_pos geometry.scales.imageDelta_pos
    geometry.scales.finalDelta_pos
    (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
    geometry.scales.scale_one geometry.scales.retube_radius
    geometry.cleanup.sourceWindow

/-- The full cubical saturation used before ED selection has positive indexed
mass. -/
theorem cleanup_finalShading_mass_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    0 < geometry.cleanup.finalShading.mass := by
  have hcoefficient : 0 < ENNReal.ofReal
      (pureWZ2Proposition64Lemma35Scale ^ 3) := by
    apply ENNReal.ofReal_pos.mpr
    exact pow_pos pureWZ2Proposition64Lemma35Scale_pos _
  exact
    (ENNReal.mul_pos hcoefficient.ne' geometry.popular_mass_pos.ne').trans_le
      geometry.cleanup_finalShading_mass_lower

/-- Weighted ED selection from the geometric prefix has a genuinely nonempty
final indexed family. -/
theorem paperED_family_nonempty
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    ed.subfamily.family.Nonempty := by
  have hfinalMassPos : 0 < ed.finalShading.mass := by
    have hright : 0 < (K + 1) * ed.finalShading.mass :=
      geometry.cleanup_finalShading_mass_pos.trans_le ed.mass_retention
    by_contra hzero
    rw [not_lt, nonpos_iff_eq_zero] at hzero
    simp [hzero] at hright
  by_contra hempty
  have hcard : ed.subfamily.family.card = 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hempty
  have hmassZero : ed.finalShading.mass = 0 := by
    change (∑ index : Fin ed.subfamily.family.card,
      volume (ed.finalShading.carrier index)) = 0
    apply Finset.sum_eq_zero
    intro index _
    exact Fin.elim0 (Fin.cast hcard index)
  rw [hmassZero] at hfinalMassPos
  exact (lt_irrefl 0 hfinalMassPos)

/-- The complete indexed-mass ledger through short-slab selection, the common
window, the exact affine Jacobian, popular-box restriction, isotropic
dilation, and weighted ED selection.  The product form avoids every unsafe
division by a runtime mass or cardinality. -/
theorem paperED_mass_ledger
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        (ENNReal.ofReal
            (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
          (ENNReal.ofReal
              (1 / (output.prepared.normalization *
                output.prepared.slab.halfHeight)) *
            (ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
              output.hierarchy.shading.mass))) ≤
      147 * (K + 1) * ed.finalShading.mass := by
  have hselected :
      ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          output.hierarchy.shading.mass ≤
        147 * geometry.selectedShading.mass := by
    calc
      ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          output.hierarchy.shading.mass ≤
        3 * output.prepared.slab.shading.mass :=
          output.prepared.slab.mass_fraction
      _ ≤ 3 * (49 * geometry.selectedShading.mass) := by
        gcongr
        rw [geometry.selectedShading_mass]
        exact geometry.common.retained_mass
      _ = 147 * geometry.selectedShading.mass := by ring
  have hexact :
      ENNReal.ofReal
          (1 / (output.prepared.normalization *
            output.prepared.slab.halfHeight)) *
        (ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          output.hierarchy.shading.mass) ≤
      147 * geometry.exactShading.mass := by
    calc
      _ ≤ ENNReal.ofReal
          (1 / (output.prepared.normalization *
            output.prepared.slab.halfHeight)) *
          (147 * geometry.selectedShading.mass) := by gcongr
      _ = 147 *
          (ENNReal.ofReal
            (1 / (output.prepared.normalization *
              output.prepared.slab.halfHeight)) *
            geometry.selectedShading.mass) := by ring
      _ = 147 * geometry.exactShading.mass := by
        rw [geometry.exactShading_mass]
  have hpopular :
      ENNReal.ofReal
          (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
        (ENNReal.ofReal
            (1 / (output.prepared.normalization *
              output.prepared.slab.halfHeight)) *
          (ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
            output.hierarchy.shading.mass)) ≤
      147 * geometry.cleanup.popular.restricted.mass := by
    calc
      _ ≤ ENNReal.ofReal
          (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
            (147 * geometry.exactShading.mass) := by gcongr
      _ = 147 *
          (ENNReal.ofReal
            (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
              geometry.exactShading.mass) := by ring
      _ ≤ 147 * geometry.cleanup.popular.restricted.mass := by
        gcongr
        exact geometry.cleanup.popular.mass_lower
  calc
    _ ≤ ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        (147 * geometry.cleanup.popular.restricted.mass) := by gcongr
    _ = 147 *
        (ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
          geometry.cleanup.popular.restricted.mass) := by ring
    _ ≤ 147 * geometry.cleanup.finalShading.mass :=
      mul_le_mul_left' geometry.cleanup_finalShading_mass_lower 147
    _ ≤ 147 * ((K + 1) * ed.finalShading.mass) :=
      mul_le_mul_left' ed.mass_retention 147
    _ = 147 * (K + 1) * ed.finalShading.mass := by ring

/-- Product of all deterministic density-retention factors before the final
source body mass. -/
noncomputable def pureWZ2Proposition64QuantitativeMassCoefficient
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta) : ENNReal :=
  ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
    (ENNReal.ofReal (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
      (ENNReal.ofReal
          (1 / (quantitativeOutput.normalized.prepared.normalization *
            quantitativeOutput.normalized.prepared.slab.halfHeight)) *
        (ENNReal.ofReal
            (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
          (ENNReal.ofReal (1 / 6) *
            Kakeya.realRpowENN sourceDelta quantitativeOutput.densityLoss))))

/-- Source-family form of the final indexed-mass ledger.  This is the exact
quantitative receipt carried from R3 into the R4 geometry. -/
theorem paperED_quantitative_mass_ledger
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass ≤
      147 * (K + 1) * ed.finalShading.mass := by
  unfold pureWZ2Proposition64QuantitativeMassCoefficient
  have hgroup :
      (ENNReal.ofReal
          (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
        (ENNReal.ofReal (1 / 6) *
          Kakeya.realRpowENN sourceDelta quantitativeOutput.densityLoss)) *
          (wz1PaperBodyFamily
            quantitativeOutput.normalized.source.family).mass =
      ENNReal.ofReal
          (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
        (ENNReal.ofReal (1 / 6) *
          (Kakeya.realRpowENN sourceDelta quantitativeOutput.densityLoss *
            (wz1PaperBodyFamily
              quantitativeOutput.normalized.source.family).mass)) := by ring
  calc
    ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
          (ENNReal.ofReal
              (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
            (ENNReal.ofReal
                (1 / (quantitativeOutput.normalized.prepared.normalization *
                  quantitativeOutput.normalized.prepared.slab.halfHeight)) *
              (ENNReal.ofReal
                  (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
                (ENNReal.ofReal (1 / 6) *
                  Kakeya.realRpowENN sourceDelta
                    quantitativeOutput.densityLoss)))) *
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass =
      ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
          (ENNReal.ofReal
              (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
            (ENNReal.ofReal
                (1 / (quantitativeOutput.normalized.prepared.normalization *
                  quantitativeOutput.normalized.prepared.slab.halfHeight)) *
              (ENNReal.ofReal
                  (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
                (ENNReal.ofReal (1 / 6) *
                  (Kakeya.realRpowENN sourceDelta
                      quantitativeOutput.densityLoss *
                    (wz1PaperBodyFamily
                      quantitativeOutput.normalized.source.family).mass))))) := by
        rw [← hgroup]
        ring
    _ ≤ _ := by
      calc
        _ ≤ ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        (ENNReal.ofReal
            (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
          (ENNReal.ofReal
              (1 / (quantitativeOutput.normalized.prepared.normalization *
                quantitativeOutput.normalized.prepared.slab.halfHeight)) *
              (ENNReal.ofReal
                (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
                quantitativeOutput.normalized.hierarchy.shading.mass))) := by
          gcongr
          exact quantitativeOutput.normalized_mass_retention
        _ ≤ _ := geometry.paperED_mass_ledger ed

/-- Every final ED index comes from a distinct index of the original
normalized source family. -/
theorem paperED_enncard_le_source
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    ed.subfamily.family.enncard ≤ output.source.family.enncard := by
  have hed := Fintype.card_le_of_injective ed.subfamily.embedding
    ed.subfamily.embedding.injective
  simp only [Fintype.card_fin] at hed
  have hselected : geometry.selectedSource.family.card ≤
      output.source.family.card :=
    by
      simpa [Fintype.card_fin] using
        Fintype.card_le_of_injective geometry.selectedSource.embedding
          geometry.selectedSource.embedding.injective
  change (ed.subfamily.family.card : ENNReal) ≤
    (output.source.family.card : ENNReal)
  change ed.subfamily.family.card ≤ geometry.selectedSource.family.card at hed
  exact_mod_cast hed.trans hselected

/-- The paper-body mass of the final family is controlled by the original
source body mass and the explicit quadratic change of scale. -/
theorem paperED_body_mass_comparison
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    Kakeya.realRpowENN sourceDelta 2 *
        (wz1PaperBodyFamily ed.subfamily.family).mass ≤
      (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2) *
        (wz1PaperBodyFamily output.source.family).mass := by
  let fullShading : WZ1PaperTubeShading ed.subfamily.family := {
    carrier := fun index => wz1PaperTubeCarrier
      (ed.subfamily.family.tube index)
    measurable_carrier := fun index =>
      wz1PaperTubeCarrier_measurable (ed.subfamily.family.tube index)
    subset_body := fun _ => Set.Subset.rfl }
  have hfinalBody :
      (wz1PaperBodyFamily ed.subfamily.family).mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2 *
          ed.subfamily.family.enncard := by
    have h := wz2_paper_shading_mass_upper
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      (geometry.paperED_lineClass ed) fullShading
    change fullShading.mass ≤ _
    simpa [mul_assoc] using h
  have hsourceBody :
      output.source.family.enncard * Kakeya.realRpowENN sourceDelta 2 ≤
        (wz1PaperBodyFamily output.source.family).mass :=
    pureWZ2_paperBody_mass_lower output.source.extremal.delta_pos
      (by nlinarith [geometry.scales.sourceDelta_small])
      output.source.line_class
  calc
    Kakeya.realRpowENN sourceDelta 2 *
          (wz1PaperBodyFamily ed.subfamily.family).mass ≤
        Kakeya.realRpowENN sourceDelta 2 *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2 *
            ed.subfamily.family.enncard) := by gcongr
    _ ≤ (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2) *
          (output.source.family.enncard *
            Kakeya.realRpowENN sourceDelta 2) := by
      rw [mul_assoc]
      ring_nf
      gcongr
      exact geometry.paperED_enncard_le_source ed
    _ ≤ (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2) *
          (wz1PaperBodyFamily output.source.family).mass := by gcongr

/-- Quantitative-output specialization of the final/source paper-body mass
comparison. -/
theorem paperED_quantitative_body_mass_comparison
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    Kakeya.realRpowENN sourceDelta 2 *
        (wz1PaperBodyFamily ed.subfamily.family).mass ≤
      (55296 * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2) *
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass :=
  geometry.paperED_body_mass_comparison ed

/-- Cancel the common finite positive source-scale factor and ED loss from a
mass ledger. -/
private theorem density_of_scaled_mass_ledger
    (sourceScale edLoss targetDensity targetBody bodyCoefficient
      sourceBody massCoefficient finalMass : ENNReal)
    (hsourceScaleZero : sourceScale ≠ 0)
    (hsourceScaleTop : sourceScale ≠ ⊤)
    (hedLossZero : edLoss ≠ 0)
    (hedLossTop : edLoss ≠ ⊤)
    (hbody : sourceScale * targetBody ≤ bodyCoefficient * sourceBody)
    (habsorb : edLoss * (targetDensity * bodyCoefficient) ≤
      massCoefficient * sourceScale)
    (hledger : massCoefficient * sourceBody ≤ edLoss * finalMass) :
    targetDensity * targetBody ≤ finalMass := by
  have hscaled :
      (edLoss * sourceScale) * (targetDensity * targetBody) ≤
        (edLoss * sourceScale) * finalMass := by
    calc
      (edLoss * sourceScale) * (targetDensity * targetBody) =
          edLoss * targetDensity * (sourceScale * targetBody) := by ring
      _ ≤ edLoss * targetDensity * (bodyCoefficient * sourceBody) := by
        gcongr
      _ = (edLoss * (targetDensity * bodyCoefficient)) * sourceBody := by
        ring
      _ ≤ (massCoefficient * sourceScale) * sourceBody := by gcongr
      _ = sourceScale * (massCoefficient * sourceBody) := by ring
      _ ≤ sourceScale * (edLoss * finalMass) := by gcongr
      _ = (edLoss * sourceScale) * finalMass := by ring
  apply (ENNReal.mul_le_mul_iff_left
    (mul_ne_zero hedLossZero hsourceScaleZero)
    (ENNReal.mul_ne_top hedLossTop hsourceScaleTop)).mp
  simpa [mul_comm] using hscaled

/-- The exact mass ledger gives final lambda density after one scalar
absorption.  All family and shading factors are derived internally. -/
theorem paperED_dense_of_quantitative_mass
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K)
    {densityLoss : ℝ}
    (hKtop : K ≠ ⊤)
    (habsorption :
      (147 * (K + 1)) *
          (Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) densityLoss *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) ≤
        pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
          Kakeya.realRpowENN sourceDelta 2) :
    ed.finalShading.IsLambdaDense
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) densityLoss) := by
  apply density_of_scaled_mass_ledger
    (Kakeya.realRpowENN sourceDelta 2) (147 * (K + 1))
    (Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) densityLoss)
    (wz1PaperBodyFamily ed.subfamily.family).mass
    (55296 * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)
    (wz1PaperBodyFamily
      quantitativeOutput.normalized.source.family).mass
    (pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput)
    ed.finalShading.mass
  · apply (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos
        quantitativeOutput.normalized.source.extremal.delta_pos 2)).ne'
  · simp [Kakeya.realRpowENN]
  · apply mul_ne_zero
    · norm_num
    · simp
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨hKtop, by norm_num⟩)
  · exact geometry.paperED_quantitative_body_mass_comparison
      quantitativeOutput ed
  · exact habsorption
  · exact geometry.paperED_quantitative_mass_ledger quantitativeOutput ed

/-- Fixed cell-count and scale cost in the upper union-volume transport.  The
only hierarchy-dependent part is the vertical factor `O(h⁻¹)`. -/
noncomputable def pureWZ2Proposition64VolumeCoefficient
    (output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta) : ENNReal :=
  ((3 * 3 * (2 * Nat.ceil
      (2 / (45 * output.prepared.slab.halfHeight)) + 1) : ℕ) : ENNReal) *
    ENNReal.ofReal ((45 * pureWZ2Proposition64Lemma35Scale) ^ 3)

/-- The exact affine/isotropic image and final grid saturation expand the
source cubical union by only the explicit Proposition-6.4 cell-count cost. -/
theorem paperED_union_volume_upper
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    volume ed.finalShading.union ≤
      pureWZ2Proposition64VolumeCoefficient output *
        Kakeya.realRpowENN sourceDelta (sigma - output.inputLoss) := by
  let combined := pureWZ2Proposition64CombinedMap
    output.prepared.restrictedRaw.slope output.prepared.slab.center
    output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
    output.prepared.normalization geometry.common.translation
    geometry.cleanup.popular.center pureWZ2Proposition64Lemma35Scale
  have hselectedSource : geometry.selectedShading.union ⊆
      output.source.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨geometry.selectedSource.embedding index,
      output.hierarchy.subshading _
        (output.prepared.slab.subshading _ hpoint)⟩
  have hfullSubset : geometry.cleanup.finalShading.union ⊆
      wz1PaperCubicalSaturation
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (combined '' geometry.selectedShading.union) := by
    rintro point ⟨index, hpoint⟩
    change point ∈ wz1PaperCubicalSaturation
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      (pureWZ2Proposition64IsotropicMap geometry.cleanup.popular.center
        pureWZ2Proposition64Lemma35Scale ''
          geometry.cleanup.popular.restricted.carrier index) at hpoint
    rcases hpoint with
      ⟨isotropicPoint, ⟨exactPoint, hexactPoint, rfl⟩, hcell⟩
    have hexactFull : exactPoint ∈ geometry.exactShading.carrier index :=
      geometry.cleanup.popular.restricted_subshading index hexactPoint
    rcases hexactFull with ⟨sourcePoint, hsourcePoint, hexactEq⟩
    refine ⟨combined sourcePoint, ?_, ?_⟩
    · exact ⟨sourcePoint, ⟨index, hsourcePoint⟩, rfl⟩
    · simpa [combined, pureWZ2Proposition64CombinedMap, hexactEq] using hcell
  have hsaturation :=
    pureWZ2Proposition64CombinedSaturation_volume_upper
      output.prepared.restrictedRaw.slope output.prepared.slab.center
      output.prepared.slab.anchorHeight geometry.common.translation
      geometry.cleanup.popular.center output.source.shading
      geometry.selectedShading.union output.source.extremal.delta_pos
      geometry.scales.finalDelta_pos output.prepared.slab.halfHeight_pos
      output.normalization_nine output.prepared.normalized.anchor_value_bound
      geometry.scales.scale_one rfl output.source.cubical hselectedSource
  calc
    volume ed.finalShading.union ≤
        volume geometry.cleanup.finalShading.union :=
      measure_mono ed.union_subset
    _ ≤ volume (wz1PaperCubicalSaturation
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (combined '' geometry.selectedShading.union)) :=
      measure_mono hfullSubset
    _ ≤ pureWZ2Proposition64VolumeCoefficient output *
          volume output.source.shading.union := by
      simpa [pureWZ2Proposition64VolumeCoefficient, combined] using
        hsaturation
    _ ≤ pureWZ2Proposition64VolumeCoefficient output *
        Kakeya.realRpowENN sourceDelta (sigma - output.inputLoss) := by
      gcongr
      exact output.source.extremal.volume_upper

/-- Quantitative data still needed after the final lower volume bound is
delegated to the quantifier-ordered critical-floor theorem.  The density and
nearby CWA live at the same structural loss selected before the runtime
family. -/
structure FinalCriticalFloorReceipt
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K)
    (outputLoss : ℝ)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss) where
  nearby : WZ2PaperPureCWAAtNearbyScales ed.subfamily.family
    (Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-floor.structuralLoss))
  finalDelta_le_floor :
    pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ floor.delta₀
  ed_loss_ne_top : K ≠ ⊤
  density_absorption :
    (147 * (K + 1)) *
        (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              floor.structuralLoss *
          (55296 * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) ≤
      pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        Kakeya.realRpowENN sourceDelta 2
  cwa_absorption :
    4 * Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  volume_absorption :
    pureWZ2Proposition64VolumeCoefficient quantitativeOutput.normalized *
        Kakeya.realRpowENN sourceDelta
          (sigma - quantitativeOutput.normalized.inputLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss)
  local_constant_absorption :
    192 * Kakeya.realRpowENN sourceDelta (-workLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  global_constant_absorption :
    7077888 * (24000 * Kakeya.realRpowENN sourceDelta (-workLoss)) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)

/-- The critical floor supplies the final lower union-volume estimate on the
same ED-selected shading. -/
theorem FinalCriticalFloorReceipt.volume_lower
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K)
    {outputLoss : ℝ}
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)
    (receipt : FinalCriticalFloorReceipt
      quantitativeOutput geometry ed outputLoss floor) :
    Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma + outputLoss) ≤
      volume ed.finalShading.union :=
  floor.volume_floor
    (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
    geometry.scales.finalDelta_pos receipt.finalDelta_le_floor
    ed.subfamily.family (geometry.paperED_family_nonempty ed) ed.finalShading
    receipt.nearby (ed.cubical geometry.cleanup.cubical)
    (geometry.paperED_dense_of_quantitative_mass quantitativeOutput ed
      receipt.ed_loss_ne_top receipt.density_absorption)

/-- Assemble Proposition 6.4 while deriving both the output-loss density
weakening and the lower union-volume bound from the preselected critical-floor
receipt. -/
theorem assembleVerticalRediscretizationOfCriticalFloor
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K)
    {outputLoss : ℝ}
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)
    (receipt : FinalCriticalFloorReceipt
      quantitativeOutput geometry ed outputLoss floor) :
    Nonempty (PureWZ2VerticalRediscretizationData
      quantitativeOutput.normalized.prepared.normalized
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  have hfinalDeltaOne :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ 1 :=
    geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num)
  have hdense : ed.finalShading.IsLambdaDense
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
    have hstructural := geometry.paperED_dense_of_quantitative_mass
      quantitativeOutput ed receipt.ed_loss_ne_top
      receipt.density_absorption
    apply le_trans (mul_le_mul_right' ?_ _) hstructural
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      geometry.scales.finalDelta_pos hfinalDeltaOne floor.structuralLoss_le
  apply geometry.assembleVerticalRediscretization ed
    (geometry.paperED_family_nonempty ed)
  exact {
    nearbyLoss := floor.structuralLoss
    nearby := receipt.nearby
    nearby_le_output := floor.structuralLoss_le
    cwa_absorption := receipt.cwa_absorption
    dense := hdense
    volume_upper :=
      (geometry.paperED_union_volume_upper ed).trans
        receipt.volume_absorption
    local_constant_absorption := receipt.local_constant_absorption
    global_constant_absorption := receipt.global_constant_absorption }

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
