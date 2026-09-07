import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry

/-!
# Cardinality retention from paper shaded-mass retention

Once every ambient tube has a uniform shaded-mass floor, a retained fraction
of total shaded mass forces a quantitative fraction of the indexed tubes to
survive.  The selected shaded mass is bounded above using the uniform
quadratic volume bound for cropped `L₃` paper tubes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2PaperWeightedCardinality_retained_from_mass
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (selected : Finset (Fin family.card))
    (tubeMassFactor : ENNReal)
    (massLoss : ENNReal)
    (hambientMass :
      tubeMassFactor * family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (hretained :
      shading.mass ≤
        massLoss *
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              family selected)
            shading).mass) :
    tubeMassFactor * family.enncard ≤
      massLoss *
          (55296 * Kakeya.deltaTubeVolume 1) *
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          family selected).family.enncard := by
  let selectedFamily :=
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
      family selected).family
  let volumeScale : ENNReal := Kakeya.realRpowENN delta 2
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have hselectedUpper :
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          family selected)
        shading).mass ≤
      selectedFamily.enncard *
        (geometryConstant * volumeScale) := by
    rw [restrictPaperShading_fromFinset_mass]
    calc
      ∑ index ∈ selected, volume (shading.carrier index)
          ≤ ∑ index ∈ selected,
              volume (wz1PaperTubeCarrier (family.tube index)) := by
        exact Finset.sum_le_sum fun index _ =>
          measure_mono (shading.subset_body index)
      _ ≤ ∑ _index ∈ selected,
          geometryConstant * volumeScale := by
        apply Finset.sum_le_sum
        intro index _
        exact
          wz2PaperTubeCarrier_convex_and_volume_quadratic
            wz2_paper_tube_carrier_geometry
            hdelta hdeltaSmall (family.tube index) (hline index) |>.2
      _ = selectedFamily.enncard *
          (geometryConstant * volumeScale) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
        dsimp only [selectedFamily]
        rfl
  have hwithScale :
      (tubeMassFactor * family.enncard) * volumeScale ≤
        (massLoss * geometryConstant *
          selectedFamily.enncard) * volumeScale := by
    calc
      (tubeMassFactor * family.enncard) * volumeScale =
          tubeMassFactor * family.enncard * volumeScale := by
        ring
      _ ≤ shading.mass := by
        simpa [volumeScale] using hambientMass
      _ ≤ massLoss *
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              family selected)
            shading).mass := hretained
      _ ≤ massLoss *
          (selectedFamily.enncard *
            (geometryConstant * volumeScale)) := by
        gcongr
      _ = (massLoss * geometryConstant *
          selectedFamily.enncard) * volumeScale := by
        ring
  have hscalePos : 0 < volumeScale := by
    dsimp only [volumeScale, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta 2)
  have hscaleTop : volumeScale ≠ ⊤ := by
    simp [volumeScale, Kakeya.realRpowENN]
  exact
    (ENNReal.mul_le_mul_iff_left
      hscalePos.ne' hscaleTop).mp hwithScale

theorem wz2PaperCardinality_retained_from_mass
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (selected : Finset (Fin family.card))
    (massLoss : ENNReal)
    (hambientMass :
      family.enncard * Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (hretained :
      shading.mass ≤
        massLoss *
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              family selected)
            shading).mass) :
    family.enncard ≤
      massLoss *
          (55296 * Kakeya.deltaTubeVolume 1) *
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          family selected).family.enncard := by
  have h :=
    wz2PaperWeightedCardinality_retained_from_mass
      hdelta hdeltaSmall hline shading selected 1 massLoss
      (by simpa using hambientMass) hretained
  simpa using h

/--
Cardinality retention for an already-indexed tube subfamily.

The existing quantitative theorem is stated for a finite set of ambient
indices.  Apply it to the image of the subfamily embedding and reindex the
selected mass and cardinality back to the supplied family.
-/
theorem wz2PaperWeightedCardinality_retained_from_subfamily_mass
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (tubeMassFactor massLoss : ENNReal)
    (hambientMass :
      tubeMassFactor * family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (hretained :
      shading.mass ≤
        massLoss * (restrictPaperShading selected shading).mass) :
    tubeMassFactor * family.enncard ≤
      massLoss *
          (55296 * Kakeya.deltaTubeVolume 1) *
        selected.family.enncard := by
  let selectedIndices : Finset (Fin family.card) :=
    Finset.univ.map selected.embedding
  have hselectedShading :
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          family selectedIndices)
        shading).mass =
        (restrictPaperShading selected shading).mass := by
    rw [restrictPaperShading_fromFinset_mass]
    change
      (∑ index ∈ selectedIndices,
        volume (shading.carrier index)) =
        ∑ index : Fin selected.family.card,
          volume (shading.carrier (selected.embedding index))
    rw [Finset.sum_map]
  have hselectedCard :
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        family selectedIndices).family.enncard =
        selected.family.enncard := by
    change
      (selectedIndices.card : ENNReal) =
        (selected.family.card : ENNReal)
    have hcard :
        selectedIndices.card = selected.family.card := by
      dsimp only [selectedIndices]
      rw [Finset.card_map]
      simp
    exact congrArg (fun value : ℕ => (value : ENNReal)) hcard
  have hmain :=
    wz2PaperWeightedCardinality_retained_from_mass
      hdelta hdeltaSmall hline shading selectedIndices
      tubeMassFactor massLoss hambientMass
      (by simpa [hselectedShading] using hretained)
  simpa [hselectedCard] using hmain

/--
Weighted cardinality retention against an external reference cardinality.

The shading may live on a root fiber while its absolute mass lower bound is
normalized by the cardinality of the original ambient source family.
-/
theorem wz2PaperReferenceCardinality_retained_from_subfamily_mass
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (referenceCardinality tubeMassFactor massLoss : ENNReal)
    (hambientMass :
      tubeMassFactor * referenceCardinality *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (hretained :
      shading.mass ≤
        massLoss * (restrictPaperShading selected shading).mass) :
    tubeMassFactor * referenceCardinality ≤
      massLoss *
          (55296 * Kakeya.deltaTubeVolume 1) *
        selected.family.enncard := by
  let volumeScale : ENNReal := Kakeya.realRpowENN delta 2
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have hselectedUpper :
      (restrictPaperShading selected shading).mass ≤
        selected.family.enncard *
          (geometryConstant * volumeScale) := by
    rw [restrictPaperShading_mass]
    calc
      ∑ index : Fin selected.family.card,
          volume (shading.carrier (selected.embedding index))
          ≤
        ∑ index : Fin selected.family.card,
          volume
            (wz1PaperTubeCarrier
              (family.tube (selected.embedding index))) := by
        exact Finset.sum_le_sum fun index _ =>
          measure_mono (shading.subset_body (selected.embedding index))
      _ ≤
        ∑ _index : Fin selected.family.card,
          geometryConstant * volumeScale := by
        apply Finset.sum_le_sum
        intro index _
        exact
          wz2PaperTubeCarrier_convex_and_volume_quadratic
            wz2_paper_tube_carrier_geometry
            hdelta hdeltaSmall
            (family.tube (selected.embedding index))
            (hline (selected.embedding index)) |>.2
      _ =
        selected.family.enncard *
          (geometryConstant * volumeScale) := by
        simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hwithScale :
      (tubeMassFactor * referenceCardinality) * volumeScale ≤
        (massLoss * geometryConstant *
          selected.family.enncard) * volumeScale := by
    calc
      (tubeMassFactor * referenceCardinality) * volumeScale =
          tubeMassFactor * referenceCardinality * volumeScale := by
        ring
      _ ≤ shading.mass := by
        simpa [volumeScale] using hambientMass
      _ ≤ massLoss *
          (restrictPaperShading selected shading).mass :=
        hretained
      _ ≤ massLoss *
          (selected.family.enncard *
            (geometryConstant * volumeScale)) := by
        gcongr
      _ =
          (massLoss * geometryConstant *
            selected.family.enncard) * volumeScale := by
        ring
  have hscalePos : 0 < volumeScale := by
    dsimp only [volumeScale, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta 2)
  have hscaleTop : volumeScale ≠ ⊤ := by
    simp [volumeScale, Kakeya.realRpowENN]
  exact
    (ENNReal.mul_le_mul_iff_left
      hscalePos.ne' hscaleTop).mp hwithScale

end Kakeya.Assouad

end
