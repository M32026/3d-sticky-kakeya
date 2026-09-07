import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedTubeCardinalityRetentionFromMass

/-!
# Indexed per-tube pruning for the pure WZ2 source family

From aggregate shading density, discard indices whose shaded carrier has less
than the requested pointwise tube density.  The retained indexed family keeps
at least half of the total shaded mass and the requested cardinality fraction.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Indexed aggregate-to-pointwise density pruning.

The selected shading is the literal reindexing of the original shading.  In
particular, every later source-index selection can inherit the pointwise lower
bound without paying another density loss.
-/
theorem pure_wz2_indexed_per_tube_pruning
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hfamilyNonempty : family.Nonempty)
    (shading : Kakeya.Streamlined.TubeShading family)
    {inputEta outputEta : ℝ}
    (hdense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta inputEta))
    (hsmall :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta inputEta) :
    ∃ selected : Finset (Fin family.card),
      selected.Nonempty ∧
        Kakeya.realRpowENN delta outputEta *
            family.enncard ≤
          (selectedTubeFamily family selected).enncard ∧
        shading.mass ≤
          2 * (selectedTubeShading shading selected).mass ∧
        ∀ index ∈ selected,
          Kakeya.realRpowENN delta outputEta *
              (family.tube index).volume ≤
            MeasureTheory.volume (shading.carrier index) := by
  let tubeVolume : ENNReal := Kakeya.deltaTubeVolume delta
  let threshold : ENNReal :=
    Kakeya.realRpowENN delta outputEta * tubeVolume
  let selected : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      threshold ≤ MeasureTheory.volume (shading.carrier index)
  let discarded : Finset (Fin family.card) :=
    Finset.univ \ selected
  let discardedMass : ENNReal :=
    ∑ index ∈ discarded,
      MeasureTheory.volume (shading.carrier index)
  have htubeVolumePositive : 0 < tubeVolume :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).1
  have htubeVolumeTop : tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).2
  have hperTube :
      ∀ index ∈ selected,
        Kakeya.realRpowENN delta outputEta *
            (family.tube index).volume ≤
          MeasureTheory.volume (shading.carrier index) := by
    intro index hindex
    have hthreshold :
        threshold ≤ MeasureTheory.volume (shading.carrier index) :=
      (Finset.mem_filter.mp hindex).2
    have hvolume :
        (family.tube index).volume = tubeVolume :=
      tube_volume_scaling.1 delta (family.tube index)
    simpa [threshold, hvolume] using hthreshold
  have hdiscardedMass :
      discardedMass ≤
        threshold * family.enncard := by
    calc
      discardedMass ≤
          ∑ _index ∈ discarded, threshold := by
        apply Finset.sum_le_sum
        intro index hindex
        have hnotSelected : index ∉ selected :=
          (Finset.mem_sdiff.mp hindex).2
        have hnot :
            ¬ threshold ≤
              MeasureTheory.volume (shading.carrier index) := by
          simpa [selected] using hnotSelected
        exact (lt_of_not_ge hnot).le
      _ = threshold * (discarded.card : ENNReal) := by
        simp [Finset.sum_const]
        ring
      _ ≤ threshold * family.enncard := by
        gcongr
        change (discarded.card : ENNReal) ≤ (family.card : ENNReal)
        have hcard :
            discarded.card ≤ family.card := by
          simpa using Finset.card_le_univ discarded
        exact_mod_cast hcard
  have hmassSplit :
      (selectedTubeShading shading selected).mass +
          discardedMass =
        shading.mass := by
    rw [selectedTubeShading_mass]
    have hdisjoint : Disjoint selected discarded := by
      rw [Finset.disjoint_left]
      intro index hselected hdiscarded
      exact (Finset.mem_sdiff.mp hdiscarded).2 hselected
    have hunion :
        selected ∪ discarded =
          (Finset.univ : Finset (Fin family.card)) := by
      ext index
      simp [discarded]
    calc
      (∑ index ∈ selected,
          MeasureTheory.volume (shading.carrier index)) +
          discardedMass =
        ∑ index ∈ selected ∪ discarded,
          MeasureTheory.volume (shading.carrier index) := by
            rw [Finset.sum_union hdisjoint]
      _ = shading.mass := by
        rw [hunion]
        rfl
  have hfamilyMass :
      family.toBodyFamily.mass =
        family.enncard * tubeVolume := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have hbadHalf :
      2 * discardedMass ≤ shading.mass := by
    calc
      2 * discardedMass ≤
          2 * (threshold * family.enncard) := by
        gcongr
      _ =
          (2 * Kakeya.realRpowENN delta outputEta) *
            family.enncard * tubeVolume := by
        simp [threshold]
        ring
      _ ≤
          Kakeya.realRpowENN delta inputEta *
            family.enncard * tubeVolume := by
        gcongr
        have htwo :
            2 * Kakeya.realRpowENN delta outputEta ≤
              Kakeya.realRpowENN delta inputEta := by
          calc
            2 * Kakeya.realRpowENN delta outputEta ≤
                2 * ((1 / 2 : ENNReal) *
                  Kakeya.realRpowENN delta inputEta) := by
              gcongr
            _ = Kakeya.realRpowENN delta inputEta := by
              rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
                norm_num]
              rw [← mul_assoc,
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
                one_mul]
        exact htwo
      _ =
          Kakeya.realRpowENN delta inputEta *
            family.toBodyFamily.mass := by
        rw [hfamilyMass]
        ring
      _ ≤ shading.mass := hdense
  have hdiscardedTop : discardedMass ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          ENNReal.ofReal_ne_top htubeVolumeTop)
        (by
          change (family.card : ENNReal) ≠ ⊤
          simp))
      hdiscardedMass
  have hdiscardedSelected :
      discardedMass ≤
        (selectedTubeShading shading selected).mass := by
    have hbound :
        discardedMass + discardedMass ≤
          (selectedTubeShading shading selected).mass +
            discardedMass := by
      rw [hmassSplit]
      simpa [two_mul] using hbadHalf
    exact
      (ENNReal.add_le_add_iff_right hdiscardedTop).mp
        hbound
  have hmassRetention :
      shading.mass ≤
        2 * (selectedTubeShading shading selected).mass := by
    rw [← hmassSplit]
    calc
      (selectedTubeShading shading selected).mass +
          discardedMass ≤
        (selectedTubeShading shading selected).mass +
          (selectedTubeShading shading selected).mass := by
            gcongr
      _ =
          2 * (selectedTubeShading shading selected).mass := by
        ring
  have hcardinality :
      Kakeya.realRpowENN delta outputEta *
          family.enncard ≤
        (selectedTubeFamily family selected).enncard := by
    have hhalfCardinality :=
      selected_tube_cardinality_retention_from_mass
        tube_volume_scaling hdelta hdeltaOne family shading
        selected
        (Kakeya.realRpowENN delta inputEta)
        2 hdense hmassRetention (by norm_num) (by norm_num)
    calc
      Kakeya.realRpowENN delta outputEta *
          family.enncard ≤
        ((2 : ENNReal)⁻¹ *
            Kakeya.realRpowENN delta inputEta) *
          family.enncard := by
            gcongr
            simpa using hsmall
      _ ≤ (selectedTubeFamily family selected).enncard :=
        hhalfCardinality
  have hselectedNonempty : selected.Nonempty := by
    have hsourcePositive : 0 < family.enncard := by
      change 0 < (family.card : ENNReal)
      exact_mod_cast hfamilyNonempty
    have hweightPositive :
        0 < Kakeya.realRpowENN delta outputEta :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta outputEta)
    have hselectedPositive :
        0 < (selectedTubeFamily family selected).enncard :=
      (ENNReal.mul_pos hweightPositive.ne'
        hsourcePositive.ne').trans_le hcardinality
    change 0 < (selected.card : ENNReal) at hselectedPositive
    exact Finset.card_pos.mp (by exact_mod_cast hselectedPositive)
  exact
    ⟨selected, hselectedNonempty, hcardinality,
      hmassRetention, hperTube⟩

end Kakeya.Assouad

end
