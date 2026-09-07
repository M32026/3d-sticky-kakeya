import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCardinalityRetention

/-!
# Per-tube mass pruning for cropped paper shadings

This is the literal paper-model version of the first pruning in the proof of
`prop: sticky`: discard tubes whose shaded carrier has less than half the
average density scale.  The output is a genuine tube subfamily, not a shading
with empty carriers left on the ambient family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure WZ2PaperPerTubePruningData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (density : ENNReal) where
  selected : Finset (Fin family.card)
  retained_mass :
    shading.mass ≤
      2 *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            family selected)
          shading).mass
  per_tube :
    ∀ index :
        Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset
          family selected).family.card,
      (1 / 2 : ENNReal) * density *
          Kakeya.realRpowENN delta 2 ≤
        volume
          ((restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              family selected)
            shading).carrier index)

theorem wz2PaperPerTubePruning
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (density : ENNReal)
    (hdense :
      density * family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass) :
    Nonempty (WZ2PaperPerTubePruningData shading density) := by
  let threshold : ENNReal :=
    (1 / 2 : ENNReal) * density *
      Kakeya.realRpowENN delta 2
  let selected : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      threshold ≤ volume (shading.carrier index)
  let selectedShading :=
    restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        family selected)
      shading
  let discarded := Finset.univ \ selected
  let discardedMass : ENNReal :=
    ∑ index ∈ discarded, volume (shading.carrier index)
  have hdiscarded :
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
            ¬threshold ≤ volume (shading.carrier index) := by
          simpa [selected] using hnotSelected
        exact (lt_of_not_ge hnot).le
      _ = threshold * (discarded.card : ENNReal) := by
        simp [Finset.sum_const]
        ring
      _ ≤ threshold * family.enncard := by
        gcongr
        have hcard :
            discarded.card ≤ family.card := by
          have hsubset :
              discarded ⊆
                (Finset.univ : Finset (Fin family.card)) := by
            simp [discarded]
          simpa using Finset.card_le_card hsubset
        simpa [Kakeya.Streamlined.TubeFamily.enncard] using
          (show (discarded.card : ENNReal) ≤
              (family.card : ENNReal) by
            exact_mod_cast hcard)
  have hsplit :
      selectedShading.mass + discardedMass = shading.mass := by
    rw [restrictPaperShading_fromFinset_mass]
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
      (∑ index ∈ selected, volume (shading.carrier index)) +
          discardedMass =
          ∑ index ∈ selected ∪ discarded,
            volume (shading.carrier index) := by
        rw [Finset.sum_union hdisjoint]
      _ = shading.mass := by
        rw [hunion]
        rfl
  have hthreshold :
      2 * (threshold * family.enncard) =
        density * family.enncard *
          Kakeya.realRpowENN delta 2 := by
    dsimp only [threshold]
    have hhalf :
        (2 : ENNReal)⁻¹ * 2 = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    have hhalfDef :
        (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
      simp
    rw [hhalfDef]
    calc
      2 * ((2 : ENNReal)⁻¹ * density *
          Kakeya.realRpowENN delta 2 *
          family.enncard) =
          ((2 : ENNReal)⁻¹ * 2) *
            (density * family.enncard *
              Kakeya.realRpowENN delta 2) := by ring
      _ = density * family.enncard *
          Kakeya.realRpowENN delta 2 := by rw [hhalf, one_mul]
  have htwoDiscarded :
      2 * discardedMass ≤ shading.mass := by
    calc
      2 * discardedMass ≤
          2 * (threshold * family.enncard) := by
        gcongr
      _ = density * family.enncard *
          Kakeya.realRpowENN delta 2 := hthreshold
      _ ≤ shading.mass := hdense
  have hretained :
      shading.mass ≤ 2 * selectedShading.mass := by
    rw [← hsplit]
    have hdiscardedSelected :
        discardedMass ≤ selectedShading.mass := by
      have hbound :
          discardedMass + discardedMass ≤
            selectedShading.mass + discardedMass := by
        have hbound' := htwoDiscarded
        rw [← hsplit] at hbound'
        simpa [two_mul] using hbound'
      have hdiscardedFinite : discardedMass ≠ ⊤ := by
        dsimp only [discardedMass]
        apply (ENNReal.sum_ne_top).2
        intro index hindex
        have hcarrierBox :
            shading.carrier index ⊆
              Kakeya.Streamlined.axisBox 2 2 2 :=
          (shading.subset_body index).trans Set.inter_subset_right
        have hmeasure :
            volume (shading.carrier index) ≤
              volume (Kakeya.Streamlined.axisBox 2 2 2) :=
          measure_mono hcarrierBox
        exact
          ne_top_of_le_ne_top
            (by
              rw [Kakeya.Streamlined.volume_axisBox
                2 2 2 (by norm_num) (by norm_num) (by norm_num)]
              exact ENNReal.ofReal_ne_top)
            hmeasure
      exact ENNReal.add_le_add_iff_right
        hdiscardedFinite
        |>.mp hbound
    calc
      selectedShading.mass + discardedMass ≤
          selectedShading.mass + selectedShading.mass := by
        gcongr
      _ = 2 * selectedShading.mass := by ring
  refine ⟨{
    selected := selected
    retained_mass := by
      simpa [selectedShading] using hretained
    per_tube := ?_ }⟩
  intro index
  have hselected :
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        family selected).embedding index ∈ selected :=
    Finset.orderEmbOfFin_mem selected rfl index
  have hthresholdSelected :
      threshold ≤
        volume
          (shading.carrier
            ((Kakeya.Streamlined.TubeSubfamily.fromFinset
              family selected).embedding index)) :=
    (Finset.mem_filter.mp hselected).2
  simpa [threshold, restrictPaperShading] using
    hthresholdSelected

end Kakeya.Assouad

end
