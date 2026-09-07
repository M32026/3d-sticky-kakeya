import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicBandSelection

/-!
# Dyadic multiplicity selection above a supplied floor

If every active point has multiplicity at least `m`, the empty dyadic levels
below `log₂ m` need not be paid.  Pigeonholing only the shifted levels gives
the loss `log₂ #family - log₂ m + 1`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset Classical

attribute [local instance] Classical.propDecidable

/-- Select a factor-two multiplicity band after discarding all dyadic levels
below the supplied pointwise floor. -/
theorem exists_relative_dyadic_band_with_mass_retention
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading source)
    (m : ℕ) (hm : 0 < m)
    (hmultiplicity : ∀ point ∈ source.union,
      m ≤ source.pointMultiplicity point) :
    ∃ level : ℕ,
      let selected := wz1PaperDyadicBandSubshading source level
      Nat.log 2 m ≤ level ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        (2 ^ level : ℕ) ≤ selected.pointMultiplicity point ∧
        selected.pointMultiplicity point < 2 ^ (level + 1)) ∧
      source.mass ≤
        ((Nat.log 2 family.card - Nat.log 2 m + 1 : ℕ) : ENNReal) *
          selected.mass := by
  let base : ℕ := Nat.log 2 m
  let levelCount : ℕ := Nat.log 2 family.card - base + 1
  let band (offset : ℕ) : Set Point3 :=
    wz1PaperDyadicMultiplicityBand source (base + offset)
  let bandMass (offset : ℕ) : ENNReal :=
    (wz1PaperDyadicBandSubshading source (base + offset)).mass
  have hdisjoint : ∀ first second : ℕ, first ≠ second →
      Disjoint (band first) (band second) := by
    intro first second hne
    simp only [band, wz1PaperDyadicMultiplicityBand, Set.disjoint_left]
    intro point hfirst hsecond
    have hlevels : base + first < base + second ∨
        base + second < base + first := by omega
    rcases hlevels with hlt | hlt
    · have hpower : (2 ^ (base + first + 1) : ENNReal) ≤
          (2 ^ (base + second) : ENNReal) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (not_le_of_gt (hsecond.1.trans_lt hfirst.2)) hpower
    · have hpower : (2 ^ (base + second + 1) : ENNReal) ≤
          (2 ^ (base + first) : ENNReal) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (not_le_of_gt (hfirst.1.trans_lt hsecond.2)) hpower
  have hcover : ∀ index : Fin family.card, source.carrier index ⊆
      ⋃ offset ∈ Finset.range levelCount, band offset := by
    intro index point hpoint
    have hpointUnion : point ∈ source.union := ⟨index, hpoint⟩
    have hmultPos : 0 < source.pointMultiplicity point :=
      hm.trans_le (hmultiplicity point hpointUnion)
    let level := Nat.log 2 (source.pointMultiplicity point)
    have hbaseLevel : base ≤ level := by
      dsimp only [base, level]
      exact Nat.log_mono_right (hmultiplicity point hpointUnion)
    have hmultCard : source.pointMultiplicity point ≤ family.card := by
      change (Finset.univ.filter fun index : Fin family.card =>
        point ∈ source.carrier index).card ≤ family.card
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
    have hlevelTop : level ≤ Nat.log 2 family.card :=
      Nat.log_mono_right hmultCard
    let offset := level - base
    have hoffset : offset < levelCount := by
      dsimp only [offset, levelCount]
      omega
    have hlevelEq : base + offset = level := by
      dsimp only [offset]
      omega
    have hband : point ∈ band offset := by
      simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq,
        hlevelEq]
      constructor
      · exact_mod_cast Nat.pow_log_le_self 2 hmultPos.ne'
      · exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num)
          (source.pointMultiplicity point)
    exact Set.mem_iUnion₂.mpr
      ⟨offset, by simpa [Finset.mem_range] using hoffset, hband⟩
  have hmassDecomp : source.mass =
      ∑ offset ∈ Finset.range levelCount, bandMass offset := by
    have hperIndex : ∀ index : Fin family.card,
        volume (source.carrier index) =
          ∑ offset ∈ Finset.range levelCount,
            volume (source.carrier index ∩ band offset) := by
      intro index
      have hpairwise : Set.PairwiseDisjoint
          (↑(Finset.range levelCount))
          (fun offset => source.carrier index ∩ band offset) := by
        intro first _ second _ hne
        exact (hdisjoint first second hne).mono
          Set.inter_subset_right Set.inter_subset_right
      have hmeasurable : ∀ offset ∈ Finset.range levelCount,
          MeasurableSet (source.carrier index ∩ band offset) := by
        intro offset _
        exact (source.measurable_carrier index).inter
          (wz1PaperDyadicMultiplicityBand_measurable
            source (base + offset))
      have hunion : source.carrier index =
          ⋃ offset ∈ Finset.range levelCount,
            source.carrier index ∩ band offset := by
        apply Set.Subset.antisymm
        · intro point hpoint
          rcases Set.mem_iUnion₂.mp (hcover index hpoint) with
            ⟨offset, hoffset, hband⟩
          exact Set.mem_iUnion₂.mpr ⟨offset, hoffset, hpoint, hband⟩
        · exact Set.iUnion₂_subset fun _offset _hoffset =>
            Set.inter_subset_left
      calc
        volume (source.carrier index) =
            volume (⋃ offset ∈ Finset.range levelCount,
              source.carrier index ∩ band offset) := congrArg volume hunion
        _ = ∑ offset ∈ Finset.range levelCount,
              volume (source.carrier index ∩ band offset) :=
          MeasureTheory.measure_biUnion_finset hpairwise hmeasurable
    calc
      source.mass = ∑ index : Fin family.card,
          volume (source.carrier index) := by rfl
      _ = ∑ index : Fin family.card,
          ∑ offset ∈ Finset.range levelCount,
            volume (source.carrier index ∩ band offset) := by
        apply Finset.sum_congr rfl
        intro index _
        exact hperIndex index
      _ = ∑ offset ∈ Finset.range levelCount,
          ∑ index : Fin family.card,
            volume (source.carrier index ∩ band offset) := by
        rw [Finset.sum_comm]
      _ = ∑ offset ∈ Finset.range levelCount, bandMass offset := by
        apply Finset.sum_congr rfl
        intro offset _
        rfl
  have hlevelCount : 0 < levelCount := by
    dsimp only [levelCount]
    omega
  have hmax : ∃ offset ∈ Finset.range levelCount,
      ∀ other ∈ Finset.range levelCount,
        bandMass other ≤ bandMass offset :=
    Finset.exists_max_image (Finset.range levelCount) bandMass
      (Finset.nonempty_range_iff.mpr hlevelCount.ne')
  rcases hmax with ⟨offset, hoffset, hmaximal⟩
  let level := base + offset
  let selected := wz1PaperDyadicBandSubshading source level
  have hmass : source.mass ≤ (levelCount : ENNReal) * selected.mass := by
    rw [hmassDecomp]
    calc
      ∑ other ∈ Finset.range levelCount, bandMass other ≤
          ∑ _other ∈ Finset.range levelCount, bandMass offset := by
        apply Finset.sum_le_sum
        intro other hother
        exact hmaximal other hother
      _ = (levelCount : ENNReal) * bandMass offset := by
        simp [Finset.sum_const]
      _ = (levelCount : ENNReal) * selected.mass := by rfl
  have hlevelBase : Nat.log 2 m ≤ level := by
    simp [level, base]
  have hcubicalSelected : WZ1PaperIsCubicalShading selected :=
    hcubical.dyadicBandSubshading level
  have hmultiplicitySelected : ∀ point ∈ selected.union,
      (2 ^ level : ℕ) ≤ selected.pointMultiplicity point ∧
      selected.pointMultiplicity point < 2 ^ (level + 1) := by
    intro point hpoint
    have hpointBand : point ∈
        wz1PaperDyadicMultiplicityBand source level := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    have heq : selected.pointMultiplicity point =
        source.pointMultiplicity point := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro index _
      constructor
      · intro hindex
        exact hindex.1
      · intro hindex
        exact ⟨hindex, hpointBand⟩
    rw [heq]
    exact ⟨by exact_mod_cast hpointBand.1,
      by exact_mod_cast hpointBand.2⟩
  refine ⟨level, hlevelBase, hcubicalSelected,
    hmultiplicitySelected, ?_⟩
  simpa [levelCount, base, selected] using hmass

end Kakeya.Assouad.PureWZ2

end
