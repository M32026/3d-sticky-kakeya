import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Cubical multiplicity selection for WZ2 `prop: sticky`

Select one dyadic point-multiplicity band while preserving whole literal
paper cells and a logarithmic fraction of the shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

private lemma paperDyadicBand_disjoint_of_lt
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {first second : ℕ}
    (hlt : first < second) :
    Disjoint
      (wz1PaperDyadicMultiplicityBand shading first)
      (wz1PaperDyadicMultiplicityBand shading second) := by
  apply Set.disjoint_left.mpr
  intro point hfirst hsecond
  have hlevels : first + 1 ≤ second := by omega
  have hpowers :
      (2 ^ (first + 1) : ENNReal) ≤
        (2 ^ second : ENNReal) := by
    exact_mod_cast
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hlevels
  exact
    (not_le_of_gt hfirst.2)
      (hpowers.trans hsecond.1)

private lemma paperDyadicBand_disjoint
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {first second : ℕ}
    (hne : first ≠ second) :
    Disjoint
      (wz1PaperDyadicMultiplicityBand shading first)
      (wz1PaperDyadicMultiplicityBand shading second) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact paperDyadicBand_disjoint_of_lt hlt
  · exact (paperDyadicBand_disjoint_of_lt hgt).symm

private lemma point_mem_paperDyadicBand
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {index : Fin family.card}
    {point : Point3}
    (hpoint : point ∈ shading.carrier index) :
    ∃ level ∈ Finset.range (Nat.log 2 family.card + 1),
      point ∈
        wz1PaperDyadicMultiplicityBand shading level := by
  let multiplicity := shading.pointMultiplicity point
  have hindex :
      index ∈
        Finset.univ.filter fun candidate : Fin family.card =>
          point ∈ shading.carrier candidate := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpoint
  have hmultiplicity_pos : 0 < multiplicity := by
    exact Finset.card_pos.mpr ⟨index, hindex⟩
  have hmultiplicity_le :
      multiplicity ≤ family.card := by
    change
      (Finset.univ.filter
        (fun candidate : Fin family.card =>
          point ∈ shading.carrier candidate)).card ≤
        family.card
    have hsubset :
        Finset.univ.filter
            (fun candidate : Fin family.card =>
              point ∈ shading.carrier candidate) ⊆
          (Finset.univ : Finset (Fin family.card)) :=
      Finset.filter_subset _ _
    simpa using Finset.card_le_card hsubset
  let level := Nat.log 2 multiplicity
  have hlower :
      (2 : ℕ) ^ level ≤ multiplicity :=
    Nat.pow_log_le_self 2 hmultiplicity_pos.ne'
  have hupper :
      multiplicity < (2 : ℕ) ^ (level + 1) := by
    apply Nat.lt_pow_of_log_lt (by norm_num)
    simp [level]
  have hlevel :
      level < Nat.log 2 family.card + 1 := by
    have hlog :
        Nat.log 2 multiplicity ≤
          Nat.log 2 family.card :=
      Nat.log_mono_right hmultiplicity_le
    omega
  refine ⟨level, Finset.mem_range.mpr hlevel, ?_⟩
  constructor
  · exact_mod_cast hlower
  · exact_mod_cast hupper

private lemma paperDyadicBands_partition
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (index : Fin family.card) :
    shading.carrier index =
      ⋃ level ∈
          Finset.range (Nat.log 2 family.card + 1),
        shading.carrier index ∩
          wz1PaperDyadicMultiplicityBand shading level := by
  ext point
  constructor
  · intro hpoint
    rcases point_mem_paperDyadicBand hpoint with
      ⟨level, hlevel, hband⟩
    exact
      Set.mem_iUnion.mpr
        ⟨level,
          Set.mem_iUnion.mpr
            ⟨hlevel, hpoint, hband⟩⟩
  · intro hpoint
    rcases Set.mem_iUnion.mp hpoint with
      ⟨level, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with
      ⟨_, hpoint, _⟩
    exact hpoint

/--
The paper shading mass is the sum of the masses of all dyadic
point-multiplicity bands.
-/
theorem paperDyadicBands_mass_sum
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family} :
    shading.mass =
      ∑ level ∈
          Finset.range (Nat.log 2 family.card + 1),
        (wz1PaperDyadicBandSubshading
          shading level).mass := by
  let levels :=
    Finset.range (Nat.log 2 family.card + 1)
  have hcarrier :
      ∀ index : Fin family.card,
        volume (shading.carrier index) =
          ∑ level ∈ levels,
            volume
              (shading.carrier index ∩
                wz1PaperDyadicMultiplicityBand
                  shading level) := by
    intro index
    let pieces : ℕ → Set Point3 :=
      fun level =>
        shading.carrier index ∩
          wz1PaperDyadicMultiplicityBand shading level
    have hdisjoint :
        (levels : Set ℕ).PairwiseDisjoint pieces := by
      intro first _ second _ hne
      exact
        (paperDyadicBand_disjoint hne).mono
          Set.inter_subset_right Set.inter_subset_right
    have hmeasurable :
        ∀ level ∈ levels,
          MeasurableSet (pieces level) := by
      intro level _
      exact
        (shading.measurable_carrier index).inter
          (wz1PaperDyadicMultiplicityBand_measurable
            shading level)
    have hpartition :
        shading.carrier index =
          ⋃ level ∈ levels, pieces level := by
      simpa [levels, pieces] using
        paperDyadicBands_partition index
    calc
      volume (shading.carrier index) =
          volume (⋃ level ∈ levels, pieces level) := by
        rw [hpartition]
      _ = ∑ level ∈ levels, volume (pieces level) :=
        MeasureTheory.measure_biUnion_finset
          hdisjoint hmeasurable
  calc
    shading.mass =
        ∑ index : Fin family.card,
          volume (shading.carrier index) := rfl
    _ =
        ∑ index : Fin family.card,
          ∑ level ∈ levels,
            volume
              (shading.carrier index ∩
                wz1PaperDyadicMultiplicityBand
                  shading level) := by
      apply Finset.sum_congr rfl
      intro index _
      exact hcarrier index
    _ =
        ∑ level ∈ levels,
          ∑ index : Fin family.card,
            volume
              (shading.carrier index ∩
                wz1PaperDyadicMultiplicityBand
                  shading level) := by
      rw [Finset.sum_comm]
    _ =
        ∑ level ∈ levels,
          (wz1PaperDyadicBandSubshading
            shading level).mass := by
      rfl

/--
Select one cubical dyadic point-multiplicity band retaining a logarithmic
fraction of the total shaded mass.
-/
theorem paperDyadicBandPigeonhole
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    ∃ level : ℕ,
      let band :=
        wz1PaperDyadicBandSubshading shading level
      WZ1PaperIsCubicalShading band ∧
      shading.mass /
          (↑(Nat.log 2 family.card + 1) : ENNReal) ≤
        band.mass ∧
      ∀ point ∈ band.union,
        (2 ^ level : ENNReal) ≤
            (band.pointMultiplicity point : ENNReal) ∧
          (band.pointMultiplicity point : ENNReal) <
            (2 ^ (level + 1) : ENNReal) := by
  let levels :=
    Finset.range (Nat.log 2 family.card + 1)
  let bandMass : ℕ → ENNReal :=
    fun level =>
      (wz1PaperDyadicBandSubshading
        shading level).mass
  have hlevels : levels.Nonempty := by
    simp [levels]
  rcases Finset.exists_max_image
      levels bandMass hlevels with
    ⟨level, hlevel, hmax⟩
  refine ⟨level, ?_⟩
  let band :=
    wz1PaperDyadicBandSubshading shading level
  have hsum :
      shading.mass =
        ∑ candidate ∈ levels,
          bandMass candidate := by
    simpa [levels, bandMass] using
      (paperDyadicBands_mass_sum
        (shading := shading))
  have hsum_le :
      ∑ candidate ∈ levels,
          bandMass candidate ≤
        levels.card • bandMass level :=
    Finset.sum_le_card_nsmul
      levels bandMass (bandMass level) hmax
  have hcard :
      (levels.card : ENNReal) =
        (Nat.log 2 family.card + 1 : ℕ) := by
    simp [levels]
  have hcard_ne_zero :
      (levels.card : ENNReal) ≠ 0 := by
    exact_mod_cast hlevels.card_pos.ne'
  have hcard_ne_top :
      (levels.card : ENNReal) ≠ ⊤ := by
    simp
  have hmass :
      shading.mass /
          (levels.card : ENNReal) ≤
        bandMass level := by
    rw [ENNReal.div_le_iff hcard_ne_zero hcard_ne_top]
    rw [hsum]
    simpa [nsmul_eq_mul, mul_comm] using hsum_le
  refine
    ⟨hcubical.dyadicBandSubshading level,
      ?_, ?_⟩
  · simpa [band, bandMass, hcard] using hmass
  · intro point hpoint
    have hband :
        point ∈
          wz1PaperDyadicMultiplicityBand
            shading level := by
      rcases hpoint with ⟨index, hpoint⟩
      exact hpoint.2
    have hmultiplicity :
        band.pointMultiplicity point =
          shading.pointMultiplicity point := by
      classical
      simp only
        [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro index _
      change
        (point ∈ shading.carrier index ∧
            point ∈
              wz1PaperDyadicMultiplicityBand
                shading level) ↔
          point ∈ shading.carrier index
      exact
        and_iff_left hband
    rw [hmultiplicity]
    exact hband

end Kakeya.Assouad
