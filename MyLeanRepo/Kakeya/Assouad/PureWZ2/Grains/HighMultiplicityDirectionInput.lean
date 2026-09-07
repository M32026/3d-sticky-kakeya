import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseCloseDensityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17GridPruningBudget
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import Mathlib.Tactic

/-!
# High-multiplicity input for the dense/sparse direction split

The threshold is a fixed power times the ambient family cardinality.  Cropped
extremality makes its contribution to the union volume smaller than half the
aggregate shaded mass, so the explicit whole-cell high-multiplicity
restriction retains half the mass.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Round a finite ENNReal threshold to a natural number within a factor two. -/
lemma exists_nat_between_one_and_twice
    (D : ENNReal) (hD_one : 1 ≤ D) (hD_top : D ≠ ⊤) :
    ∃ m : ℕ, D ≤ (m : ENNReal) ∧ (m : ENNReal) ≤ 2 * D ∧ 0 < m := by
  let m : ℕ := Nat.ceil D.toReal
  have hDreal : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hceilLower : D.toReal ≤ (m : ℝ) := Nat.le_ceil _
  have hLower : D ≤ (m : ENNReal) := by
    rw [← ENNReal.ofReal_toReal hD_top]
    simpa [m] using ENNReal.ofReal_mono hceilLower
  have hceilUpper : (m : ℝ) < D.toReal + 1 :=
    Nat.ceil_lt_add_one hDreal
  have hDrealOne : 1 ≤ D.toReal := by
    have h := (ENNReal.toReal_le_toReal (by norm_num) hD_top).mpr hD_one
    simpa using h
  have hrealUpper : (m : ℝ) ≤ 2 * D.toReal := by linarith
  have hUpper : (m : ENNReal) ≤ 2 * D := by
    have hofReal : ENNReal.ofReal (m : ℝ) ≤
        ENNReal.ofReal (2 * D.toReal) :=
      ENNReal.ofReal_mono hrealUpper
    have hright : ENNReal.ofReal (2 * D.toReal) = 2 * D := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hD_top]
      norm_num
    simpa [hright] using hofReal
  have hm : 0 < m := by
    by_contra hzero
    have : m = 0 := Nat.eq_zero_of_not_pos hzero
    rw [this] at hLower
    simpa using hD_one.trans hLower
  exact ⟨m, hLower, hUpper, hm⟩

/-- The explicit high-multiplicity whole-cell restriction at a cardinality
power threshold. -/
theorem high_multiplicity_direction_input
    {delta sigma loss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (extremal :
      WZ2PaperCroppedIsExtremal sigma loss family source)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (hloss : 0 < loss)
    (hsmall : Kakeya.realRpowENN delta loss < 1 / 4) :
    ∃ (m : ℕ) (selected : WZ1PaperTubeShading family),
      PaperIsSubshading selected source ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        m ≤ selected.pointMultiplicity point) ∧
      Kakeya.realRpowENN delta densityLoss * family.enncard ≤
        (m : ENNReal) ∧
      (1 / 2 : ENNReal) * source.mass ≤ selected.mass ∧
      (∀ index, selected.carrier index =
        source.carrier index ∩ selected.union) ∧
      0 < m := by
  have hdelta : 0 < delta := extremal.delta_pos
  let D : ENNReal :=
    Kakeya.realRpowENN delta densityLoss * family.enncard
  have hD_top : D ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [Kakeya.realRpowENN]
    · simp [Kakeya.Streamlined.TubeFamily.enncard]
  by_cases hDone : D ≤ 1
  · have hmult : ∀ point ∈ source.union,
        1 ≤ source.pointMultiplicity point := by
      intro point hpoint
      rcases hpoint with ⟨index, hindex⟩
      apply Finset.one_le_card.mpr
      refine ⟨index, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hindex
    have hmass : (1 / 2 : ENNReal) * source.mass ≤ source.mass := by
      calc
        (1 / 2 : ENNReal) * source.mass ≤ 1 * source.mass := by
          exact mul_le_mul_right' (by norm_num) source.mass
        _ = source.mass := by simp
    exact ⟨1, source, (fun _ => Set.Subset.rfl), extremal.cubical,
      hmult, (by simpa [D] using hDone), hmass, (by
        intro index
        ext point
        constructor
        · intro hpoint
          exact ⟨hpoint, ⟨index, hpoint⟩⟩
        · exact fun hpoint => hpoint.1), by norm_num⟩
  · have hDone' : 1 ≤ D := le_of_not_ge hDone
    rcases exists_nat_between_one_and_twice D hDone' hD_top with
      ⟨m, hDLower, hDUpper, hm⟩
    let high := paperHighMultiplicitySet source (m : ENNReal)
    let selected := paperRestrictShadingToSet source high
      (measurableSet_paperHighMultiplicitySet source (m : ENNReal))
    have hmassTop : source.mass ≠ ⊤ := by
      have hupper := wz2_paper_shading_mass_upper hdelta hdeltaSmall
        hline source
      have hvolumeOne : Kakeya.deltaTubeVolume 1 ≠ ⊤ :=
        (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).2
      have hconstant :
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) hvolumeOne
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hconstant (by
          simp [Kakeya.realRpowENN])) (by
          simp [Kakeya.Streamlined.TubeFamily.enncard])) hupper
    have hambient :
        Kakeya.realRpowENN delta (loss + 2) * family.enncard ≤
          source.mass := by
      have hbody := paperBodyFamily_mass_lower_rpow_two
        hdelta (hdeltaSmall.trans (by norm_num)) hline
      calc
        Kakeya.realRpowENN delta (loss + 2) * family.enncard =
            Kakeya.realRpowENN delta loss *
              (Kakeya.realRpowENN delta 2 * family.enncard) := by
                rw [Kakeya.Assouad.realRpowENN_add hdelta]
                ring
        _ ≤ Kakeya.realRpowENN delta loss *
            (wz1PaperBodyFamily family).mass := by gcongr
        _ ≤ source.mass := extremal.dense
    have hthresholdVolume :
        (m : ENNReal) * volume source.union <
          (1 / 2 : ENNReal) * source.mass := by
      have hvolume := extremal.volume_upper
      have hfirst :
          (m : ENNReal) * volume source.union ≤
            (2 * D) * Kakeya.realRpowENN delta (sigma - loss) := by
        calc
          (m : ENNReal) * volume source.union ≤
              (2 * D) * volume source.union := by gcongr
          _ ≤ (2 * D) *
              Kakeya.realRpowENN delta (sigma - loss) := by gcongr
      let B := Kakeya.realRpowENN delta (loss + 2) * family.enncard
      have hB_zero : B ≠ 0 := by
        apply mul_ne_zero
        · simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
        · change (family.card : ENNReal) ≠ 0
          exact_mod_cast Nat.one_le_iff_ne_zero.mp extremal.nonempty
      have hB_top : B ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · simp [Kakeya.realRpowENN]
        · simp [Kakeya.Streamlined.TubeFamily.enncard]
      have hcoeff :
          2 * Kakeya.realRpowENN delta loss < (1 / 2 : ENNReal) := by
        have htwo : (2 : ENNReal) ≠ 0 := by norm_num
        have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
        calc
          2 * Kakeya.realRpowENN delta loss < 2 * (1 / 4 : ENNReal) := by
            simpa [mul_comm] using
              (ENNReal.mul_lt_mul_left htwo htwoTop hsmall)
          _ = (1 / 2 : ENNReal) := by
            apply (ENNReal.toReal_eq_toReal_iff'
              (ENNReal.mul_ne_top (by norm_num) (by simp [one_div]))
              (by simp [one_div])).mp
            norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      have hrewrite :
          (2 * D) * Kakeya.realRpowENN delta (sigma - loss) =
            (2 * Kakeya.realRpowENN delta loss) * B := by
        dsimp only [D, B]
        rw [hdensityLoss]
        have hfirstPower :
            Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
                Kakeya.realRpowENN delta (sigma - loss) =
              Kakeya.realRpowENN delta (2 + 2 * loss) := by
          rw [← Kakeya.Assouad.realRpowENN_add hdelta]
          congr 1
          ring
        have hsecondPower :
            Kakeya.realRpowENN delta loss *
                Kakeya.realRpowENN delta (loss + 2) =
              Kakeya.realRpowENN delta (2 + 2 * loss) := by
          rw [← Kakeya.Assouad.realRpowENN_add hdelta]
          congr 1
          ring
        calc
          (2 * (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
              family.enncard)) * Kakeya.realRpowENN delta (sigma - loss) =
              2 *
                (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
                  Kakeya.realRpowENN delta (sigma - loss)) *
                family.enncard := by ring
          _ = 2 * Kakeya.realRpowENN delta (2 + 2 * loss) *
                family.enncard := by rw [hfirstPower]
          _ = 2 *
                (Kakeya.realRpowENN delta loss *
                  Kakeya.realRpowENN delta (loss + 2)) *
                family.enncard := by rw [hsecondPower]
          _ = (2 * Kakeya.realRpowENN delta loss) *
                (Kakeya.realRpowENN delta (loss + 2) *
                  family.enncard) := by ring
      have hstrict :
          (2 * D) * Kakeya.realRpowENN delta (sigma - loss) <
            (1 / 2 : ENNReal) * B := by
        rw [hrewrite]
        simpa [mul_comm] using
          (ENNReal.mul_lt_mul_right hB_zero hB_top hcoeff)
      exact hfirst.trans_lt <| hstrict.trans_le <|
        mul_le_mul_left' hambient (1 / 2 : ENNReal)
    have hmass : (1 / 2 : ENNReal) * source.mass ≤ selected.mass := by
      exact paperHighMultiplicityRestriction_half_mass hmassTop
        hthresholdVolume
    have hcubical : WZ1PaperIsCubicalShading selected :=
      paperHighMultiplicityRestriction_cubical extremal.cubical
    have hsub : PaperIsSubshading selected source :=
      fun _ _ hpoint => hpoint.1
    have hmult : ∀ point ∈ selected.union,
        m ≤ selected.pointMultiplicity point := by
      intro point hpoint
      have hpointHigh : point ∈ high := by
        rcases hpoint with ⟨index, hindex⟩
        exact hindex.2
      have heq := paperPmRestrictShadingToSet
        (Z := source)
        (measurableSet_paperHighMultiplicitySet source (m : ENNReal))
        hpointHigh
      have hlower : (m : ENNReal) ≤
          (source.pointMultiplicity point : ENNReal) := hpointHigh.2
      have hlower' : (m : ENNReal) ≤
          (selected.pointMultiplicity point : ENNReal) := by
        simpa [selected] using hlower.trans_eq
          (congrArg (fun n : ℕ => (n : ENNReal)) heq.symm)
      exact_mod_cast hlower'
    have hunion : selected.union = high := by
      ext point
      simp only [selected, paperRestrictShadingToSet,
        Kakeya.Streamlined.Shading.union, Set.mem_iUnion]
      constructor
      · rintro ⟨index, hpoint⟩
        exact hpoint.2
      · intro hpoint
        rcases hpoint.1 with ⟨index, hindex⟩
        exact ⟨index, hindex, hpoint⟩
    have hcommon : ∀ index, selected.carrier index =
        source.carrier index ∩ selected.union := by
      intro index
      change source.carrier index ∩ high =
        source.carrier index ∩ selected.union
      rw [hunion]
    exact ⟨m, selected, hsub, hcubical, hmult, hDLower, hmass,
      hcommon, hm⟩

end Kakeya.Assouad.PureWZ2

end
