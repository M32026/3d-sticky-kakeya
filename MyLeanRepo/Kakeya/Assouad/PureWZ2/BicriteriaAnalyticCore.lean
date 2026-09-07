import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.WeightedSelection
import MyLeanRepo.Kakeya.Assouad.Targets.WeightedEssentiallyDistinctSelection
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedTubeCardinalityRetentionFromMass

/-!
# Bicriteria analytic core from a conflict-degree bound

A weighted essentially-distinct selection retains shaded mass.  The same
mass inequality, together with ambient shading density and the common volume
of equal-radius tubes, forces indexed-cardinality retention for that exact
selected family.  Thus no second cardinality selection is required.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Select one analytic essentially-distinct core that simultaneously retains
shaded mass, aggregate density, and indexed cardinality.

The geometric input is only an `ENNReal` upper bound for every broad conflict
neighborhood.  In the literal WZ2 application this bound comes from the
public body's Convex-Wolff estimate.
-/
theorem pure_wz2_bicriteria_analytic_core_of_degree
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : Kakeya.Streamlined.TubeShading family)
    (densityConstant conflictBound : ENNReal)
    (hdense : shading.IsLambdaDense densityConstant)
    (hconflictTop : conflictBound ≠ ⊤)
    (hdegree :
      ∀ index,
        ((Finset.univ.filter fun other =>
          ¬(family.tube index).EssentiallyDistinct
            (family.tube other)).card : ENNReal) ≤
          conflictBound) :
    ∃ selected : Finset (Fin family.card),
      let selectedFamily := selectedTubeFamily family selected
      let selectedShading := selectedTubeShading shading selected
      selectedFamily.IsEssentiallyDistinct ∧
        selectedShading.union ⊆ shading.union ∧
        shading.mass ≤
          (conflictBound + 1) * selectedShading.mass ∧
        ((conflictBound + 1)⁻¹ * densityConstant) *
            family.enncard ≤
          selectedFamily.enncard ∧
        selectedShading.IsLambdaDense
          ((conflictBound + 1)⁻¹ * densityConstant) := by
  rcases
      weighted_essentially_distinct_shading_refinement_of_broad_ennreal_degree
        weighted_essentially_distinct_selection
        family shading conflictBound hdegree with
    ⟨selected, hdistinct, hunion, hmass⟩
  let loss : ENNReal := conflictBound + 1
  have hlossZero : loss ≠ 0 := by
    have hone : (0 : ENNReal) < 1 := by norm_num
    exact (lt_of_lt_of_le hone (le_add_left le_rfl)).ne'
  have hlossTop : loss ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hconflictTop, by norm_num⟩
  have hcardinality :
      (loss⁻¹ * densityConstant) * family.enncard ≤
        (selectedTubeFamily family selected).enncard := by
    exact
      selected_tube_cardinality_retention_from_mass
        tube_volume_scaling hdelta hdeltaOne family shading selected
        densityConstant loss hdense (by simpa [loss] using hmass)
        hlossZero hlossTop
  have hdensityProduct :
      densityConstant *
          (selectedTubeFamily family selected).toBodyFamily.mass ≤
        loss * (selectedTubeShading shading selected).mass :=
    selectedTubeShading_density_product
      shading selected densityConstant loss hdense
        (by simpa [loss] using hmass)
  have hselectedDense :
      (selectedTubeShading shading selected).IsLambdaDense
        (loss⁻¹ * densityConstant) := by
    calc
      (loss⁻¹ * densityConstant) *
          (selectedTubeFamily family selected).toBodyFamily.mass =
        loss⁻¹ *
          (densityConstant *
            (selectedTubeFamily family selected).toBodyFamily.mass) := by
              ring
      _ ≤ loss⁻¹ *
          (loss * (selectedTubeShading shading selected).mass) := by
            gcongr
      _ = (selectedTubeShading shading selected).mass := by
        exact ENNReal.inv_mul_cancel_left hlossZero hlossTop
  refine ⟨selected, hdistinct, hunion, hmass, ?_, ?_⟩
  · simpa [loss] using hcardinality
  · simpa [loss] using hselectedDense

/--
The Assertion-D-ready form of the same selection.

If every ambient shaded tube already has density `densityConstant`, then the
selected shading keeps that density with no conflict-degree loss.  The
weighted selection is still used for cardinality retention on the same core.
-/
theorem pure_wz2_bicriteria_analytic_core_of_degree_and_per_tube
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hfamilyNonempty : family.Nonempty)
    (shading : Kakeya.Streamlined.TubeShading family)
    (densityConstant conflictBound : ENNReal)
    (hdensityPositive : 0 < densityConstant)
    (hconflictTop : conflictBound ≠ ⊤)
    (hperTube :
      ∀ index,
        densityConstant * (family.tube index).volume ≤
          MeasureTheory.volume (shading.carrier index))
    (hdegree :
      ∀ index,
        ((Finset.univ.filter fun other =>
          ¬(family.tube index).EssentiallyDistinct
            (family.tube other)).card : ENNReal) ≤
          conflictBound) :
    ∃ selected : Finset (Fin family.card),
      let selectedFamily := selectedTubeFamily family selected
      let selectedShading := selectedTubeShading shading selected
      selected.Nonempty ∧
        selectedFamily.IsEssentiallyDistinct ∧
        selectedShading.union ⊆ shading.union ∧
        shading.mass ≤
          (conflictBound + 1) * selectedShading.mass ∧
        ((conflictBound + 1)⁻¹ * densityConstant) *
            family.enncard ≤
          selectedFamily.enncard ∧
        selectedShading.IsLambdaDense densityConstant := by
  have hdense : shading.IsLambdaDense densityConstant := by
    change
      densityConstant *
          (∑ index : Fin family.card, (family.tube index).volume) ≤
        ∑ index : Fin family.card,
          MeasureTheory.volume (shading.carrier index)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun index _ => hperTube index
  rcases
      pure_wz2_bicriteria_analytic_core_of_degree
        hdelta hdeltaOne family shading densityConstant conflictBound
        hdense hconflictTop hdegree with
    ⟨selected, hdistinct, hunion, hmass, hcardinality, _hdensityWeakened⟩
  let loss : ENNReal := conflictBound + 1
  have hlossZero : loss ≠ 0 := by
    have hone : (0 : ENNReal) < 1 := by norm_num
    exact (lt_of_lt_of_le hone (le_add_left le_rfl)).ne'
  have hlossTop : loss ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hconflictTop, by norm_num⟩
  have hlossInversePositive : 0 < loss⁻¹ :=
    ENNReal.inv_pos.mpr hlossTop
  have hfamilyCardPositive : 0 < family.enncard := by
    change 0 < (family.card : ENNReal)
    exact_mod_cast hfamilyNonempty
  have hfractionPositive :
      0 < (loss⁻¹ * densityConstant) * family.enncard :=
    ENNReal.mul_pos
      (ENNReal.mul_pos hlossInversePositive.ne'
        hdensityPositive.ne').ne'
      hfamilyCardPositive.ne'
  have hselectedCardPositive :
      0 < (selectedTubeFamily family selected).enncard :=
    hfractionPositive.trans_le (by simpa [loss] using hcardinality)
  have hselectedNonempty : selected.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (selected.card : ENNReal) at hselectedCardPositive
    exact_mod_cast hselectedCardPositive
  have hselectedDense :
      (selectedTubeShading shading selected).IsLambdaDense
        densityConstant := by
    change
      densityConstant *
          (selectedTubeFamily family selected).toBodyFamily.mass ≤
        (selectedTubeShading shading selected).mass
    rw [selectedTubeFamily_mass, selectedTubeShading_mass,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun index membership =>
      hperTube index
  refine
    ⟨selected, hselectedNonempty, hdistinct, hunion, hmass,
      hcardinality, hselectedDense⟩

end Kakeya.Assouad

end
