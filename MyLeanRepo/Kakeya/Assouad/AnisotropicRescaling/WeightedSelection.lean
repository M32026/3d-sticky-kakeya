import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.BoundedFamilyAssembly
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily

/-!
# Weighted essential-distinctness cleanup

Apply the abstract bounded-conflict selection theorem to the actual carrier
volumes of a tube shading, then reindex the selected tubes and shaded pieces.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Indices whose shaded carrier has positive measure. -/
def positiveMassIndices
    {rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    (Y : Kakeya.Streamlined.TubeShading F) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    MeasureTheory.volume (Y.carrier i) ≠ 0

/-- Membership in `positiveMassIndices` is the positive-volume certificate. -/
lemma volume_ne_zero_of_mem_positiveMassIndices
    {rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    (Y : Kakeya.Streamlined.TubeShading F)
    {i : Fin F.card}
    (hi : i ∈ positiveMassIndices Y) :
    MeasureTheory.volume (Y.carrier i) ≠ 0 := by
  exact (Finset.mem_filter.mp hi).2

/-- Discarding zero-mass shaded carriers preserves total shaded mass exactly. -/
lemma selectedTubeShading_positiveMass_mass
    {rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    (Y : Kakeya.Streamlined.TubeShading F) :
    (selectedTubeShading Y (positiveMassIndices Y)).mass = Y.mass := by
  rw [selectedTubeShading_mass]
  change
    (∑ i ∈ positiveMassIndices Y,
      MeasureTheory.volume (Y.carrier i)) =
      ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i)
  symm
  rw [Finset.sum_subset
    (show positiveMassIndices Y ⊆ Finset.univ from by simp)]
  intro i _ hi
  have hi' :
      ¬MeasureTheory.volume (Y.carrier i) ≠ 0 := by
    simpa [positiveMassIndices] using hi
  exact not_ne_iff.mp hi'

/-- Every shaded carrier has finite volume because it lies in a compact tube. -/
lemma tubeShading_carrier_volume_ne_top
    {rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    (Y : Kakeya.Streamlined.TubeShading F)
    (i : Fin F.card) :
    MeasureTheory.volume (Y.carrier i) ≠ ⊤ := by
  have hsegment :
      IsCompact (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have htube : IsCompact (F.tube i).carrier := by
    simpa [Kakeya.DeltaTube.carrier] using hsegment.cthickening
  have hle :
      MeasureTheory.volume (Y.carrier i) ≤
        MeasureTheory.volume (F.tube i).carrier :=
    MeasureTheory.measure_mono (Y.subset_body i)
  exact (hle.trans_lt htube.measure_lt_top).ne

/--
Select a pairwise essentially-distinct subfamily while retaining the carrier
mass guaranteed by a bounded conflict degree.
-/
lemma weighted_essentially_distinct_shading_refinement
    (hselect : WeightedEssentiallyDistinctSelectionStatement)
    {rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily rho)
    (Y : Kakeya.Streamlined.TubeShading F)
    (D : ℕ)
    (hdegree :
      ∀ i,
        (Finset.univ.filter fun j =>
          j ≠ i ∧
            ¬(F.tube i).EssentiallyDistinct (F.tube j)).card ≤ D) :
    ∃ selected : Finset (Fin F.card),
      let coarse := selectedTubeFamily F selected
      let Z := selectedTubeShading Y selected
      coarse.IsEssentiallyDistinct ∧
        Z.union ⊆ Y.union ∧
        Y.mass ≤ (D + 1 : ENNReal) * Z.mass := by
  let weight : Fin F.card → ENNReal :=
    fun i => MeasureTheory.volume (Y.carrier i)
  have hweight : ∀ i, weight i ≠ ⊤ := by
    intro i
    exact tubeShading_carrier_volume_ne_top Y i
  rcases hselect F weight hweight D hdegree with
    ⟨selected, hdistinct, hmass⟩
  refine ⟨selected, ?_, selectedTubeShading_union_subset Y selected, ?_⟩
  · exact selectedTubeFamily_isEssentiallyDistinct F selected hdistinct
  · rw [selectedTubeShading_mass]
    exact hmass

/--
ENNReal-valued version of bounded-degree weighted cleanup.

The actual finite graph degree is still a natural number, chosen internally
as the maximum over the finite family.  A uniform ENNReal bound `K` then
controls the mass loss by `K + 1`, avoiding any external rounding convention.
-/
lemma weighted_essentially_distinct_shading_refinement_of_ennreal_degree
    (hselect : WeightedEssentiallyDistinctSelectionStatement)
    {rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily rho)
    (Y : Kakeya.Streamlined.TubeShading F)
    (K : ENNReal)
    (hdegree :
      ∀ i,
        ((Finset.univ.filter fun j =>
          j ≠ i ∧
            ¬(F.tube i).EssentiallyDistinct (F.tube j)).card : ENNReal) ≤ K) :
    ∃ selected : Finset (Fin F.card),
      let coarse := selectedTubeFamily F selected
      let Z := selectedTubeShading Y selected
      coarse.IsEssentiallyDistinct ∧
        Z.union ⊆ Y.union ∧
        Y.mass ≤ (K + 1) * Z.mass := by
  let conflictDegree : Fin F.card → ℕ := fun i =>
    (Finset.univ.filter fun j =>
      j ≠ i ∧
        ¬(F.tube i).EssentiallyDistinct (F.tube j)).card
  let D : ℕ := Finset.univ.sup conflictDegree
  have hdegreeNat : ∀ i, conflictDegree i ≤ D := by
    intro i
    exact Finset.le_sup (Finset.mem_univ i)
  rcases weighted_essentially_distinct_shading_refinement
      hselect F Y D hdegreeNat with
    ⟨selected, hdistinct, hunion, hmass⟩
  have hD : (D : ENNReal) ≤ K := by
    by_cases hcard : F.card = 0
    · have hDzero : D = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro i _hi
        have himpossible : i.val < 0 := by
          simpa [hcard] using i.isLt
        omega
      simp [hDzero]
    · have hnonempty : (Finset.univ : Finset (Fin F.card)).Nonempty := by
        have hpos : 0 < F.card := Nat.pos_of_ne_zero hcard
        exact ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
      rcases Finset.exists_mem_eq_sup Finset.univ hnonempty conflictDegree with
        ⟨i, _hi, hDi⟩
      have hDi' : D = conflictDegree i := by
        exact hDi
      rw [hDi']
      simpa [conflictDegree] using hdegree i
  refine ⟨selected, hdistinct, hunion, hmass.trans ?_⟩
  gcongr

/--
The same cleanup from the slightly larger conflict count that includes the
reference tube itself.  This is the natural output of parameter-cluster
counting and immediately dominates the loop-free graph degree.
-/
lemma weighted_essentially_distinct_shading_refinement_of_broad_ennreal_degree
    (hselect : WeightedEssentiallyDistinctSelectionStatement)
    {rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily rho)
    (Y : Kakeya.Streamlined.TubeShading F)
    (K : ENNReal)
    (hdegree :
      ∀ i,
        ((Finset.univ.filter fun j =>
          ¬(F.tube i).EssentiallyDistinct (F.tube j)).card : ENNReal) ≤ K) :
    ∃ selected : Finset (Fin F.card),
      let coarse := selectedTubeFamily F selected
      let Z := selectedTubeShading Y selected
      coarse.IsEssentiallyDistinct ∧
        Z.union ⊆ Y.union ∧
        Y.mass ≤ (K + 1) * Z.mass := by
  apply weighted_essentially_distinct_shading_refinement_of_ennreal_degree
    hselect F Y K
  intro i
  let narrow : Finset (Fin F.card) :=
    Finset.univ.filter fun j =>
      j ≠ i ∧ ¬(F.tube i).EssentiallyDistinct (F.tube j)
  let broad : Finset (Fin F.card) :=
    Finset.univ.filter fun j =>
      ¬(F.tube i).EssentiallyDistinct (F.tube j)
  have hsubset : narrow ⊆ broad := by
    intro j hj
    have hj' :
        j ≠ i ∧ ¬(F.tube i).EssentiallyDistinct (F.tube j) := by
      dsimp only [narrow] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    dsimp only [broad]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj'.2⟩
  have hcard : (narrow.card : ENNReal) ≤ (broad.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hcard.trans (by
    simpa [broad] using hdegree i)

/--
Cancellation-free density transfer to a selected tube family.

If the original shading is `lambda`-dense and the selected shading loses at
most the explicit factor `L`, then `lambda * selectedFamily.mass` is at most
`L * selectedShading.mass`.  The product form remains valid when a family is
empty or one of the masses is zero or infinite.
-/
lemma selectedTubeShading_density_product
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (selected : Finset (Fin F.card))
    (lambda L : ENNReal)
    (hdense : Y.IsLambdaDense lambda)
    (hmass :
      Y.mass ≤ L * (selectedTubeShading Y selected).mass) :
    lambda *
        (selectedTubeFamily F selected).toBodyFamily.mass ≤
      L * (selectedTubeShading Y selected).mass := by
  calc
    lambda * (selectedTubeFamily F selected).toBodyFamily.mass
        ≤ lambda * F.toBodyFamily.mass := by
      gcongr
      exact selectedTubeFamily_mass_le F selected
    _ ≤ Y.mass := hdense
    _ ≤ L * (selectedTubeShading Y selected).mass := hmass

/--
Convert a natural-number weighted-selection loss to an actual density.

The factor `K + 1` is automatically nonzero and finite in `ENNReal`, so the
product inequality can be cancelled without any hypothesis on the family or
shading masses.
-/
lemma selectedTubeShading_isLambdaDense_of_nat_loss
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (selected : Finset (Fin F.card))
    (lambda : ENNReal) (K : ℕ)
    (hdense : Y.IsLambdaDense lambda)
    (hmass :
      Y.mass ≤
        (K + 1 : ENNReal) *
          (selectedTubeShading Y selected).mass) :
    (selectedTubeShading Y selected).IsLambdaDense
      ((K + 1 : ENNReal)⁻¹ * lambda) := by
  have hproduct :=
    selectedTubeShading_density_product
      Y selected lambda (K + 1 : ENNReal) hdense hmass
  have hnonzero : (K + 1 : ENNReal) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero K
  have hfinite : (K + 1 : ENNReal) ≠ ⊤ := by
    simp
  calc
    ((K + 1 : ENNReal)⁻¹ * lambda) *
        (selectedTubeFamily F selected).toBodyFamily.mass =
      (K + 1 : ENNReal)⁻¹ *
        (lambda *
          (selectedTubeFamily F selected).toBodyFamily.mass) := by
        ring
    _ ≤ (K + 1 : ENNReal)⁻¹ *
        ((K + 1 : ENNReal) *
          (selectedTubeShading Y selected).mass) := by
        gcongr
    _ = (selectedTubeShading Y selected).mass := by
      exact ENNReal.inv_mul_cancel_left hnonzero hfinite

/--
Apply weighted conflict cleanup to the source-indexed anisotropic target
shading.  The only unresolved geometric input is the explicit conflict degree
of the flattened target family.
-/
lemma weighted_anisotropic_target_refinement
    (hselect : WeightedEssentiallyDistinctSelectionStatement)
    {delta rho c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d))
    (D : ℕ)
    (hdegree :
      let raw :=
        flattenThreeTubeImageCover F
          (anisotropicRescalingMap g c d m)
          (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
      ∀ i,
        (Finset.univ.filter fun j =>
          j ≠ i ∧
            ¬(raw.tube i).EssentiallyDistinct (raw.tube j)).card ≤ D) :
    let raw :=
      flattenThreeTubeImageCover F
        (anisotropicRescalingMap g c d m)
        (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
    let rawShading := sourceIndexedAnisotropicTargetShading F Y g W
    ∃ selected : Finset (Fin raw.card),
      let coarse := selectedTubeFamily raw selected
      let Z := selectedTubeShading rawShading selected
      coarse.IsEssentiallyDistinct ∧
        Z.union ⊆ rawShading.union ∧
        ENNReal.ofReal m * shadedMassInSlab Y c d ≤
          (D + 1 : ENNReal) * Z.mass := by
  let raw :=
    flattenThreeTubeImageCover F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
  let rawShading := sourceIndexedAnisotropicTargetShading F Y g W
  rcases weighted_essentially_distinct_shading_refinement
      hselect raw rawShading D hdegree with
    ⟨selected, hdistinct, hunion, hmass⟩
  refine ⟨selected, hdistinct, hunion, ?_⟩
  exact
    (sourceIndexedAnisotropicTargetShading_mass_lower
      hcd hm F Y g W).trans hmass

/--
Run anisotropic conflict cleanup only on positive-mass target tubes.  This
removes geometrically irrelevant zero-mass indices before asking for a degree
bound, while preserving the full raw target shading mass.
-/
lemma weighted_positive_anisotropic_target_refinement
    (hselect : WeightedEssentiallyDistinctSelectionStatement)
    {delta rho c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d))
    (D : ℕ)
    (hdegree :
      let raw :=
        flattenThreeTubeImageCover F
          (anisotropicRescalingMap g c d m)
          (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
      let rawShading := sourceIndexedAnisotropicTargetShading F Y g W
      let positive :=
        selectedTubeFamily raw (positiveMassIndices rawShading)
      ∀ i,
        (Finset.univ.filter fun j =>
          j ≠ i ∧
            ¬(positive.tube i).EssentiallyDistinct
              (positive.tube j)).card ≤ D) :
    let raw :=
      flattenThreeTubeImageCover F
        (anisotropicRescalingMap g c d m)
        (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
    let rawShading := sourceIndexedAnisotropicTargetShading F Y g W
    let positiveIndices := positiveMassIndices rawShading
    let positive := selectedTubeFamily raw positiveIndices
    let positiveShading := selectedTubeShading rawShading positiveIndices
    ∃ selected : Finset (Fin positive.card),
      let coarse := selectedTubeFamily positive selected
      let Z := selectedTubeShading positiveShading selected
      coarse.IsEssentiallyDistinct ∧
        Z.union ⊆ rawShading.union ∧
        ENNReal.ofReal m * shadedMassInSlab Y c d ≤
          (D + 1 : ENNReal) * Z.mass := by
  let raw :=
    flattenThreeTubeImageCover F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
  let rawShading := sourceIndexedAnisotropicTargetShading F Y g W
  let positiveIndices := positiveMassIndices rawShading
  let positive := selectedTubeFamily raw positiveIndices
  let positiveShading := selectedTubeShading rawShading positiveIndices
  rcases weighted_essentially_distinct_shading_refinement
      hselect positive positiveShading D hdegree with
    ⟨selected, hdistinct, hunionPositive, hmass⟩
  have hunionRaw : positiveShading.union ⊆ rawShading.union :=
    selectedTubeShading_union_subset rawShading positiveIndices
  have hrawMass : rawShading.mass = positiveShading.mass := by
    symm
    exact selectedTubeShading_positiveMass_mass rawShading
  refine ⟨selected, hdistinct, hunionPositive.trans hunionRaw, ?_⟩
  calc
    ENNReal.ofReal m * shadedMassInSlab Y c d
        ≤ rawShading.mass :=
      sourceIndexedAnisotropicTargetShading_mass_lower
        hcd hm F Y g W
    _ = positiveShading.mass := hrawMass
    _ ≤ (D + 1 : ENNReal) *
        (selectedTubeShading positiveShading selected).mass := hmass

end Kakeya.Assouad
