import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.FullFiberProfiles
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.DividingScales.DeltaMaxFiniteUnion
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalRelationDeltaMaxSplitProduct.Helpers
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.SubfamilyFrostmanProduct
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax

/-!
# Common all-scale selection for the two independent full-fiber profiles

For a nonempty equal-radius full containment fiber inside its dilated parent,
the maximal density is exactly the product of its Frostman constant and its
reference density. At a fixed scale, all parent containers have the same
volume and all fine tubes have the same volume. Consequently branching and
`deltaMax` comparability determine Frostman comparability.

This module freezes the remaining common-selection problem for repaired
Definition 2.1(iv). The output selects one fine set at all distinguished
scales, retains shading mass, and regularizes the final full-containment
branching and `deltaMax` profiles. No assigned-parent fiber, cross-scale
transition map, or pre-selection witness-retention assumption appears.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- Fine indices selected inside one complete geometric containment fiber. -/
def selectedFullContainmentIndices
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    Finset (Fin F.card) :=
  selected ∩ U.containedFineIndices r j

/-- The exact selected part of one complete geometric containment fiber. -/
def selectedFullContainmentSubfamily
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    TubeSubfamily F :=
  TubeSubfamily.fromFinset F
    (selectedFullContainmentIndices U selected r j)

/--
Parents used by the original independent cover on the selected fine set.

This definition chooses only the parent roster. All profiles below are still
computed on the complete geometric fibers
`selected ∩ containedFineIndices`, never on assigned-parent fibers.
-/
def activeSelectedParents
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta) :
    Finset (Fin (U.coarse r).card) :=
  selected.image (U.cover r).parent

/-- Selected indices assigned by the auxiliary cover to one coarse parent. -/
def selectedAssignedFineIndices
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    Finset (Fin F.card) :=
  selected.filter fun i => (U.cover r).parent i = j

/-- The selected assigned-parent fiber, used only for disjoint bookkeeping. -/
def selectedAssignedFineSubfamily
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    TubeSubfamily F :=
  TubeSubfamily.fromFinset F
    (selectedAssignedFineIndices U selected r j)

/-- A parent is active exactly when its selected assigned fiber is nonempty. -/
lemma mem_activeSelectedParents_iff_selectedAssigned_nonempty
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    j ∈ activeSelectedParents U selected r ↔
      (selectedAssignedFineIndices U selected r j).Nonempty := by
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, hparent⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    exact hparent
  · rintro ⟨i, hi⟩
    have hselected : i ∈ selected :=
      (Finset.mem_filter.mp hi).1
    have hparent : (U.cover r).parent i = j :=
      (Finset.mem_filter.mp hi).2
    exact Finset.mem_image.mpr ⟨i, hselected, hparent⟩

/-- Every selected assigned fiber lies in the selected full geometric fiber. -/
lemma selectedAssignedFineIndices_subset_selectedFullContainmentIndices
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    selectedAssignedFineIndices U selected r j ⊆
      selectedFullContainmentIndices U selected r j := by
  intro i hi
  have hselected : i ∈ selected :=
    (Finset.mem_filter.mp hi).1
  have hparent : (U.cover r).parent i = j :=
    (Finset.mem_filter.mp hi).2
  have hfull : i ∈ U.containedFineIndices r j := by
    rw [U.mem_containedFineIndices_iff r j i]
    simpa [hparent] using (U.cover r).nested i
  exact Finset.mem_inter.mpr ⟨hselected, hfull⟩

/--
Every selected full child of `j` belongs to the selected assigned fiber of a
same-scale parent in the fixed geometric neighborhood of `j`.
-/
lemma selectedFullContainmentIndices_subset_biUnion_selectedAssigned
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    selectedFullContainmentIndices U selected r j ⊆
      (U.containedParentIndices r r j).biUnion
        (selectedAssignedFineIndices U selected r) := by
  intro i hi
  have hselected : i ∈ selected :=
    (Finset.mem_inter.mp hi).1
  have hfull : i ∈ U.containedFineIndices r j :=
    (Finset.mem_inter.mp hi).2
  let p := (U.cover r).parent i
  have hp : p ∈ U.containedParentIndices r r j := by
    rw [U.mem_containedParentIndices_iff r r j p]
    have hi_contains :
        (F.tube i).carrier ⊆
          dilatedTubeCarrier A ((U.coarse r).tube j) :=
      (U.mem_containedFineIndices_iff r j i).mp hfull
    exact
      DilatedDiscreteUniformTubeStructure.common_child_parent_containment
        hA
        (lt_of_lt_of_le hdelta
          (uniformScale delta hdelta_le_one r).property.1)
        (uniformScale delta hdelta_le_one r).property.2
        le_rfl (F.tube i) (hF_ball i)
        ((U.coarse r).tube p) ((U.coarse r).tube j)
        ((U.cover r).nested i) hi_contains
  refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
  exact Finset.mem_filter.mpr ⟨hselected, rfl⟩

/--
The cardinality of a selected full geometric fiber is bounded by the sum of
the selected assigned-fiber cardinalities in its same-scale parent
neighborhood.
-/
lemma selectedFullContainmentCard_le_sum_selectedAssigned
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    ((selectedFullContainmentIndices U selected r j).card : ENNReal) ≤
      ∑ p ∈ U.containedParentIndices r r j,
        ((selectedAssignedFineIndices U selected r p).card : ENNReal) := by
  have hsubset :=
    selectedFullContainmentIndices_subset_biUnion_selectedAssigned
      hA hdelta hF_ball U selected r j
  have hcard :
      (selectedFullContainmentIndices U selected r j).card ≤
        ((U.containedParentIndices r r j).biUnion
          (selectedAssignedFineIndices U selected r)).card :=
    Finset.card_le_card hsubset
  have hunion :
      ((U.containedParentIndices r r j).biUnion
          (selectedAssignedFineIndices U selected r)).card ≤
        ∑ p ∈ U.containedParentIndices r r j,
          (selectedAssignedFineIndices U selected r p).card :=
    Finset.card_biUnion_le
  exact_mod_cast hcard.trans hunion

/-- Selected assigned-fiber `deltaMax` is bounded by the selected full fiber. -/
lemma selectedAssignedFineDeltaMax_le_selectedFullContainmentDeltaMax
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (selectedAssignedFineSubfamily U selected r j).family.toBodyFamily.deltaMax ≤
      (selectedFullContainmentSubfamily U selected r j).family.toBodyFamily.deltaMax :=
  ConditionalRelationDeltaMaxSplitProduct.fromFinset_deltaMax_mono
    (selectedAssignedFineIndices_subset_selectedFullContainmentIndices
      U selected r j)

/--
The selected full-fiber `deltaMax` is at most the sum of the selected assigned
fiber `deltaMax` values over the fixed same-scale parent neighborhood.
-/
lemma selectedFullContainmentDeltaMax_le_sum_selectedAssigned
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (selectedFullContainmentSubfamily U selected r j).family.toBodyFamily.deltaMax ≤
      ∑ p ∈ U.containedParentIndices r r j,
        (selectedAssignedFineSubfamily U selected r p).family.toBodyFamily.deltaMax :=
  deltaMax_finset_union_bound
    (U.containedParentIndices r r j)
    (selectedFullContainmentIndices U selected r j)
    (selectedAssignedFineIndices U selected r)
    (selectedFullContainmentIndices_subset_biUnion_selectedAssigned
      hA hdelta hF_ball U selected r j)

/--
Comparable selected assigned fibers imply comparable selected full geometric
fibers, with one fixed same-scale parent-neighborhood loss.

The assigned fibers are used only as a disjoint partition. The conclusion is
stated for the paper-semantic full containment fibers.
-/
lemma selectedFullProfilesComparable_of_selectedAssigned
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (selected : Finset (Fin F.card))
    (D C : ENNReal)
    (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hneighborhood :
      ∀ r : UniformScaleIndex delta,
      ∀ j : Fin (U.coarse r).card,
        ((U.containedParentIndices r r j).card : ENNReal) ≤ D)
    (hassignedCard :
      ∀ r : UniformScaleIndex delta,
      ∀ j ∈ activeSelectedParents U selected r,
      ∀ k ∈ activeSelectedParents U selected r,
        ComparableBy C
          ((selectedAssignedFineIndices U selected r j).card : ENNReal)
          ((selectedAssignedFineIndices U selected r k).card : ENNReal))
    (hassignedDeltaMax :
      ∀ r : UniformScaleIndex delta,
      ∀ j ∈ activeSelectedParents U selected r,
      ∀ k ∈ activeSelectedParents U selected r,
        ComparableBy C
          (selectedAssignedFineSubfamily U selected r j).family.toBodyFamily.deltaMax
          (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax) :
    (∀ r : UniformScaleIndex delta,
      ∀ j ∈ activeSelectedParents U selected r,
      ∀ k ∈ activeSelectedParents U selected r,
        ComparableBy (D * C)
          (selectedFullContainmentSubfamily U selected r j).family.enncard
          (selectedFullContainmentSubfamily U selected r k).family.enncard) ∧
    ∀ r : UniformScaleIndex delta,
      ∀ j ∈ activeSelectedParents U selected r,
      ∀ k ∈ activeSelectedParents U selected r,
        ComparableBy (D * C)
          (selectedFullContainmentSubfamily U selected r j).family.toBodyFamily.deltaMax
          (selectedFullContainmentSubfamily U selected r k).family.toBodyFamily.deltaMax := by
  have hfactor : 1 ≤ D * C := one_le_mul hD hC
  have hassignedCard_le :
      ∀ r : UniformScaleIndex delta,
      ∀ p : Fin (U.coarse r).card,
      ∀ k ∈ activeSelectedParents U selected r,
        ((selectedAssignedFineIndices U selected r p).card : ENNReal) ≤
          C * ((selectedAssignedFineIndices U selected r k).card : ENNReal) := by
    intro r p k hk
    by_cases hp : p ∈ activeSelectedParents U selected r
    · exact (hassignedCard r p hp k hk).2.1
    · have hp_empty :
          selectedAssignedFineIndices U selected r p = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hnonempty
        exact hp
          ((mem_activeSelectedParents_iff_selectedAssigned_nonempty
            U selected r p).mpr hnonempty)
      rw [hp_empty]
      simp
  have hassignedDelta_le :
      ∀ r : UniformScaleIndex delta,
      ∀ p : Fin (U.coarse r).card,
      ∀ k ∈ activeSelectedParents U selected r,
        (selectedAssignedFineSubfamily U selected r p).family.toBodyFamily.deltaMax ≤
          C * (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax := by
    intro r p k hk
    by_cases hp : p ∈ activeSelectedParents U selected r
    · exact (hassignedDeltaMax r p hp k hk).2.1
    · have hp_empty :
          selectedAssignedFineIndices U selected r p = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hnonempty
        exact hp
          ((mem_activeSelectedParents_iff_selectedAssigned_nonempty
            U selected r p).mpr hnonempty)
      have hempty_subset :
          selectedAssignedFineIndices U selected r p ⊆
            selectedAssignedFineIndices U selected r k := by
        rw [hp_empty]
        exact Finset.empty_subset _
      have hmono :
          (selectedAssignedFineSubfamily U selected r p).family.toBodyFamily.deltaMax ≤
            (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax :=
        ConditionalRelationDeltaMaxSplitProduct.fromFinset_deltaMax_mono
          hempty_subset
      exact hmono.trans
        (le_mul_of_one_le_left' hC)
  have hcard_direction :
      ∀ r : UniformScaleIndex delta,
      ∀ j ∈ activeSelectedParents U selected r,
      ∀ k ∈ activeSelectedParents U selected r,
        (selectedFullContainmentSubfamily U selected r j).family.enncard ≤
          D * C *
            (selectedFullContainmentSubfamily U selected r k).family.enncard := by
    intro r j hj k hk
    have hfull_sum :=
      selectedFullContainmentCard_le_sum_selectedAssigned
        hA hdelta hF_ball U selected r j
    have hsum :
        (∑ p ∈ U.containedParentIndices r r j,
            ((selectedAssignedFineIndices U selected r p).card : ENNReal)) ≤
          (U.containedParentIndices r r j).card *
            (C * ((selectedAssignedFineIndices U selected r k).card : ENNReal)) := by
      calc
        (∑ p ∈ U.containedParentIndices r r j,
            ((selectedAssignedFineIndices U selected r p).card : ENNReal))
            ≤ ∑ _p ∈ U.containedParentIndices r r j,
                C * ((selectedAssignedFineIndices U selected r k).card : ENNReal) := by
              exact Finset.sum_le_sum fun p _ =>
                hassignedCard_le r p k hk
        _ = (U.containedParentIndices r r j).card *
              (C * ((selectedAssignedFineIndices U selected r k).card : ENNReal)) := by
              simp [nsmul_eq_mul]
    have hassigned_full :
        ((selectedAssignedFineIndices U selected r k).card : ENNReal) ≤
          ((selectedFullContainmentIndices U selected r k).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card
        (selectedAssignedFineIndices_subset_selectedFullContainmentIndices
          U selected r k)
    have hfull_card :
        (selectedFullContainmentSubfamily U selected r j).family.enncard =
          ((selectedFullContainmentIndices U selected r j).card : ENNReal) := by
      rfl
    have hfull_card_k :
        (selectedFullContainmentSubfamily U selected r k).family.enncard =
          ((selectedFullContainmentIndices U selected r k).card : ENNReal) := by
      rfl
    rw [hfull_card, hfull_card_k]
    calc
      ((selectedFullContainmentIndices U selected r j).card : ENNReal)
          ≤ ∑ p ∈ U.containedParentIndices r r j,
              ((selectedAssignedFineIndices U selected r p).card : ENNReal) :=
        hfull_sum
      _ ≤ (U.containedParentIndices r r j).card *
            (C * ((selectedAssignedFineIndices U selected r k).card : ENNReal)) :=
        hsum
      _ ≤ D * (C *
            ((selectedAssignedFineIndices U selected r k).card : ENNReal)) := by
        gcongr
        exact hneighborhood r j
      _ ≤ D * (C *
            ((selectedFullContainmentIndices U selected r k).card : ENNReal)) := by
        gcongr
      _ = D * C *
            ((selectedFullContainmentIndices U selected r k).card : ENNReal) := by
        ring
  have hdelta_direction :
      ∀ r : UniformScaleIndex delta,
      ∀ j ∈ activeSelectedParents U selected r,
      ∀ k ∈ activeSelectedParents U selected r,
        (selectedFullContainmentSubfamily U selected r j).family.toBodyFamily.deltaMax ≤
          D * C *
            (selectedFullContainmentSubfamily U selected r k).family.toBodyFamily.deltaMax := by
    intro r j hj k hk
    have hfull_sum :=
      selectedFullContainmentDeltaMax_le_sum_selectedAssigned
        hA hdelta hF_ball U selected r j
    have hsum :
        (∑ p ∈ U.containedParentIndices r r j,
            (selectedAssignedFineSubfamily U selected r p).family.toBodyFamily.deltaMax) ≤
          (U.containedParentIndices r r j).card *
            (C * (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax) := by
      calc
        (∑ p ∈ U.containedParentIndices r r j,
            (selectedAssignedFineSubfamily U selected r p).family.toBodyFamily.deltaMax)
            ≤ ∑ _p ∈ U.containedParentIndices r r j,
                C * (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax := by
              exact Finset.sum_le_sum fun p _ =>
                hassignedDelta_le r p k hk
        _ = (U.containedParentIndices r r j).card *
              (C * (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax) := by
              simp [nsmul_eq_mul]
    have hassigned_full :=
      selectedAssignedFineDeltaMax_le_selectedFullContainmentDeltaMax
        U selected r k
    calc
      (selectedFullContainmentSubfamily U selected r j).family.toBodyFamily.deltaMax
          ≤ ∑ p ∈ U.containedParentIndices r r j,
              (selectedAssignedFineSubfamily U selected r p).family.toBodyFamily.deltaMax :=
        hfull_sum
      _ ≤ (U.containedParentIndices r r j).card *
            (C * (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax) :=
        hsum
      _ ≤ D * (C *
            (selectedAssignedFineSubfamily U selected r k).family.toBodyFamily.deltaMax) := by
        gcongr
        exact hneighborhood r j
      _ ≤ D * (C *
            (selectedFullContainmentSubfamily U selected r k).family.toBodyFamily.deltaMax) := by
        gcongr
      _ = D * C *
            (selectedFullContainmentSubfamily U selected r k).family.toBodyFamily.deltaMax := by
        ring
  constructor
  · intro r j hj k hk
    exact ⟨hfactor,
      hcard_direction r j hj k hk,
      hcard_direction r k hk j hj⟩
  · intro r j hj k hk
    exact ⟨hfactor,
      hdelta_direction r j hj k hk,
      hdelta_direction r k hk j hj⟩

/--
For a family contained in a positive finite convex reference set, `deltaMax`
is exactly its Frostman constant times its reference density.
-/
lemma BodyFamily.deltaMax_eq_frostmanConstantIn_mul_density_of_contained
    (G : BodyFamily) (U : Set Point3)
    (hU_convex : Convex ℝ U)
    (hall : ∀ i, (G.body i).carrier ⊆ U)
    (hmass_pos : 0 < G.containedMass U)
    (hmass_top : G.containedMass U ≠ ⊤)
    (hvol_pos : 0 < volume U)
    (hvol_top : volume U ≠ ⊤) :
    G.deltaMax =
      G.frostmanConstantIn U * G.density U := by
  have hdensity_zero : G.density U ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hmass_pos.ne', hvol_top⟩
  have hdensity_top : G.density U ≠ ⊤ :=
    ENNReal.div_ne_top hmass_top hvol_pos.ne'
  apply le_antisymm
  · exact G.deltaMax_le_frostmanConstantIn_mul_density
      hU_convex hall hdensity_zero hdensity_top
  · have hfrostman :
        G.frostmanConstantIn U ≤
          G.deltaMax * volume U / G.containedMass U :=
      BodyFamily.frostman_from_deltaMax
        hmass_pos hmass_top hvol_pos hvol_top le_rfl le_rfl
    calc
      G.frostmanConstantIn U * G.density U
          ≤ (G.deltaMax * volume U / G.containedMass U) *
              G.density U := by
                gcongr
      _ = (G.deltaMax * volume U / G.containedMass U) *
              (G.containedMass U / volume U) := by
            rfl
      _ = G.deltaMax *
              ((volume U * (G.containedMass U)⁻¹) *
                (G.containedMass U * (volume U)⁻¹)) := by
            simp only [div_eq_mul_inv]
            ring
      _ = G.deltaMax *
              ((volume U * (volume U)⁻¹) *
                ((G.containedMass U)⁻¹ * G.containedMass U)) := by
            congr 1
            ac_rfl
      _ = G.deltaMax := by
            rw [ENNReal.mul_inv_cancel hvol_pos.ne' hvol_top,
              ENNReal.inv_mul_cancel hmass_pos.ne' hmass_top]
            simp

/-- The preceding identity specialized to one complete full-containment fiber. -/
lemma fineFiber_deltaMax_eq_frostman_mul_referenceDensity
    {delta A : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (hdelta : 0 < delta) (hA : 1 ≤ A)
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    U.fineFiberDeltaMax r j =
      U.fineFiberFrostmanConstant r j *
        (U.containedFineSubfamily r j).family.toBodyFamily.density
          (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  let G := (U.containedFineSubfamily r j).family.toBodyFamily
  let container :=
    dilatedTubeCarrier A ((U.coarse r).tube j)
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hall : ∀ i, (G.body i).carrier ⊆ container := by
    intro i
    have hi_image :
        (U.containedFineSubfamily r j).embedding i ∈
          Finset.image (U.containedFineSubfamily r j).embedding
            Finset.univ :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h_image :
        Finset.image (U.containedFineSubfamily r j).embedding
            Finset.univ =
          U.containedFineIndices r j :=
      Finset.image_orderEmbOfFin_univ _ rfl
    rw [h_image] at hi_image
    change
      ((U.containedFineSubfamily r j).family.tube i).carrier ⊆
        container
    rw [(U.containedFineSubfamily r j).tube_eq i]
    exact (U.mem_containedFineIndices_iff r j _).mp hi_image
  exact
    BodyFamily.deltaMax_eq_frostmanConstantIn_mul_density_of_contained
      G container
      (GeometricLemmas.dilatedTubeCarrier_convex _) hall
      (U.containedFineReferenceMass_pos hdelta r j)
      (U.containedFineReferenceMass_ne_top r j)
      (GeometricLemmas.dilatedTubeCarrier_volume_pos hrho hA _)
      (GeometricLemmas.dilatedTubeCarrier_volume_ne_top hrho hA _)

/--
For equal-radius tube families in equal-volume containers, cardinality
comparability is exactly the corresponding reference-density comparability.
-/
lemma TubeFamily.referenceDensityComparable_of_enncard
    {delta : ℝ} (G H : TubeFamily delta)
    {U V : Set Point3}
    (hG : ∀ i, (G.tube i).carrier ⊆ U)
    (hH : ∀ i, (H.tube i).carrier ⊆ V)
    (hvol : volume U = volume V)
    {K : ENNReal}
    (hcard : ComparableBy K G.enncard H.enncard) :
    ComparableBy K
      (G.toBodyFamily.density U)
      (H.toBodyFamily.density V) := by
  have hmassG :
      G.toBodyFamily.containedMass U =
        G.enncard * Kakeya.deltaTubeVolume delta := by
    rw [BodyFamily.containedMass_eq_mass_of_all_contained
      G.toBodyFamily U hG]
    exact G.bodyMass_eq_nominalMass
  have hmassH :
      H.toBodyFamily.containedMass V =
        H.enncard * Kakeya.deltaTubeVolume delta := by
    rw [BodyFamily.containedMass_eq_mass_of_all_contained
      H.toBodyFamily V hH]
    exact H.bodyMass_eq_nominalMass
  refine ⟨hcard.1, ?_, ?_⟩
  · dsimp only [BodyFamily.density]
    rw [hmassG, hmassH, hvol]
    calc
      G.enncard * Kakeya.deltaTubeVolume delta / volume V
          ≤ (K * H.enncard) * Kakeya.deltaTubeVolume delta /
              volume V := by
            gcongr
            exact hcard.2.1
      _ = K *
          (H.enncard * Kakeya.deltaTubeVolume delta / volume V) := by
            simp only [div_eq_mul_inv]
            ring
  · dsimp only [BodyFamily.density]
    rw [hmassG, hmassH, hvol]
    calc
      H.enncard * Kakeya.deltaTubeVolume delta / volume V
          ≤ (K * G.enncard) * Kakeya.deltaTubeVolume delta /
              volume V := by
            gcongr
            exact hcard.2.2
      _ = K *
          (G.enncard * Kakeya.deltaTubeVolume delta / volume V) := by
            simp only [div_eq_mul_inv]
            ring

/--
If maximal densities and positive finite reference densities are each
`K`-comparable, the corresponding Frostman constants are `K^2`-comparable.

Together with `fineFiber_deltaMax_eq_frostman_mul_referenceDensity`, this is
the deterministic consumer that reconstructs Definition 2.1(iv)'s Frostman
comparison from the two profiles returned by the selector below.
-/
lemma frostmanComparable_of_deltaMax_density
    {K Fx Fy Dx Dy rx ry : ENNReal}
    (hK : 1 ≤ K)
    (hrx_zero : rx ≠ 0) (hrx_top : rx ≠ ⊤)
    (hry_zero : ry ≠ 0) (hry_top : ry ≠ ⊤)
    (hx : Dx = Fx * rx) (hy : Dy = Fy * ry)
    (hD : ComparableBy K Dx Dy)
    (hr : ComparableBy K rx ry) :
    ComparableBy (K ^ 2) Fx Fy := by
  refine ⟨one_le_pow₀ hK, ?_, ?_⟩
  · apply (ENNReal.mul_le_mul_iff_right hrx_zero hrx_top).mp
    calc
      rx * Fx = Dx := by rw [mul_comm, hx]
      _ ≤ K * Dy := hD.2.1
      _ = K * (Fy * ry) := by rw [hy]
      _ ≤ K * (Fy * (K * rx)) := by
        gcongr
        exact hr.2.2
      _ = rx * (K ^ 2 * Fy) := by ring
  · apply (ENNReal.mul_le_mul_iff_right hry_zero hry_top).mp
    calc
      ry * Fy = Dy := by rw [mul_comm, hy]
      _ ≤ K * Dx := hD.2.2
      _ = K * (Fx * rx) := by rw [hx]
      _ ≤ K * (Fx * (K * ry)) := by
        gcongr
        exact hr.2.1
      _ = ry * (K ^ 2 * Fx) := by ring

/--
One common selected fine set regularizes the two independent final full-fiber
profiles at every paper scale.

The active parent family is defined from the final full geometric containment
fibers. The same natural loss controls shading retention, branching
comparability, and `deltaMax` comparability, and is subpolynomial in `delta`.
The closed identity above then recovers the Frostman comparison required by
Definition 2.1(iv).
-/
def FactorLocalTwoProfileCommonSelectionStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ hdelta_le_one : delta ≤ 1,
          ∀ U : DilatedDiscreteUniformTubeStructure
              (A := 1000) F hdelta_le_one,
          ∀ Y : TubeShading F, 0 < Y.mass →
            ∃ (selected : Finset (Fin F.card)) (loss : ℕ),
              selected.Nonempty ∧
              1 ≤ loss ∧
              (loss : ENNReal) ≤
                Kakeya.realRpowENN delta (-epsilon) ∧
              Y.mass ≤
                (loss : ENNReal) *
                  ((TubeSubfamily.fromFinset F selected)
                    |>.restrictShading Y).mass ∧
              (∀ r : UniformScaleIndex delta,
                (activeSelectedParents U selected r).Nonempty) ∧
              (∀ r : UniformScaleIndex delta,
                ∀ j ∈ activeSelectedParents U selected r,
                ∀ k ∈ activeSelectedParents U selected r,
                  ComparableBy (loss : ENNReal)
                    ((selectedFullContainmentSubfamily U selected r j)
                      |>.family.enncard)
                    ((selectedFullContainmentSubfamily U selected r k)
                      |>.family.enncard)) ∧
              ∀ r : UniformScaleIndex delta,
                ∀ j ∈ activeSelectedParents U selected r,
                ∀ k ∈ activeSelectedParents U selected r,
                  ComparableBy (loss : ENNReal)
                    ((selectedFullContainmentSubfamily U selected r j)
                      |>.family.toBodyFamily.deltaMax)
                    ((selectedFullContainmentSubfamily U selected r k)
                      |>.family.toBodyFamily.deltaMax)

/--
The production selector package, additionally exposing the assigned-fiber
branching comparison used to build the final surjective local covers.

Assigned fibers remain an internal bookkeeping interface.  The two public
paper-semantic conclusions are still stated for full geometric containment
fibers.
-/
def FactorLocalTwoProfileCommonSelectionWithAssignedStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ hdelta_le_one : delta ≤ 1,
          ∀ U : DilatedDiscreteUniformTubeStructure
              (A := 1000) F hdelta_le_one,
          ∀ Y : TubeShading F, 0 < Y.mass →
            ∃ (selected : Finset (Fin F.card)) (loss : ℕ),
              selected.Nonempty ∧
              1 ≤ loss ∧
              (loss : ENNReal) ≤
                Kakeya.realRpowENN delta (-epsilon) ∧
              Y.mass ≤
                (loss : ENNReal) *
                  ((TubeSubfamily.fromFinset F selected)
                    |>.restrictShading Y).mass ∧
              (∀ r : UniformScaleIndex delta,
                (activeSelectedParents U selected r).Nonempty) ∧
              (∀ r : UniformScaleIndex delta,
                ∀ j ∈ activeSelectedParents U selected r,
                ∀ k ∈ activeSelectedParents U selected r,
                  ComparableBy (loss : ENNReal)
                    ((selectedAssignedFineIndices U selected r j).card :
                      ENNReal)
                    ((selectedAssignedFineIndices U selected r k).card :
                      ENNReal)) ∧
              (∀ r : UniformScaleIndex delta,
                ∀ j ∈ activeSelectedParents U selected r,
                ∀ k ∈ activeSelectedParents U selected r,
                  ComparableBy (loss : ENNReal)
                    ((selectedFullContainmentSubfamily U selected r j)
                      |>.family.enncard)
                    ((selectedFullContainmentSubfamily U selected r k)
                      |>.family.enncard)) ∧
              ∀ r : UniformScaleIndex delta,
                ∀ j ∈ activeSelectedParents U selected r,
                ∀ k ∈ activeSelectedParents U selected r,
                  ComparableBy (loss : ENNReal)
                    ((selectedFullContainmentSubfamily U selected r j)
                      |>.family.toBodyFamily.deltaMax)
                    ((selectedFullContainmentSubfamily U selected r k)
                      |>.family.toBodyFamily.deltaMax)

end Kakeya.Streamlined
