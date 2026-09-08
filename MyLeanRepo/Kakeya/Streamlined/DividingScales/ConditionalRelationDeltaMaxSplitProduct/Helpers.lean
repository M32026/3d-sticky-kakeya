import MyLeanRepo.Kakeya.Streamlined.DividingScales.WeightedFiniteUnion
import MyLeanRepo.Kakeya.Streamlined.DividingScales.DiscreteKatzTaoProof.RelationIndicesDecomposition
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverGeometry

/-!
# Helpers for conditional relation deltaMax products

This module contains the finite-union and geometric containment steps that
are independent of the remaining multiscale neighborhood cancellation.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace ConditionalRelationDeltaMaxSplitProduct

/--
A uniform contained-mass estimate on every finite-volume convex test set
implies the corresponding `deltaMax` bound.
-/
lemma deltaMax_le_of_containedMass_le
    {G : BodyFamily} {bound : ENNReal}
    (h : ∀ K : Set Point3, Convex ℝ K → volume K ≠ ⊤ →
      G.containedMass K ≤ bound * volume K) :
    G.deltaMax ≤ bound := by
  classical
  dsimp only [BodyFamily.deltaMax]
  apply csSup_le
    (by
      exact ⟨0, Set.univ, convex_univ, by simp [BodyFamily.density]⟩)
  intro d hd
  rcases hd with ⟨K, hK, rfl⟩
  by_cases htop : volume K = ⊤
  · simp [BodyFamily.density, htop]
  · by_cases hzero : volume K = 0
    · have hmass : G.containedMass K = 0 := by
        dsimp only [BodyFamily.containedMass]
        apply Finset.sum_eq_zero
        intro i hi
        have hsub : (G.body i).carrier ⊆ K :=
          (Finset.mem_filter.mp hi).2
        have hvol : (G.body i).volume ≤ volume K := volume.mono hsub
        rw [hzero] at hvol
        simpa using hvol
      simp [BodyFamily.density, hmass, hzero]
    · exact (ENNReal.div_le_iff hzero htop).mpr (h K hK htop)

/-- `deltaMax` is monotone when the selected index finset grows. -/
lemma fromFinset_deltaMax_mono
    {δ : ℝ} {G : TubeFamily δ}
    {I₁ I₂ : Finset (Fin G.card)} (hsubset : I₁ ⊆ I₂) :
    (TubeSubfamily.fromFinset G I₁).family.toBodyFamily.deltaMax ≤
      (TubeSubfamily.fromFinset G I₂).family.toBodyFamily.deltaMax := by
  classical
  let S₁ := TubeSubfamily.fromFinset G I₁
  let S₂ := TubeSubfamily.fromFinset G I₂
  have hmass : ∀ K : Set Point3,
      finsetContainedMass I₁ K ≤ finsetContainedMass I₂ K := by
    intro K
    dsimp only [finsetContainedMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.filter_subset_filter
      exact hsubset
    · intro _ _ _
      positivity
  have hmain : ∀ K : Set Point3, Convex ℝ K →
      S₁.family.toBodyFamily.density K ≤
        S₂.family.toBodyFamily.deltaMax := by
    intro K hK
    have hcontained :
        S₁.family.toBodyFamily.containedMass K ≤
          S₂.family.toBodyFamily.containedMass K := by
      rw [subfamily_containedMass_eq I₁ K,
        subfamily_containedMass_eq I₂ K]
      exact hmass K
    by_cases htop : volume K = ⊤
    · simp [BodyFamily.density, htop]
    · by_cases hzero : volume K = 0
      · have hmass_zero :
            S₁.family.toBodyFamily.containedMass K = 0 := by
          dsimp only [BodyFamily.containedMass]
          apply Finset.sum_eq_zero
          intro i hi
          have hsub :
              (S₁.family.toBodyFamily.body i).carrier ⊆ K :=
            (Finset.mem_filter.mp hi).2
          have hvol :
              (S₁.family.toBodyFamily.body i).volume ≤ volume K :=
            volume.mono hsub
          rw [hzero] at hvol
          simpa using hvol
        simp [BodyFamily.density, hmass_zero, hzero]
      · have hdensity :
            S₁.family.toBodyFamily.density K ≤
              S₂.family.toBodyFamily.density K := by
          dsimp only [BodyFamily.density]
          exact ENNReal.div_le_div hcontained le_rfl
        have hmem :
            S₂.family.toBodyFamily.density K ∈
              {d : ENNReal |
                ∃ K' : Set Point3, Convex ℝ K' ∧
                  d = S₂.family.toBodyFamily.density K'} :=
          ⟨K, hK, rfl⟩
        have hbdd :
            BddAbove
              {d : ENNReal |
                ∃ K' : Set Point3, Convex ℝ K' ∧
                  d = S₂.family.toBodyFamily.density K'} :=
          ⟨⊤, fun _ _ => le_top⟩
        exact hdensity.trans (le_csSup hbdd hmem)
  dsimp only [BodyFamily.deltaMax]
  apply csSup_le
    (by
      exact ⟨0, Set.univ, convex_univ, by simp [BodyFamily.density]⟩)
  intro d hd
  rcases hd with ⟨K, hK, rfl⟩
  exact hmain K hK

/--
Every fine-scale parent in a split piece is contained in the universal
dilation of the selected middle parent.
-/
lemma splitPiece_tubes_contained_in_dilatedMiddle
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one}
    (P : FrostmanConditionalFactorScope U)
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card)
    (k : Fin (U.coarse middle).card) :
    ∀ j ∈ P.splitPiece i middle P.coarse k,
      ((U.coarse P.fine).tube j).carrier ⊆
        dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse middle).tube k) := by
  intro j hj
  simp only [FrostmanConditionalFactorScope.splitPiece,
    Finset.mem_image] at hj
  rcases hj with ⟨original, hfilter, rfl⟩
  have hmiddle : (U.cover middle).parent original = k :=
    (Finset.mem_filter.mp hfilter).2
  let fineTube := F.tube original
  let fineParent :=
    (U.coarse P.fine).tube ((U.cover P.fine).parent original)
  let middleParent := (U.coarse middle).tube k
  have hfine :
      fineTube.carrier ⊆ dilatedTubeCarrier A fineParent :=
    (U.cover P.fine).nested original
  have hmiddleContain :
      fineTube.carrier ⊆ dilatedTubeCarrier A middleParent := by
    have h := (U.cover middle).nested original
    rw [hmiddle] at h
    exact h
  have hfine_pos :
      0 < (uniformScale delta hdelta_le_one P.fine).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one P.fine).property.1
  have hmiddle_one :
      (uniformScale delta hdelta_le_one middle).1 ≤ 1 :=
    (uniformScale delta hdelta_le_one middle).property.2
  exact
    DilatedDiscreteUniformTubeStructure.common_child_parent_containment
      hA hfine_pos hmiddle_one hfine_middle fineTube
      (hF_ball original) fineParent middleParent hfine hmiddleContain

end ConditionalRelationDeltaMaxSplitProduct

end Kakeya.Streamlined
