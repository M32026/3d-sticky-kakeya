import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionFrostmanHelpers

/-!
# Helper lemmas for the final cluster Frostman assembly

Provides Frostman constant bounds, regularization loss properties,
and a general restricted-shading construction.
-/

noncomputable section

namespace Kakeya.Assouad

/-- `1 ≤ tubeParameterClusterFrostmanConstant C regularizationLoss lambda`. -/
lemma clusterFrostmanConstant_one
    (C regularizationLoss lambda : ENNReal)
    (hC : 1 ≤ C) (hRL : 1 ≤ regularizationLoss) (hlambda : lambda ≤ 1) :
    1 ≤ tubeParameterClusterFrostmanConstant C regularizationLoss lambda := by
  dsimp only [tubeParameterClusterFrostmanConstant]
  have hinv : 1 ≤ lambda⁻¹ := ENNReal.one_le_inv.mpr hlambda
  calc
    1 ≤ C := hC
    _ ≤ C * regularizationLoss := le_mul_of_one_le_right (by positivity) hRL
    _ ≤ (100000 : ENNReal) * (C * regularizationLoss) :=
      le_mul_of_one_le_left (by positivity) (by norm_num)
    _ = 100000 * C * regularizationLoss := by ring
    _ ≤ 100000 * C * regularizationLoss * lambda⁻¹ :=
      le_mul_of_one_le_right (by positivity) hinv

/-- `tubeParameterClusterFrostmanConstant C regularizationLoss lambda ≠ ⊤`. -/
lemma clusterFrostmanConstant_ne_top
    (C regularizationLoss lambda : ENNReal)
    (hC : C ≠ ⊤) (hRL : regularizationLoss ≠ ⊤) (hlambda : lambda ≠ 0) :
    tubeParameterClusterFrostmanConstant C regularizationLoss lambda ≠ ⊤ := by
  dsimp only [tubeParameterClusterFrostmanConstant]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hC) hRL)
    (by simpa [ENNReal.inv_eq_top] using hlambda)

/--
Given `imbalance > 0`, `regularizationLoss = 4 * (Nat.log 2 (2 * imbalance) + 1)`
satisfies `1 ≤ regularizationLoss`.
-/
lemma regularizationLoss_one (imbalance : ℕ) (_hpos : 0 < imbalance) :
    1 ≤ (4 * (Nat.log 2 (2 * imbalance) + 1 : ENNReal)) := by
  have h1 : 1 ≤ (Nat.log 2 (2 * imbalance) + 1 : ENNReal) := by
    exact_mod_cast Nat.le_add_left 1 (Nat.log 2 (2 * imbalance))
  calc
    1 ≤ (Nat.log 2 (2 * imbalance) + 1 : ENNReal) := h1
    _ ≤ 4 * (Nat.log 2 (2 * imbalance) + 1 : ENNReal) :=
      le_mul_of_one_le_left (by positivity) (by norm_num)

/--
`regularizationLoss` is finite.
-/
lemma regularizationLoss_ne_top (imbalance : ℕ) :
    (4 * (Nat.log 2 (2 * imbalance) + 1 : ENNReal)) ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · simp
  · simp

/--
General restricted shading: keep only tubes whose assigned center is in `selected`.
-/
def restrictShadingToCenters
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading F)
    (assign : Fin F.card → Point 3)
    (selected : DiscreteSet 3) :
    Kakeya.Streamlined.TubeShading F where
  carrier i :=
    if assign i ∈ selected then shading.carrier i else ∅
  measurable_carrier i := by
    by_cases hi : assign i ∈ selected
    · simp [hi, shading.measurable_carrier]
    · simp [hi]
  subset_body i := by
    by_cases hi : assign i ∈ selected
    · simpa [hi] using shading.subset_body i
    · simp [hi]

/-- The restricted shading is a subshading. -/
lemma restrictShadingToCenters_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading F)
    (assign : Fin F.card → Point 3)
    (selected : DiscreteSet 3) :
    IsSubshading (restrictShadingToCenters shading assign selected) shading := by
  intro i
  by_cases hi : assign i ∈ selected
  · simp [restrictShadingToCenters, hi]
  · simp [restrictShadingToCenters, hi]

/--
Mass of the restricted shading equals the sum of assigned cluster masses
over the selected centers.
-/
lemma restrictShadingToCenters_mass
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading F)
    (assign : Fin F.card → Point 3)
    (selected : DiscreteSet 3) :
    (restrictShadingToCenters shading assign selected).mass =
      ∑ p ∈ selected, tubeParameterAssignedClusterMass shading assign p := by
  classical
  simp only [Kakeya.Streamlined.Shading.mass,
    restrictShadingToCenters, tubeParameterAssignedClusterMass]
  have h0 : ∀ (i : Fin F.card),
      MeasureTheory.volume (if assign i ∈ selected then shading.carrier i else ∅) =
        (if assign i ∈ selected then MeasureTheory.volume (shading.carrier i) else 0) := by
    intro i
    split_ifs <;> simp [*]
  have h_main : ∀ (i : Fin F.card),
      (if assign i ∈ selected then MeasureTheory.volume (shading.carrier i) else 0) =
        ∑ p ∈ selected,
          (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) := by
    intro i
    by_cases hi : assign i ∈ selected
    · let f : Point 3 → ENNReal := fun p =>
          if assign i = p then MeasureTheory.volume (shading.carrier i) else 0
      have h_sum : ∑ p ∈ selected, f p = f (assign i) :=
        Finset.sum_eq_single_of_mem (assign i) hi
          (fun p _ hne => by
            have h' : assign i ≠ p := hne.symm
            simp [f, h'])
      have h_fa : f (assign i) = MeasureTheory.volume (shading.carrier i) := by
        simp [f]
      have h_final : ∑ p ∈ selected,
          (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
          MeasureTheory.volume (shading.carrier i) := by
        exact h_sum.trans h_fa
      rw [h_final, if_pos hi]
    · have h_not : ∀ p ∈ selected, assign i ≠ p := by
        intro p hp h_eq
        rw [h_eq] at hi
        exact hi hp
      have h_sum : ∑ p ∈ selected,
          (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        exact if_neg (h_not p hp)
      rw [h_sum, if_neg hi]
  have h1 : ∑ i : Fin F.card,
        (if assign i ∈ selected then MeasureTheory.volume (shading.carrier i) else 0) =
      ∑ i : Fin F.card, ∑ p ∈ selected,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h_main i
  have h2 : ∑ i : Fin F.card, ∑ p ∈ selected,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
      ∑ p ∈ selected, ∑ i : Fin F.card,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) := by
    rw [Finset.sum_comm]
  have h_a : ∑ (x : Fin F.card),
        MeasureTheory.volume (if assign x ∈ selected then shading.carrier x else ∅) =
      ∑ (x : Fin F.card),
        (if assign x ∈ selected then MeasureTheory.volume (shading.carrier x) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    exact h0 x
  have h_b := h1.trans h2
  exact h_a.trans h_b

end Kakeya.Assouad
