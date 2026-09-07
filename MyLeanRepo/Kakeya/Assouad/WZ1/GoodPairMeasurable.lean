import MyLeanRepo.Kakeya.Assouad.WZ1.MeasurableFiniteChoice
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Measurability of WZ1 good-pair data
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- The number of narrow active third directions is measurable in the point. -/
lemma measurable_wz1GoodThirdCount
    {delta tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (i j : Fin F.card) :
    Measurable fun p : Point3 =>
      wz1GoodThirdCount Y p i j tau := by
  classical
  let Q : Point3 → Fin F.card → Prop := fun p k =>
    p ∈ Y.carrier k ∧
      |wz1TripleProduct
        (F.tube i).direction
        (F.tube j).direction
        (F.tube k).direction| < tau
  have hQ : ∀ k : Fin F.card, MeasurableSet {p : Point3 | Q p k} := by
    intro k
    by_cases hthresh :
        |wz1TripleProduct
          (F.tube i).direction
          (F.tube j).direction
          (F.tube k).direction| < tau
    · have h_set : {p : Point3 | Q p k} = Y.carrier k := by
        ext p
        simp [Q, hthresh]
      rw [h_set]
      exact Y.measurable_carrier k
    · have h_set : {p : Point3 | Q p k} = (∅ : Set Point3) := by
        ext p
        simp [Q, hthresh]
      rw [h_set]
      exact MeasurableSet.empty
  have h_sum : Measurable fun p : Point3 =>
      ∑ k : Fin F.card, if Q p k then (1 : ℕ) else 0 := by
    apply Finset.measurable_sum Finset.univ
    intro k _
    exact Measurable.ite (hQ k) measurable_const measurable_const
  have h_eq :
      (fun p : Point3 => wz1GoodThirdCount Y p i j tau) =
        fun p : Point3 =>
          ∑ k : Fin F.card, if Q p k then (1 : ℕ) else 0 := by
    funext p
    have h : wz1GoodThirdCount Y p i j tau =
        (Finset.univ.filter (Q p)).card := by
      rfl
    rw [h, Finset.card_filter]
  exact h_eq ▸ h_sum

/-- The predicate used to select a transverse pair has measurable sections. -/
lemma wz1GoodPairPredicate_measurable
    {delta kappa tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (ij : Fin F.card × Fin F.card) :
    MeasurableSet {p : Point3 |
      p ∈ Y.carrier ij.1 ∧
      p ∈ Y.carrier ij.2 ∧
      kappa ≤ ‖wz1Cross
        (F.tube ij.1).direction
        (F.tube ij.2).direction‖ ∧
      4 * wz1GoodThirdCount Y p ij.1 ij.2 tau ≥
        Y.pointMultiplicity p} := by
  let i := ij.1
  let j := ij.2
  let crossNorm : ℝ :=
    ‖wz1Cross (F.tube i).direction (F.tube j).direction‖
  have h1 : MeasurableSet (Y.carrier i) := Y.measurable_carrier i
  have h2 : MeasurableSet (Y.carrier j) := Y.measurable_carrier j
  have h3 : MeasurableSet {p : Point3 | kappa ≤ crossNorm} := by
    by_cases h : kappa ≤ crossNorm
    · have h_set : {p : Point3 | kappa ≤ crossNorm} = Set.univ := by
        ext p
        simp [h]
      rw [h_set]
      exact MeasurableSet.univ
    · have h_set : {p : Point3 | kappa ≤ crossNorm} = (∅ : Set Point3) := by
        ext p
        simp [h]
      rw [h_set]
      exact MeasurableSet.empty
  have h4Count : Measurable fun p : Point3 =>
      wz1GoodThirdCount Y p i j tau :=
    measurable_wz1GoodThirdCount i j
  have h4Mult : Measurable fun p : Point3 =>
      Y.pointMultiplicity p :=
    measurable_pointMultiplicity Y
  have h4 : MeasurableSet {p : Point3 |
      4 * wz1GoodThirdCount Y p i j tau ≥ Y.pointMultiplicity p} := by
    let f : Point3 → ℕ × ℕ := fun p =>
      (wz1GoodThirdCount Y p i j tau, Y.pointMultiplicity p)
    have hf : Measurable f := h4Count.prod h4Mult
    let S : Set (ℕ × ℕ) := {nm | 4 * nm.1 ≥ nm.2}
    have hS : MeasurableSet S :=
      DiscreteMeasurableSpace.forall_measurableSet S
    have h_eq :
        {p : Point3 |
          4 * wz1GoodThirdCount Y p i j tau ≥ Y.pointMultiplicity p} =
          f ⁻¹' S := by
      ext p
      simp [f, S]
    rw [h_eq]
    exact hf hS
  exact h1.inter (h2.inter (h3.inter h4))

/-- The normalized cross-product normal of a measurable finite selector is measurable. -/
lemma WZ1NarrowDirectionSelection.normal_measurable
    {delta kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (selection : WZ1NarrowDirectionSelection Y kappa) :
    Measurable selection.normal := by
  classical
  let pair : Point3 → Fin F.card × Fin F.card :=
    fun p => (selection.first p, selection.second p)
  have hpair : Measurable pair :=
    selection.first_measurable.prod selection.second_measurable
  let crossOfPair : Fin F.card × Fin F.card → Point3 :=
    fun ij =>
      wz1Cross
        (F.tube ij.1).direction
        (F.tube ij.2).direction
  have hCrossOfPair : Measurable crossOfPair :=
    measurable_of_finite crossOfPair
  have hcross : Measurable fun p : Point3 =>
      wz1Cross
        (F.tube (selection.first p)).direction
        (F.tube (selection.second p)).direction := by
    exact hCrossOfPair.comp hpair
  have hnorm : Measurable fun p : Point3 =>
      ‖wz1Cross
        (F.tube (selection.first p)).direction
        (F.tube (selection.second p)).direction‖ :=
    hcross.norm
  have hinv : Measurable fun p : Point3 =>
      (‖wz1Cross
        (F.tube (selection.first p)).direction
        (F.tube (selection.second p)).direction‖)⁻¹ :=
    hnorm.inv
  unfold WZ1NarrowDirectionSelection.normal
  exact hinv.smul hcross

end Kakeya.Assouad
