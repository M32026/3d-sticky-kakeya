import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Measurability of selected-third carriers
-/

namespace Kakeya.Assouad

open MeasureTheory

/--
The triple-product threshold set determined by two finite-valued measurable
index selections is measurable.
-/
lemma measurable_selected_carrier
    {delta tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {first second : Point3 → Fin F.card}
    (hfirst_meas : Measurable first)
    (hsecond_meas : Measurable second)
    (k : Fin F.card) :
    MeasurableSet {p : Point3 |
      |wz1TripleProduct
        (F.tube (first p)).direction
        (F.tube (second p)).direction
        (F.tube k).direction| < tau} := by
  classical
  let S : Set (Fin F.card × Fin F.card) := Set.univ
  have h_main :
      {p : Point3 |
        |wz1TripleProduct
          (F.tube (first p)).direction
          (F.tube (second p)).direction
          (F.tube k).direction| < tau} =
        ⋃ ij ∈ S,
          {p : Point3 | first p = ij.1 ∧ second p = ij.2} ∩
            {p : Point3 |
              |wz1TripleProduct
                (F.tube ij.1).direction
                (F.tube ij.2).direction
                (F.tube k).direction| < tau} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨(first p, second p), by simp [S], ?_⟩
      exact ⟨by simp, h⟩
    · rintro ⟨ij, _, ⟨h1, h2⟩, h⟩
      rw [h1, h2] at *
      exact h
  rw [h_main]
  exact MeasurableSet.biUnion (Set.to_countable S) (fun ij _ =>
    have h1 : MeasurableSet {p : Point3 | first p = ij.1} :=
      hfirst_meas (MeasurableSet.singleton ij.1)
    have h2 : MeasurableSet {p : Point3 | second p = ij.2} :=
      hsecond_meas (MeasurableSet.singleton ij.2)
    have h3 :
        MeasurableSet {p : Point3 |
          |wz1TripleProduct
            (F.tube ij.1).direction
            (F.tube ij.2).direction
            (F.tube k).direction| < tau} := by
      by_cases h :
          |wz1TripleProduct
            (F.tube ij.1).direction
            (F.tube ij.2).direction
            (F.tube k).direction| < tau
      · have h_set :
            {p : Point3 |
              |wz1TripleProduct
                (F.tube ij.1).direction
                (F.tube ij.2).direction
                (F.tube k).direction| < tau} = Set.univ := by
          ext p
          simp [h]
        rw [h_set]
        exact MeasurableSet.univ
      · have h_set :
            {p : Point3 |
              |wz1TripleProduct
                (F.tube ij.1).direction
                (F.tube ij.2).direction
                (F.tube k).direction| < tau} = ∅ := by
          ext p
          simp [h]
        rw [h_set]
        exact MeasurableSet.empty
    (h1.inter h2).inter h3)

end Kakeya.Assouad
