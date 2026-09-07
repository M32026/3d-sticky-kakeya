import MyLeanRepo.Kakeya.Cinematic.Section5.GlobalizationInputs
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Graph neighborhoods restricted to a physical parameter interval

If a point lies in the centered sixteenth of an interval whose length is at
least four graph radii, every witness for ambient graph-neighborhood
membership still lies inside the interval. Hence ambient and restricted
multiplicities agree exactly at that point.
-/

noncomputable section

open Set Metric

namespace Kakeya.Cinematic

def restrictedFunctionGraph
    (f : C2Function) (I : ParameterInterval) : Set (ℝ × ℝ) :=
  {p | ∃ hp : p.1 ∈ unitInterval,
    (⟨p.1, hp⟩ : UnitPoint) ∈ I.carrier ∧
      p.2 = f ⟨p.1, hp⟩}

def restrictedGraphNeighborhood
    (f : C2Function) (I : ParameterInterval)
    (rho : ℝ) : Set (ℝ × ℝ) :=
  Metric.thickening rho (restrictedFunctionGraph f I)

def restrictedMultiplicity
    (F : FiniteFunctionFamily) (I : ParameterInterval)
    (rho : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ f ∈ F.toFinset,
    (restrictedGraphNeighborhood f I rho).indicator
      (fun _ => (1 : ℝ)) p

lemma restrictedFunctionGraph_subset
    (f : C2Function) (I : ParameterInterval) :
    restrictedFunctionGraph f I ⊆ functionGraph f := by
  rintro p ⟨hp, _hI, hval⟩
  exact ⟨hp, hval⟩

lemma restrictedGraphNeighborhood_subset
    (f : C2Function) (I : ParameterInterval) (rho : ℝ) :
    restrictedGraphNeighborhood f I rho ⊆
      graphNeighborhood f rho := by
  exact Metric.thickening_subset_of_subset rho
    (restrictedFunctionGraph_subset f I)

lemma graphNeighborhood_mem_restricted_of_centered
    {f : C2Function} {I : ParameterInterval}
    {rho : ℝ} {p : ℝ × ℝ}
    (hrho : 0 < rho) (hlen : 4 * rho ≤ I.length)
    (hp_center : p.1 ∈ I.realCenteredCarrier (1 / 16))
    (hp : p ∈ graphNeighborhood f rho) :
    p ∈ restrictedGraphNeighborhood f I rho := by
  rcases Metric.mem_thickening_iff.mp hp with ⟨q, hq, hpq⟩
  rcases hq with ⟨hq_unit, hq_value⟩
  have hpq_x : |p.1 - q.1| < rho := by
    have hdist : dist p.1 q.1 ≤ dist p q := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have : dist p.1 q.1 < rho := hdist.trans_lt hpq
    simpa [Real.dist_eq] using this
  have hp_center_abs :
      |p.1 - I.midpoint| ≤ I.length / 32 := by
    have h := hp_center.2
    change
      |p.1 - I.midpoint| ≤
        (1 / 16 : ℝ) * I.length / 2 at h
    convert h using 1
    ring
  have hq_center_abs :
      |q.1 - I.midpoint| ≤ I.length / 2 := by
    have htri :
        |q.1 - I.midpoint| ≤
          |q.1 - p.1| + |p.1 - I.midpoint| := by
      calc
        |q.1 - I.midpoint| =
            |(q.1 - p.1) + (p.1 - I.midpoint)| := by
          ring_nf
        _ ≤ |q.1 - p.1| + |p.1 - I.midpoint| :=
          abs_add_le _ _
    have hqp : |q.1 - p.1| < rho := by
      simpa [abs_sub_comm] using hpq_x
    have hrho_len : rho ≤ I.length / 4 := by
      linarith
    calc
      |q.1 - I.midpoint| ≤
          |q.1 - p.1| + |p.1 - I.midpoint| := htri
      _ ≤ rho + I.length / 32 := by linarith
      _ ≤ I.length / 4 + I.length / 32 := by linarith
      _ ≤ I.length / 2 := by
        linarith [I.length_nonneg]
  let qpoint : UnitPoint := ⟨q.1, hq_unit⟩
  have hq_carrier : qpoint ∈ I.carrier := by
    rw [← I.centeredCarrier_one]
    change |q.1 - I.midpoint| ≤ (1 : ℝ) * I.length / 2
    simpa using hq_center_abs
  apply Metric.mem_thickening_iff.mpr
  exact ⟨q, ⟨hq_unit, hq_carrier, hq_value⟩, hpq⟩

lemma graphNeighborhood_iff_restricted_of_centered
    {f : C2Function} {I : ParameterInterval}
    {rho : ℝ} {p : ℝ × ℝ}
    (hrho : 0 < rho) (hlen : 4 * rho ≤ I.length)
    (hp_center : p.1 ∈ I.realCenteredCarrier (1 / 16)) :
    p ∈ graphNeighborhood f rho ↔
      p ∈ restrictedGraphNeighborhood f I rho := by
  constructor
  · exact
      graphNeighborhood_mem_restricted_of_centered
        hrho hlen hp_center
  · intro hp
    exact restrictedGraphNeighborhood_subset f I rho hp

lemma multiplicity_eq_restricted_of_centered
    {F : FiniteFunctionFamily} {I : ParameterInterval}
    {rho : ℝ} {p : ℝ × ℝ}
    (hrho : 0 < rho) (hlen : 4 * rho ≤ I.length)
    (hp_center : p.1 ∈ I.realCenteredCarrier (1 / 16)) :
    multiplicity F rho p = restrictedMultiplicity F I rho p := by
  unfold multiplicity restrictedMultiplicity
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases h : p ∈ graphNeighborhood f rho
  · have hr : p ∈ restrictedGraphNeighborhood f I rho :=
      (graphNeighborhood_iff_restricted_of_centered
        hrho hlen hp_center).mp h
    simp [h, hr]
  · have hr : p ∉ restrictedGraphNeighborhood f I rho := by
      intro hr
      exact h
        ((graphNeighborhood_iff_restricted_of_centered
          hrho hlen hp_center).mpr hr)
    simp [h, hr]

end Kakeya.Cinematic
