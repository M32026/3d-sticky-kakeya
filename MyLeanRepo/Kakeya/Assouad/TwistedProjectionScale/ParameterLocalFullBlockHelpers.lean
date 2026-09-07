import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockStatements

/-!
# Helper lemmas for constructing `ParameterLocalFullBlockData`

These lemmas discharge the straightforward fields of the local-block data
structure from the clustered data and global premises:

- mass of the restricted block shading as a sum over selected centers;
- lower bound on the block shading mass from two-sided cluster weights;
- nonemptiness and containment of the recentered point set;
- inheritance of the common `c`-window.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/-- The mass of the block shading equals the sum of assigned cluster masses. -/
lemma parameterLocalBlockShading_mass_eq
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered : TubeParameterClusterFrostmanData F Y C lambda delta)
    (sourcePoints : DiscreteSet 3) :
    (parameterLocalBlockShading clustered sourcePoints).mass =
      ∑ p ∈ sourcePoints,
        tubeParameterAssignedClusterMass
          clustered.shading clustered.assign p := by
  classical
  let selected := parameterLocalBlockIndices clustered sourcePoints
  have h1 : (parameterLocalBlockShading clustered sourcePoints).mass =
        ∑ i ∈ selected, MeasureTheory.volume (clustered.shading.carrier i) :=
    selectedTubeShading_mass clustered.shading selected
  rw [h1]
  have h_filter : ∑ i ∈ selected, MeasureTheory.volume (clustered.shading.carrier i) =
        ∑ i : Fin F.card,
          if clustered.assign i ∈ sourcePoints
          then MeasureTheory.volume (clustered.shading.carrier i)
          else 0 := by
    rw [Finset.sum_ite]
    simp [selected, parameterLocalBlockIndices]
  have h_comm : ∑ p ∈ sourcePoints,
          tubeParameterAssignedClusterMass clustered.shading clustered.assign p =
        ∑ i : Fin F.card,
          if clustered.assign i ∈ sourcePoints
          then MeasureTheory.volume (clustered.shading.carrier i)
          else 0 := by
    simp only [tubeParameterAssignedClusterMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have h_inner : ∑ p ∈ sourcePoints,
          (if clustered.assign i = p
           then MeasureTheory.volume (clustered.shading.carrier i)
           else 0) =
        if clustered.assign i ∈ sourcePoints
        then MeasureTheory.volume (clustered.shading.carrier i)
        else 0 := by
      by_cases h : clustered.assign i ∈ sourcePoints
      · rw [if_pos h]
        let f : Point 3 → ENNReal := fun p =>
          if clustered.assign i = p
          then MeasureTheory.volume (clustered.shading.carrier i)
          else 0
        have hsum : ∑ p ∈ sourcePoints, f p = f (clustered.assign i) :=
          Finset.sum_eq_single_of_mem (clustered.assign i) h
            (fun b _ hne => by simp [f, hne.symm])
        simpa [f] using hsum
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro p hp
        have hne : clustered.assign i ≠ p := by
          intro h_eq
          exact h (h_eq ▸ hp)
        simp [hne]
    exact h_inner
  rw [h_filter, h_comm]

/--
Lower bound on the block shading mass: every selected point contributes at
least `clusterMass`, so the total is at least `#sourcePoints * clusterMass`.
-/
lemma parameterLocalBlockShading_mass_lower
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered : TubeParameterClusterFrostmanData F Y C lambda delta)
    (sourcePoints : DiscreteSet 3)
    (h_sourcePoints_subset : sourcePoints ⊆ clustered.points) :
    sourcePoints.enncard * clustered.clusterMass ≤
      (parameterLocalBlockShading clustered sourcePoints).mass := by
  have h_eq : (parameterLocalBlockShading clustered sourcePoints).mass =
        ∑ p ∈ sourcePoints,
          tubeParameterAssignedClusterMass clustered.shading clustered.assign p :=
    parameterLocalBlockShading_mass_eq clustered sourcePoints
  rw [h_eq]
  have h_sum : ∑ p ∈ sourcePoints, clustered.clusterMass ≤
        ∑ p ∈ sourcePoints,
          tubeParameterAssignedClusterMass clustered.shading clustered.assign p :=
    Finset.sum_le_sum fun p hp =>
      clustered.cluster_mass_lower p (h_sourcePoints_subset hp)
  have h_const : ∑ p ∈ sourcePoints, clustered.clusterMass =
        sourcePoints.enncard * clustered.clusterMass := by
    simp [DiscreteSet.enncard, Finset.sum_const, mul_comm]
  rw [h_const] at h_sum
  exact h_sum

/-- Recentering a nonempty set gives a nonempty set. -/
lemma centeredParameterSet_nonempty
    {points : DiscreteSet 3} {center : Point 3}
    (h : points.Nonempty) :
    (centeredParameterSet points center).Nonempty :=
  Finset.image_nonempty.mpr h

/-- Containment is preserved under recentering. -/
lemma centeredParameterSet_containment
    {points : DiscreteSet 3} {center : Point 3} {r : ℝ}
    (h : ∀ p ∈ points, dist p center ≤ r) :
    ∀ p ∈ centeredParameterSet points center, dist p 0 ≤ r := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  simpa [dist_eq_norm] using h q hq

/--
The local c-window inherits from the global c-window premise.
-/
lemma parameterLocalBlock_window
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered : TubeParameterClusterFrostmanData F Y C lambda delta)
    (sourcePoints : DiscreteSet 3)
    (c0 : ℝ)
    (hwindow : ∀ i, clustered.shading.carrier i ≠ ∅ →
      |(tubeParams i).c - c0| ≤ delta / 2) :
    ∀ i : Fin (parameterLocalBlockIndices clustered sourcePoints).card,
      (parameterLocalBlockShading clustered sourcePoints).carrier i ≠ ∅ →
      |(tubeParams
          ((parameterLocalBlockIndices clustered sourcePoints).equivFin.symm i).1).c -
        c0| ≤ delta / 2 := by
  intro i hi
  let j := (parameterLocalBlockIndices clustered sourcePoints).equivFin.symm i
  have hcarrier : (parameterLocalBlockShading clustered sourcePoints).carrier i =
        clustered.shading.carrier j.1 := by
    rfl
  have hnonempty : clustered.shading.carrier j.1 ≠ ∅ := by
    rw [←hcarrier]
    exact hi
  exact hwindow j.1 hnonempty

end Kakeya.Assouad
