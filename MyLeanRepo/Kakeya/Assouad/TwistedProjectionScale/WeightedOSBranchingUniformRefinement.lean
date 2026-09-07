import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WeightedOSBranchingUniformRefinementStatement

/-!
# Measure-weighted Orponen--Shmerkin branching refinement

Apply the exact finite branching refinement to the atom indices, then convert
cardinality retention to measure retention using the factor-two terminal atom
mass comparison.
-/

namespace Kakeya.Assouad

theorem weighted_os_branching_uniform_refinement :
    WeightedOSBranchingUniformRefinementStatement := by
  intro β _ μ α _ A hA atom h_meas h_disj h_nonzero h_finite h_mass_comp
    levels childBound hcb_pos P h_partition h_atomic h_child_parent
    h_children_bound
  rcases os_branching_uniform_refinement α A hA levels childBound hcb_pos P
      h_partition h_atomic h_child_parent h_children_bound with
    ⟨A', hA'_nonempty, hA'_sub, h_card_ret, branchExponent,
      h_branch_bound, h_branch_unif⟩
  let L : ℕ := (2 * (Nat.log 2 childBound + 1)) ^ levels

  have h_meas' : MeasurableSet (finiteAtomUnion A' atom) := by
    apply MeasurableSet.biUnion (Finset.countable_toSet A')
    intro a ha
    exact h_meas a (hA'_sub ha)

  have h_sub :
      finiteAtomUnion A' atom ⊆ finiteAtomUnion A atom := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨a, ha, hxa⟩
    exact Set.mem_iUnion₂.mpr ⟨a, hA'_sub ha, hxa⟩

  have h_disj' :
      ∀ a ∈ A', ∀ b ∈ A', a ≠ b →
        Disjoint (atom a) (atom b) := by
    intro a ha b hb hne
    exact h_disj a (hA'_sub ha) b (hA'_sub hb) hne

  have h_pd_A : (↑A : Set α).PairwiseDisjoint atom := by
    intro a ha b hb hne
    exact h_disj a ha b hb hne
  have h_pd_A' : (↑A' : Set α).PairwiseDisjoint atom := by
    intro a ha b hb hne
    exact h_disj' a ha b hb hne

  have h_measure_A :
      μ (finiteAtomUnion A atom) = ∑ a ∈ A, μ (atom a) := by
    simpa [finiteAtomUnion] using
      MeasureTheory.measure_biUnion_finset h_pd_A h_meas

  have h_meas_A' : ∀ a ∈ A', MeasurableSet (atom a) := by
    intro a ha
    exact h_meas a (hA'_sub ha)

  have h_measure_A' :
      μ (finiteAtomUnion A' atom) = ∑ a ∈ A', μ (atom a) := by
    simpa [finiteAtomUnion] using
      MeasureTheory.measure_biUnion_finset h_pd_A' h_meas_A'

  rcases Finset.exists_min_image A (fun a => μ (atom a)) hA with
    ⟨a_min, ha_min_mem, h_min⟩
  let m_min : ENNReal := μ (atom a_min)

  have h1 : ∀ a ∈ A, μ (atom a) ≤ 2 * m_min := by
    intro a ha
    exact h_mass_comp a ha a_min ha_min_mem

  have h_sum_A :
      ∑ a ∈ A, μ (atom a) ≤ 2 * (A.card : ENNReal) * m_min := by
    calc
      ∑ a ∈ A, μ (atom a) ≤ ∑ a ∈ A, 2 * m_min := by
        apply Finset.sum_le_sum
        intro i hi
        exact h1 i hi
      _ = 2 * (A.card : ENNReal) * m_min := by
        rw [Finset.sum_const]
        ring

  have h2 : ∀ a ∈ A', m_min ≤ μ (atom a) := by
    intro a ha
    exact h_min a (hA'_sub ha)

  have h_sum_A' :
      (A'.card : ENNReal) * m_min ≤ ∑ a ∈ A', μ (atom a) := by
    calc
      (A'.card : ENNReal) * m_min = ∑ a ∈ A', m_min := by
        simp [Finset.sum_const]
      _ ≤ ∑ a ∈ A', μ (atom a) := by
        apply Finset.sum_le_sum
        intro i hi
        exact h2 i hi

  have h_card_ret' :
      (A.card : ENNReal) ≤
        (L : ENNReal) * (A'.card : ENNReal) := by
    exact_mod_cast h_card_ret

  have h_sum_A'_meas :
      (A'.card : ENNReal) * m_min ≤
        μ (finiteAtomUnion A' atom) := by
    rw [h_measure_A']
    exact h_sum_A'

  have h_main :
      μ (finiteAtomUnion A atom) ≤
        (2 : ENNReal) * (L : ENNReal) *
          μ (finiteAtomUnion A' atom) := by
    calc
      μ (finiteAtomUnion A atom) =
          ∑ a ∈ A, μ (atom a) := h_measure_A
      _ ≤ 2 * (A.card : ENNReal) * m_min := h_sum_A
      _ ≤ 2 * ((L : ENNReal) * (A'.card : ENNReal)) * m_min := by
        gcongr
      _ = (2 : ENNReal) * (L : ENNReal) *
          ((A'.card : ENNReal) * m_min) := by
        ring
      _ ≤ (2 : ENNReal) * (L : ENNReal) *
          μ (finiteAtomUnion A' atom) := by
        gcongr

  exact
    ⟨A', hA'_nonempty, hA'_sub, h_meas', h_sub, h_main,
      branchExponent, h_branch_bound, h_branch_unif⟩

end Kakeya.Assouad
