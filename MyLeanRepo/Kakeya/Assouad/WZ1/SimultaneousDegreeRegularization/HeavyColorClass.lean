import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Heavy color class

One color class of a finite coloring carries at least the average total
nonnegative weight.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
One color class of a finite coloring carries at least the average total
`ENNReal` weight.
-/
lemma exists_heavy_color_class
    {α : Type*} [DecidableEq α]
    (indices : Finset α) (q : ℕ) (hq : 0 < q)
    (color : α → Fin q) (weight : α → ENNReal) :
    ∃ c : Fin q,
      (∑ i ∈ indices, weight i) ≤
        (q : ENNReal) *
          ∑ i ∈ indices.filter (fun i => color i = c), weight i := by
  classical
  let fiber (c : Fin q) : Finset α :=
    indices.filter fun i => color i = c
  let mass (c : Fin q) : ENNReal :=
    ∑ i ∈ fiber c, weight i

  have h_disjoint :
      ∀ c₁ ∈ (Finset.univ : Finset (Fin q)),
        ∀ c₂ ∈ (Finset.univ : Finset (Fin q)), c₁ ≠ c₂ →
          Disjoint (fiber c₁) (fiber c₂) := by
    intro c₁ _ c₂ _ hne
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have hc₁ : color i = c₁ := (Finset.mem_filter.mp hi₁).2
    have hc₂ : color i = c₂ := (Finset.mem_filter.mp hi₂).2
    exact hne (hc₁.symm.trans hc₂)

  have h_union :
      (Finset.univ : Finset (Fin q)).biUnion fiber = indices := by
    ext i
    simp [fiber]

  have h_partition :
      ∑ c : Fin q, mass c = ∑ i ∈ indices, weight i := by
    have h_sum :
        ∑ c ∈ (Finset.univ : Finset (Fin q)),
            ∑ i ∈ fiber c, weight i =
          ∑ i ∈ (Finset.univ : Finset (Fin q)).biUnion fiber, weight i :=
      (Finset.sum_biUnion h_disjoint).symm
    simpa [mass, h_union] using h_sum

  have hcolors : (Finset.univ : Finset (Fin q)).Nonempty := by
    exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  rcases Finset.exists_max_image
      (Finset.univ : Finset (Fin q)) mass hcolors with
    ⟨c, _, hmax⟩

  have h_sum_le : ∑ d : Fin q, mass d ≤ ∑ _d : Fin q, mass c := by
    apply Finset.sum_le_sum
    intro d _
    exact hmax d (Finset.mem_univ d)
  have h_count : ∑ _d : Fin q, mass c = (q : ENNReal) * mass c := by
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  refine ⟨c, ?_⟩
  change (∑ i ∈ indices, weight i) ≤ (q : ENNReal) * mass c
  rw [← h_partition, ← h_count]
  exact h_sum_le

end Kakeya.Assouad
