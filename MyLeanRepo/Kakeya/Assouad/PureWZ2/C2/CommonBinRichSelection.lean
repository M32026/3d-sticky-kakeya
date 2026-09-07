import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinDistinctIncidence

/-!
# Rich common-bin finite selection

This module contains the finite mass bookkeeping between the analytic
occupied-bin and spatial-cell estimates.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace CommonBinRichSelection

variable {Bin Cell : Type*}

def richBins
    (bins : Finset Bin)
    (weight : Bin → ENNReal)
    (threshold : ENNReal) : Finset Bin :=
  bins.filter fun bin => threshold ≤ weight bin

def poorBins
    (bins : Finset Bin)
    (weight : Bin → ENNReal)
    (threshold : ENNReal) : Finset Bin :=
  bins.filter fun bin => weight bin < threshold

theorem rich_union_poor
    (bins : Finset Bin)
    (weight : Bin → ENNReal)
    (threshold : ENNReal) :
    richBins bins weight threshold ∪ poorBins bins weight threshold = bins := by
  ext bin
  simp only [richBins, poorBins, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hbin, _⟩ | ⟨hbin, _⟩) <;> exact hbin
  · intro hbin
    by_cases hrich : threshold ≤ weight bin
    · exact Or.inl ⟨hbin, hrich⟩
    · exact Or.inr ⟨hbin, lt_of_not_ge hrich⟩

theorem rich_disjoint_poor
    (bins : Finset Bin)
    (weight : Bin → ENNReal)
    (threshold : ENNReal) :
    Disjoint (richBins bins weight threshold)
      (poorBins bins weight threshold) := by
  rw [Finset.disjoint_left]
  intro bin hrich hpoor
  exact
    (not_lt_of_ge (Finset.mem_filter.mp hrich).2)
      (Finset.mem_filter.mp hpoor).2

theorem poor_sum_le_card_mul
    (bins : Finset Bin)
    (weight : Bin → ENNReal)
    (threshold : ENNReal) :
    (∑ bin ∈ poorBins bins weight threshold, weight bin) ≤
      (bins.card : ENNReal) * threshold := by
  calc
    (∑ bin ∈ poorBins bins weight threshold, weight bin) ≤
        ∑ _bin ∈ poorBins bins weight threshold, threshold := by
      apply Finset.sum_le_sum
      intro bin hbin
      exact (Finset.mem_filter.mp hbin).2.le
    _ = ((poorBins bins weight threshold).card : ENNReal) *
          threshold := by simp
    _ ≤ (bins.card : ENNReal) * threshold := by
      gcongr
      exact
        (show poorBins bins weight threshold ⊆ bins from
          Finset.filter_subset _ _)

/-- If twice the worst possible poor-bin mass is at most the total mass, the
rich bins retain at least half of the total mass. -/
theorem total_le_two_mul_rich_sum
    (bins : Finset Bin)
    (weight : Bin → ENNReal)
    (threshold total : ENNReal)
    (total_eq : total = ∑ bin ∈ bins, weight bin)
    (total_ne_top : total ≠ ⊤)
    (poor_budget :
      2 * ((bins.card : ENNReal) * threshold) ≤ total) :
    total ≤
      2 * ∑ bin ∈ richBins bins weight threshold, weight bin := by
  let richMass :=
    ∑ bin ∈ richBins bins weight threshold, weight bin
  let poorMass :=
    ∑ bin ∈ poorBins bins weight threshold, weight bin
  have hpartition : total = richMass + poorMass := by
    rw [total_eq, ← rich_union_poor bins weight threshold,
      Finset.sum_union (rich_disjoint_poor bins weight threshold)]
  have poorFinite : poorMass ≠ ⊤ := by
    apply ne_top_of_le_ne_top total_ne_top
    rw [hpartition]
    exact le_add_self
  have poorBound :
      poorMass ≤ (bins.card : ENNReal) * threshold :=
    poor_sum_le_card_mul bins weight threshold
  have twoPoor : poorMass + poorMass ≤ richMass + poorMass := by
    calc
      poorMass + poorMass = 2 * poorMass := by ring
      _ ≤ 2 * ((bins.card : ENNReal) * threshold) := by gcongr
      _ ≤ total := poor_budget
      _ = richMass + poorMass := hpartition
  have poor_le_rich : poorMass ≤ richMass :=
    (ENNReal.add_le_add_iff_right poorFinite).mp twoPoor
  calc
    total = richMass + poorMass := hpartition
    _ ≤ richMass + richMass := by gcongr
    _ = 2 * richMass := by ring

/-- A rich bin whose mass is assembled from cells of mass at most `cellCap`
contains at least `K` distinct cells. -/
theorem cell_card_lower_of_rich
    (cells : Finset Cell)
    (cellWeight : Cell → ENNReal)
    (binMass threshold cellCap : ENNReal)
    (K : ℕ)
    (rich : threshold ≤ binMass)
    (mass_decomposition :
      binMass ≤ ∑ cell ∈ cells, cellWeight cell)
    (cell_upper : ∀ cell ∈ cells, cellWeight cell ≤ cellCap)
    (K_budget : (K : ENNReal) * cellCap ≤ threshold)
    (cellCap_pos : 0 < cellCap)
    (cellCap_ne_top : cellCap ≠ ⊤) :
    K ≤ cells.card := by
  have weighted :
      (K : ENNReal) * cellCap ≤ (cells.card : ENNReal) * cellCap := by
    calc
      (K : ENNReal) * cellCap ≤ threshold := K_budget
      _ ≤ binMass := rich
      _ ≤ ∑ cell ∈ cells, cellWeight cell := mass_decomposition
      _ ≤ ∑ _cell ∈ cells, cellCap :=
        Finset.sum_le_sum fun cell hcell => cell_upper cell hcell
      _ = (cells.card : ENNReal) * cellCap := by simp
  have castBound : (K : ENNReal) ≤ cells.card :=
    (ENNReal.mul_le_mul_iff_right cellCap_pos.ne' cellCap_ne_top).mp
      (by simpa [mul_comm] using weighted)
  exact_mod_cast castBound

end CommonBinRichSelection

end Kakeya.Assouad
