import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Distinct common-bin incidence counting

The common-bin argument counts each bin label once, after choosing one
witnessing height.  This finite lemma records the resulting bounded-degree
incidence estimate.
-/

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace CommonBinDistinctIncidence

variable {Bin Cell : Type*}

/-- Double-count incidences between a finite set of bin labels and their
selected spatial cells. -/
theorem sum_cell_card_eq_sum_bin_degree
    (bins : Finset Bin)
    (cells : Bin → Finset Cell) :
    ∑ bin ∈ bins, (cells bin).card =
      ∑ cell ∈ bins.biUnion cells,
        (bins.filter fun bin => cell ∈ cells bin).card := by
  calc
    ∑ bin ∈ bins, (cells bin).card =
        ∑ bin ∈ bins, ∑ cell ∈ bins.biUnion cells,
          if cell ∈ cells bin then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro bin hbin
      rw [Finset.card_eq_sum_ones]
      calc
        ∑ _cell ∈ cells bin, 1 =
            ∑ cell ∈ cells bin,
              if cell ∈ cells bin then 1 else 0 := by simp
        _ = ∑ cell ∈ bins.biUnion cells,
              if cell ∈ cells bin then 1 else 0 := by
          apply Finset.sum_subset
          · intro cell hcell
            exact Finset.mem_biUnion.mpr ⟨bin, hbin, hcell⟩
          · intro cell _hcellUnion hcell
            simp [hcell]
    _ =
        ∑ cell ∈ bins.biUnion cells, ∑ bin ∈ bins,
          if cell ∈ cells bin then 1 else 0 := by
      rw [Finset.sum_comm]
    _ =
        ∑ cell ∈ bins.biUnion cells,
          (bins.filter fun bin => cell ∈ cells bin).card := by
      apply Finset.sum_congr rfl
      intro cell _hcell
      simp

/-- If every selected bin contains at least `K` spatial cells and every cell
is selected by at most `D` distinct bins, then the total incidence count is
bounded by `D` times the number of participating cells. -/
theorem card_mul_le_degree_mul_card
    (bins : Finset Bin)
    (cells : Bin → Finset Cell)
    (K D : ℕ)
    (bin_lower : ∀ bin ∈ bins, K ≤ (cells bin).card)
    (cell_degree :
      ∀ cell ∈ bins.biUnion cells,
        (bins.filter fun bin => cell ∈ cells bin).card ≤ D) :
    bins.card * K ≤ D * (bins.biUnion cells).card := by
  calc
    bins.card * K = ∑ _bin ∈ bins, K := by
      simp [Finset.sum_const, Nat.mul_comm]
    _ ≤ ∑ bin ∈ bins, (cells bin).card :=
      Finset.sum_le_sum fun bin hbin => bin_lower bin hbin
    _ =
        ∑ cell ∈ bins.biUnion cells,
          (bins.filter fun bin => cell ∈ cells bin).card :=
      sum_cell_card_eq_sum_bin_degree bins cells
    _ ≤ ∑ _cell ∈ bins.biUnion cells, D :=
      Finset.sum_le_sum fun cell hcell => cell_degree cell hcell
    _ = D * (bins.biUnion cells).card := by
      simp [Finset.sum_const, Nat.mul_comm]

/-- Weighted form used in the slab-local common-bin argument.  Here `cellMass`
is the uniform balanced mass of one participating spatial cell and
`totalMass` is the mass available in the slab. -/
theorem card_mul_cellMass_le_degree_mul_totalMass
    (bins : Finset Bin)
    (cells : Bin → Finset Cell)
    (K D : ℕ)
    (cellMass totalMass : ENNReal)
    (bin_lower : ∀ bin ∈ bins, K ≤ (cells bin).card)
    (cell_degree :
      ∀ cell ∈ bins.biUnion cells,
        (bins.filter fun bin => cell ∈ cells bin).card ≤ D)
    (participating_mass :
      ((bins.biUnion cells).card : ENNReal) * cellMass ≤ totalMass) :
    (bins.card : ENNReal) * K * cellMass ≤ D * totalMass := by
  have incidenceNat :=
    card_mul_le_degree_mul_card bins cells K D bin_lower cell_degree
  have incidence :
      (bins.card : ENNReal) * K ≤
        D * ((bins.biUnion cells).card : ENNReal) := by
    exact_mod_cast incidenceNat
  calc
    (bins.card : ENNReal) * K * cellMass ≤
        (D * ((bins.biUnion cells).card : ENNReal)) * cellMass := by
      gcongr
    _ = D * (((bins.biUnion cells).card : ENNReal) * cellMass) := by ring
    _ ≤ D * totalMass := by gcongr

/-- Select one bin whose weight controls the sum over all distinct labels. -/
theorem exists_weight_ge_average
    (bins : Finset Bin)
    (bins_nonempty : bins.Nonempty)
    (weight : {bin // bin ∈ bins} → ENNReal) :
    ∃ selected : {bin // bin ∈ bins},
      (∑ bin, weight bin) ≤ (bins.card : ENNReal) * weight selected := by
  let first : {bin // bin ∈ bins} :=
    ⟨Classical.choose bins_nonempty, Classical.choose_spec bins_nonempty⟩
  rcases Finset.exists_max_image
      (Finset.univ : Finset {bin // bin ∈ bins}) weight
      ⟨first, Finset.mem_univ first⟩
    with
    ⟨selected, _, maximal⟩
  refine ⟨selected, ?_⟩
  simpa [nsmul_eq_mul] using
    (Finset.sum_le_card_nsmul
      (Finset.univ : Finset {bin // bin ∈ bins}) weight
      (weight selected) fun bin hbin => maximal bin hbin)

/-- Fixed-bin averaging after the distinct-bin incidence estimate and the
exact source/coarse cross identity. -/
theorem exists_fixed_bin_mass_lower
    (bins : Finset Bin)
    (bins_nonempty : bins.Nonempty)
    (cells : Bin → Finset Cell)
    (K D : ℕ)
    (cellMass sourceMass coarseMass theta : ENNReal)
    (weight : {bin // bin ∈ bins} → ENNReal)
    (bin_lower : ∀ bin ∈ bins, K ≤ (cells bin).card)
    (cell_degree :
      ∀ cell ∈ bins.biUnion cells,
        (bins.filter fun bin => cell ∈ cells bin).card ≤ D)
    (participating_mass :
      ((bins.biUnion cells).card : ENNReal) * cellMass ≤ coarseMass)
    (rich_mass : sourceMass ≤ 4 * ∑ bin, weight bin)
    (cross : sourceMass = theta * coarseMass)
    (coarseMass_pos : 0 < coarseMass)
    (coarseMass_ne_top : coarseMass ≠ ⊤) :
    ∃ selected : {bin // bin ∈ bins},
      theta * K * cellMass ≤ 4 * D * weight selected := by
  rcases exists_weight_ge_average bins bins_nonempty weight with
    ⟨selected, average⟩
  refine ⟨selected, ?_⟩
  have incidence :=
    card_mul_cellMass_le_degree_mul_totalMass
      bins cells K D cellMass coarseMass bin_lower cell_degree
      participating_mass
  apply
    (ENNReal.mul_le_mul_iff_right coarseMass_pos.ne'
      coarseMass_ne_top).mp
  calc
    coarseMass * (theta * K * cellMass) =
        (theta * coarseMass) * (K * cellMass) := by ring
    _ = sourceMass * (K * cellMass) := by rw [cross]
    _ ≤ (4 * ∑ bin, weight bin) * (K * cellMass) := by gcongr
    _ ≤ (4 * ((bins.card : ENNReal) * weight selected)) *
          (K * cellMass) := by gcongr
    _ = 4 * weight selected *
          ((bins.card : ENNReal) * K * cellMass) := by ring
    _ ≤ 4 * weight selected * (D * coarseMass) := by gcongr
    _ = coarseMass * (4 * D * weight selected) := by ring

/-- Cancel the common per-cell source density after passing from fixed-bin
source mass to a union of complete spatial cells. -/
theorem whole_cell_volume_lower
    (K D cellCount : ℕ)
    (cellMass fixedBinMass cellSourceMass cubeVolume theta : ENNReal)
    (fixed_bin_lower :
      theta * K * cellMass ≤ 4 * D * fixedBinMass)
    (fixed_bin_cell_upper :
      fixedBinMass ≤ cellSourceMass * cellCount)
    (cell_cross : cellSourceMass = theta * cubeVolume)
    (theta_pos : 0 < theta)
    (theta_ne_top : theta ≠ ⊤) :
    K * cellMass ≤
      4 * D * ((cellCount : ENNReal) * cubeVolume) := by
  apply (ENNReal.mul_le_mul_iff_right theta_pos.ne' theta_ne_top).mp
  calc
    theta * (K * cellMass) = theta * K * cellMass := by ring
    _ ≤ 4 * D * fixedBinMass := fixed_bin_lower
    _ ≤ 4 * D * (cellSourceMass * cellCount) := by gcongr
    _ = 4 * D * ((theta * cubeVolume) * cellCount) := by rw [cell_cross]
    _ = theta *
        (4 * D * ((cellCount : ENNReal) * cubeVolume)) := by ring

/-- Division-free endpoint of the common-bin argument.  It cancels first the
standard-slab coarse mass and then the per-rho-cell source mass. -/
theorem whole_cell_volume_lower_of_exact_cross
    (labelCount K D rhoCellCount : ℕ)
    (sourceMass fixedBinMass coarseMass sqrtCellMass
      rhoCellMass rhoCubeVolume : ENNReal)
    (rich_average :
      sourceMass ≤ 4 * labelCount * fixedBinMass)
    (distinct_incidence :
      labelCount * K * sqrtCellMass ≤ D * coarseMass)
    (source_coarse_cross :
      sourceMass * rhoCubeVolume = coarseMass * rhoCellMass)
    (fixed_bin_cell_upper :
      fixedBinMass ≤ rhoCellCount * rhoCellMass)
    (coarseMass_pos : 0 < coarseMass)
    (coarseMass_ne_top : coarseMass ≠ ⊤)
    (rhoCellMass_pos : 0 < rhoCellMass)
    (rhoCellMass_ne_top : rhoCellMass ≠ ⊤) :
    K * sqrtCellMass ≤
      4 * D * (rhoCellCount * rhoCubeVolume) := by
  have firstCancellation :
      rhoCellMass * (K * sqrtCellMass) ≤
        (4 * D * fixedBinMass) * rhoCubeVolume := by
    apply
      (ENNReal.mul_le_mul_iff_right
        coarseMass_pos.ne' coarseMass_ne_top).mp
    calc
      coarseMass * (rhoCellMass * (K * sqrtCellMass)) =
          (coarseMass * rhoCellMass) * (K * sqrtCellMass) := by ring
      _ = (sourceMass * rhoCubeVolume) *
          (K * sqrtCellMass) := by rw [source_coarse_cross]
      _ ≤ (4 * labelCount * fixedBinMass * rhoCubeVolume) *
          (K * sqrtCellMass) := by gcongr
      _ = (4 * fixedBinMass * rhoCubeVolume) *
          (labelCount * K * sqrtCellMass) := by ring
      _ ≤ (4 * fixedBinMass * rhoCubeVolume) *
          (D * coarseMass) := by gcongr
      _ = coarseMass *
          ((4 * D * fixedBinMass) * rhoCubeVolume) := by ring
  apply
    (ENNReal.mul_le_mul_iff_right
      rhoCellMass_pos.ne' rhoCellMass_ne_top).mp
  calc
    rhoCellMass * (K * sqrtCellMass) ≤
        (4 * D * fixedBinMass) * rhoCubeVolume :=
      firstCancellation
    _ ≤ (4 * D * (rhoCellCount * rhoCellMass)) *
          rhoCubeVolume := by gcongr
    _ = rhoCellMass *
        (4 * D * (rhoCellCount * rhoCubeVolume)) := by ring

end CommonBinDistinctIncidence

end Kakeya.Assouad
