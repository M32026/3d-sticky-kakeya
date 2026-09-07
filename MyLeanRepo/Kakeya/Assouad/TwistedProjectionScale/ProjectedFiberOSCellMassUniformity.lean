import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellMassUniformityStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridPartitionTree

/-!
# Projected cell-mass uniformity after OS branching

Equal retained leaf counts and factor-two terminal atom masses give
factor-two projected mass comparison in every pair of occupied same-level
cells.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_os_cell_mass_uniformity :
    ProjectedFiberOSCellMassUniformityStatement := by
  intro h_branching delta F Y f threshold levelCount bandData
    base levels indexBound hbase atomized uniform

  let P : ℕ → Finset (DiscreteSet 2) :=
    fun k => planarGridPartition base k atomized.centers
  let μ := projectedFiberMeasure Y f
  let atom := projectedFiberGridAtom bandData.band base levels

  have hbase2 : 2 ≤ base := by linarith
  have hbase_pos : (0 : ℝ) < base := by positivity

  set fineScale : ℝ := (base ^ levels : ℝ)⁻¹ with hfineScale_def
  have hfine_pos : 0 < fineScale := by positivity

  have hmesh : 2 < fineScale * (base ^ (levels + 1) : ℝ) := by
    have h1 :
        fineScale * (base ^ (levels + 1) : ℝ) = (base : ℝ) := by
      simp only [hfineScale_def]
      field_simp [hbase_pos.ne']
      ring
    rw [h1]
    norm_num
    linarith

  have htree := planar_grid_partition_tree
    atomized.centers atomized.centers_nonempty base (levels + 1)
    hbase2 fineScale hfine_pos atomized.centers_separated hmesh

  have hpart_props : ∀ level : ℕ, level ≤ levels + 1 →
      (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ atomized.centers) ∧
      (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
        cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      (atomized.centers ⊆ Finset.biUnion (P level) id) :=
    fun level hle => htree.1 level hle

  have hterminal : ∀ cell ∈ P (levels + 1), cell.card = 1 :=
    htree.2.1

  have hnesting : ∀ level : ℕ, level < levels + 1 →
      ∀ child ∈ P (level + 1), ∃ parent ∈ P level, child ⊆ parent :=
    htree.2.2.1

  have hcard : ∀ level : ℕ, level ≤ levels + 1 →
      ∃ cellCard : ℕ, 0 < cellCard ∧
        ∀ cell ∈ P level, (uniform.centers ∩ cell).Nonempty →
          (uniform.centers ∩ cell).card = cellCard := by
    intro level hle
    exact h_branching (α := Point2) atomized.centers (levels + 1) P
      hpart_props hterminal hnesting
      uniform.centers uniform.centers_nonempty uniform.centers_subset
      uniform.branchExponent uniform.exact_branching level hle

  have huniform_sub : uniform.centers ⊆ atomized.centers :=
    uniform.centers_subset

  refine' ⟨_, _, _, _, _⟩

  · intro level hle cell hcell
    let S := uniform.centers ∩ cell
    have hS_to_atom : ∀ c ∈ S, c ∈ atomized.centers := by
      intro c hc
      exact huniform_sub ((Finset.mem_inter.mp hc).1)
    apply MeasurableSet.biUnion (Finset.countable_toSet S)
    intro c hc
    exact atomized.atom_measurable c (hS_to_atom c hc)

  · intro level hle cell hcell x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨c, hc, hxc⟩
    have hc_uniform : c ∈ uniform.centers :=
      (Finset.mem_inter.mp hc).1
    rw [uniform.retainedBand_eq]
    exact Set.mem_iUnion₂.mpr ⟨c, hc_uniform, hxc⟩

  · intro level hle cell hcell hnonempty
    rcases hnonempty with ⟨c, hc⟩
    have hc_uniform : c ∈ uniform.centers :=
      (Finset.mem_inter.mp hc).1
    have hc_atomized : c ∈ atomized.centers :=
      huniform_sub hc_uniform
    have h_pos : μ (atom c) ≠ 0 :=
      atomized.atom_mass_pos c hc_atomized
    have h_sub :
        atom c ⊆ finiteAtomUnion (uniform.centers ∩ cell) atom := by
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨c, hc, hy⟩
    have h_mono :
        μ (atom c) ≤
          μ (finiteAtomUnion (uniform.centers ∩ cell) atom) :=
      measure_mono h_sub
    have h_band :
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell =
          finiteAtomUnion (uniform.centers ∩ cell) atom := by
      rfl
    intro h_eq
    rw [h_band] at h_eq
    rw [h_eq] at h_mono
    have h_eq0 : μ (atom c) = 0 := by simpa using h_mono
    exact h_pos h_eq0

  · intro level hle cell hcell
    let S := uniform.centers ∩ cell
    have hS_to_atom : ∀ c ∈ S, c ∈ atomized.centers := by
      intro c hc
      exact huniform_sub ((Finset.mem_inter.mp hc).1)
    have hmeas : ∀ c ∈ S, MeasurableSet (atom c) := by
      intro c hc
      exact atomized.atom_measurable c (hS_to_atom c hc)
    have h_pd : (↑S : Set Point2).PairwiseDisjoint atom := by
      intro a ha b hb hne
      exact atomized.atom_disjoint
        a (hS_to_atom a ha) b (hS_to_atom b hb) hne
    have h_band :
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell =
          finiteAtomUnion S atom := by
      rfl
    have hsum :
        μ (finiteAtomUnion S atom) = ∑ c ∈ S, μ (atom c) := by
      simpa [finiteAtomUnion] using
        MeasureTheory.measure_biUnion_finset h_pd hmeas
    rw [h_band, hsum]
    have hsum_ne_top : (∑ c ∈ S, μ (atom c)) ≠ ⊤ := by
      have h : ∀ c ∈ S, μ (atom c) < ⊤ := by
        intro c hc
        have hne : μ (atom c) ≠ ⊤ :=
          atomized.atom_mass_ne_top c (hS_to_atom c hc)
        simpa [lt_top_iff_ne_top] using hne
      have h' : (∑ c ∈ S, μ (atom c)) < ⊤ :=
        ENNReal.sum_lt_top.mpr h
      simpa [lt_top_iff_ne_top] using h'
    exact hsum_ne_top

  · intro level hle cell₁ hcell₁ hnonempty₁
      cell₂ hcell₂ hnonempty₂
    rcases hcard level hle with ⟨cellCard, hcard_pos, hcard_eq⟩
    let S₁ := uniform.centers ∩ cell₁
    let S₂ := uniform.centers ∩ cell₂
    have hS₁_nonempty : S₁.Nonempty := hnonempty₁
    have hS₂_nonempty : S₂.Nonempty := hnonempty₂
    have hcard₁ : S₁.card = cellCard :=
      hcard_eq cell₁ hcell₁ hnonempty₁
    have hcard₂ : S₂.card = cellCard :=
      hcard_eq cell₂ hcell₂ hnonempty₂
    have hS1_to_atom : ∀ c ∈ S₁, c ∈ atomized.centers := by
      intro c hc
      exact huniform_sub ((Finset.mem_inter.mp hc).1)
    have hS2_to_atom : ∀ c ∈ S₂, c ∈ atomized.centers := by
      intro c hc
      exact huniform_sub ((Finset.mem_inter.mp hc).1)

    have hmeas₁ : ∀ c ∈ S₁, MeasurableSet (atom c) := by
      intro c hc
      exact atomized.atom_measurable c (hS1_to_atom c hc)
    have h_pd1 : (↑S₁ : Set Point2).PairwiseDisjoint atom := by
      intro a ha b hb hne
      exact atomized.atom_disjoint
        a (hS1_to_atom a ha) b (hS1_to_atom b hb) hne
    have hsum₁ :
        μ (finiteAtomUnion S₁ atom) = ∑ c ∈ S₁, μ (atom c) := by
      simpa [finiteAtomUnion] using
        MeasureTheory.measure_biUnion_finset h_pd1 hmeas₁

    have hmeas₂ : ∀ c ∈ S₂, MeasurableSet (atom c) := by
      intro c hc
      exact atomized.atom_measurable c (hS2_to_atom c hc)
    have h_pd2 : (↑S₂ : Set Point2).PairwiseDisjoint atom := by
      intro a ha b hb hne
      exact atomized.atom_disjoint
        a (hS2_to_atom a ha) b (hS2_to_atom b hb) hne
    have hsum₂ :
        μ (finiteAtomUnion S₂ atom) = ∑ c ∈ S₂, μ (atom c) := by
      simpa [finiteAtomUnion] using
        MeasureTheory.measure_biUnion_finset h_pd2 hmeas₂

    let S := S₁ ∪ S₂
    have hS_nonempty : S.Nonempty := by
      have hsub : S₁ ⊆ S := by
        intro x hx
        exact Finset.mem_union_left S₂ hx
      exact Finset.Nonempty.mono hsub hS₁_nonempty
    rcases Finset.exists_min_image S (fun c => μ (atom c))
        hS_nonempty with
      ⟨c_min, hc_min_S, hmin_prop⟩
    let m_min := μ (atom c_min)

    have hc_min_atomized : c_min ∈ atomized.centers := by
      have h : c_min ∈ S₁ ∪ S₂ := hc_min_S
      have h' : c_min ∈ S₁ ∨ c_min ∈ S₂ :=
        Finset.mem_union.mp h
      rcases h' with (h_in1 | h_in2)
      · exact hS1_to_atom c_min h_in1
      · exact hS2_to_atom c_min h_in2

    have h1 : ∀ c ∈ S₁, μ (atom c) ≤ 2 * m_min := by
      intro c hc
      have hc_atomized : c ∈ atomized.centers :=
        hS1_to_atom c hc
      exact atomized.atom_mass_comparable
        c hc_atomized c_min hc_min_atomized

    have h2 : ∀ c ∈ S₂, m_min ≤ μ (atom c) := by
      intro c hc
      have hc_S : c ∈ S := Finset.mem_union_right S₁ hc
      exact hmin_prop c hc_S

    have h_sum1 :
        ∑ c ∈ S₁, μ (atom c) ≤
          2 * (S₁.card : ENNReal) * m_min := by
      calc
        ∑ c ∈ S₁, μ (atom c)
            ≤ ∑ c ∈ S₁, (2 * m_min) := by
              apply Finset.sum_le_sum
              intro i hi
              exact h1 i hi
        _ = 2 * (S₁.card : ENNReal) * m_min := by
          rw [Finset.sum_const]
          ring

    have h_sum2 :
        (S₂.card : ENNReal) * m_min ≤
          ∑ c ∈ S₂, μ (atom c) := by
      calc
        (S₂.card : ENNReal) * m_min
            = ∑ c ∈ S₂, m_min := by
              simp [Finset.sum_const]
        _ ≤ ∑ c ∈ S₂, μ (atom c) := by
          apply Finset.sum_le_sum
          intro i hi
          exact h2 i hi

    have h_final :
        ∑ c ∈ S₁, μ (atom c) ≤
          2 * ∑ c ∈ S₂, μ (atom c) := by
      calc
        ∑ c ∈ S₁, μ (atom c)
            ≤ 2 * (S₁.card : ENNReal) * m_min := h_sum1
        _ = 2 * ((S₁.card : ENNReal) * m_min) := by ring
        _ = 2 * ((cellCard : ENNReal) * m_min) := by
          rw [show (S₁.card : ENNReal) = (cellCard : ENNReal) from
            by exact_mod_cast hcard₁]
        _ = 2 * ((S₂.card : ENNReal) * m_min) := by
          rw [show (S₂.card : ENNReal) = (cellCard : ENNReal) from
            by exact_mod_cast hcard₂]
        _ ≤ 2 * (∑ c ∈ S₂, μ (atom c)) := by
          exact (mul_le_mul_right h_sum2) 2

    have h_band1 :
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell₁ =
          finiteAtomUnion S₁ atom := by
      rfl
    have h_band2 :
        projectedFiberOSCellBand
            Y f bandData base levels uniform.centers cell₂ =
          finiteAtomUnion S₂ atom := by
      rfl
    rw [h_band1, h_band2]
    rw [hsum₁, hsum₂]
    exact h_final

end Kakeya.Assouad
