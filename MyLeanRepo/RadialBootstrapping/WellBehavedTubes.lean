module

/-
  WellBehavedTubes.lean

  Proof of well_behaved_tubes with G-intersection bad tubes.
  Uses Lindelöf covering + continuity from below.
  Does NOT require hG_fiber or ball growth bound.

  Key idea: define bad tubes by ν₂(tube_r(ℓ) ∩ G_x) ≥ K'·r^(σ+τ).
  Then the lower bound per tube is immediate from badness.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.HBarGMeasurable

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

-- ============================================================================
-- Definitions
-- ============================================================================

/-- r-tube around an affine subspace. -/
def WBTG.tubeLine (r : ℝ) (ℓ : AffineSubspace ℝ Point) : Set Point :=
  Metric.thickening r (ℓ : Set Point)

/-- Bad tubes through x: G-intersection mass > K'·r^(σ+τ).
    Strict inequality ensures compatibility with open/measurable bad sets. -/
def WBTG.BadTubesG (ν₂ : Measure Point)
    (G : Set (Point × Point)) (K' σ τ r : ℝ) (x : Point) :
    Set (AffineSubspace ℝ Point) :=
  {ℓ | x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 ∧
    ν₂ {b₂ | b₂ ∈ WBTG.tubeLine r ℓ ∧ (x, b₂) ∈ G} >
      ENNReal.ofReal (K' * Real.rpow r (σ + τ))}

/-- Set of pairs (x,y) where y is in a bad G-tube through x. -/
def WBTG.HBarG_r (ν₂ : Measure Point)
    (G : Set (Point × Point)) (K' σ τ r : ℝ) :
    Set (Point × Point) :=
  {p | ∃ ℓ ∈ WBTG.BadTubesG ν₂ G K' σ τ r p.1,
    p.2 ∈ WBTG.tubeLine r ℓ}

/-- H_r = G ∩ HBarG_r. -/
def WBTG.HG_r (G : Set (Point × Point))
    (ν₂ : Measure Point) (K' σ τ r : ℝ) :
    Set (Point × Point) :=
  G ∩ WBTG.HBarG_r ν₂ G K' σ τ r

/-- XSet: x such that ν₂(HG_r|_x) ≥ r^τ. -/
def WBTG.XSet (HG_r : Set (Point × Point))
    (ν₂ : Measure Point) (r τ : ℝ) : Set Point :=
  {x | ν₂ {b₂ | (x, b₂) ∈ HG_r} ≥ ENNReal.ofReal (Real.rpow r τ)}

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- Extract a well-behaved finite tube family T_x and fiber Y_x.

With G-intersection bad tubes, no hG_fiber is needed: the lower bound
per tube comes directly from the badness condition. -/
theorem well_behaved_tubes_G
    (ν₁ ν₂ : ProbabilityMeasure Point)
    (G : Set (Point × Point))
    (K K' σ τ r c : ℝ)
    (hσ : 0 ≤ σ) (hτ : 0 < τ) (hr : 0 < r) (hr_small : r < 1)
    (hK_small : K * Real.rpow r τ ≤ 1)
    (hK'_lower : K' ≥ Real.rpow r (2 * τ))
    (hG_meas : MeasurableSet G)
    (hG_forward : ∀ x ∈ (ν₁ : Measure Point).support,
      ∀ ℓ : AffineSubspace ℝ Point, x ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ r' : ℝ, 0 < r' →
          ν₂ {b₂ | b₂ ∈ WBTG.tubeLine r' ℓ ∧ (x, b₂) ∈ G} ≤
            ENNReal.ofReal (K * Real.rpow r' σ))
    (x : Point) (hx_supp : x ∈ (ν₁ : Measure Point).support)
    (hx : x ∈ WBTG.XSet (WBTG.HG_r G ν₂ K' σ τ r) ν₂ r τ) :
    ∃ (T_x : Finset (AffineSubspace ℝ Point))
      (Y_x : Set Point),
      MeasurableSet Y_x ∧
      (∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1) ∧
      Y_x ⊆ {b₂ | (x, b₂) ∈ WBTG.HG_r G ν₂ K' σ τ r} ∧
      Y_x ⊆ ⋃ ℓ ∈ T_x, WBTG.tubeLine r ℓ ∧
      ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) ∧
      (∀ ℓ ∈ T_x,
        ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤
          ν₂ (WBTG.tubeLine r ℓ ∩ Y_x) ∧
        ν₂ (WBTG.tubeLine r ℓ ∩ Y_x) ≤
          ENNReal.ofReal (Real.rpow r (σ - τ))) := by
  let μ : Measure Point := ν₂
  let G_x : Set Point := {b₂ | (x, b₂) ∈ G}
  let H_x : Set Point := {b₂ | (x, b₂) ∈ WBTG.HG_r G ν₂ K' σ τ r}
  let Bad : Set (AffineSubspace ℝ Point) :=
    WBTG.BadTubesG μ G K' σ τ r x

  have h_coe : ∀ (S : Set Point), (ν₂ S : ENNReal) = μ S :=
    fun S => ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν₂ S

  have hHx_measure : μ H_x ≥ ENNReal.ofReal (Real.rpow r τ) := by
    have h1 : ν₂ H_x ≥ ENNReal.ofReal (Real.rpow r τ) := by
      simpa [H_x, WBTG.XSet] using hx
    have h2 : (ν₂ H_x : ENNReal) = μ H_x := h_coe H_x
    rw [h2] at h1
    exact h1

  have hHx_nonempty : H_x.Nonempty := by
    by_contra h
    have h_empty : H_x = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at hHx_measure
    have h_pos : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
    have h10 : (0 : ENNReal) < ENNReal.ofReal (Real.rpow r τ) :=
      ENNReal.ofReal_pos.mpr h_pos
    have h9 : μ ∅ = 0 := measure_empty
    rw [h9] at hHx_measure
    exact not_le.mpr h10 hHx_measure

  -- H_x is covered by bad tubes
  have h_cover : H_x ⊆ ⋃ ℓ ∈ Bad, WBTG.tubeLine r ℓ := by
    intro y hy
    have h_in_HG : (x, y) ∈ WBTG.HG_r G ν₂ K' σ τ r := hy
    have h_in_HBar : (x, y) ∈ WBTG.HBarG_r ν₂ G K' σ τ r := h_in_HG.2
    rcases h_in_HBar with ⟨ℓ, hℓ_bad, hy_in_tube⟩
    exact Set.mem_iUnion₂.mpr ⟨ℓ, hℓ_bad, hy_in_tube⟩

  let ι := {ℓ : AffineSubspace ℝ Point // ℓ ∈ Bad}
  let U : ι → Set Point := fun p => WBTG.tubeLine r p.val

  have hU_cover : H_x ⊆ ⋃ (i : ι), U i := by
    intro y hy
    have h1 : y ∈ ⋃ ℓ ∈ Bad, WBTG.tubeLine r ℓ := h_cover hy
    rcases Set.mem_iUnion₂.mp h1 with ⟨ℓ, hℓ, hy2⟩
    let p : ι := ⟨ℓ, hℓ⟩
    exact Set.mem_iUnion.mpr ⟨p, hy2⟩

  have hU_open : ∀ (i : ι), IsOpen (U i) := by
    intro i; exact isOpen_thickening

  have h_lindelof_Hx : IsLindelof H_x := by
    have h : HereditarilyLindelofSpace Point := by infer_instance
    have h' : IsHereditarilyLindelof (Set.univ : Set Point) := by exact HereditarilyLindelofSpace.isHereditarilyLindelof_univ
    exact IsHereditarilyLindelof.isLindelof_subset h' (Set.subset_univ H_x)

  rcases IsLindelof.elim_countable_subcover h_lindelof_Hx U hU_open hU_cover
    with ⟨S, hS_count, hS_cover⟩

  have hS_nonempty : S.Nonempty := by
    by_contra h
    have h_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at hS_cover
    simp at hS_cover
    have h_contra : H_x = ∅ := by simpa using hS_cover
    have h9 : ¬H_x.Nonempty := by rw [h_contra]; simp
    exact h9 hHx_nonempty

  rcases hS_count.exists_eq_range hS_nonempty with ⟨f, hf_range⟩

  let A : ℕ → Set Point := fun n => H_x ∩ ⋃ i ∈ Finset.range n, U (f i)

  have hA_mono : Monotone A := by
    intro n m hnm
    have h11 : Finset.range n ⊆ Finset.range m := by
      intro x hx
      have h : x < n := Finset.mem_range.mp hx
      have h' : x < m := lt_of_lt_of_le h hnm
      exact Finset.mem_range.mpr h'
    have h1 : (⋃ i ∈ Finset.range n, U (f i)) ⊆ (⋃ i ∈ Finset.range m, U (f i)) := by
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨h_in, hyi⟩
      have h_i_in : i ∈ Finset.range m := h11 h_in
      exact Set.mem_biUnion h_i_in hyi
    exact Set.inter_subset_inter_right H_x h1

  have hA_union : (⋃ n, A n) = H_x := by
    apply Set.Subset.antisymm
    · intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
      exact hn.1
    · intro y hy
      have h_in_S : y ∈ ⋃ i ∈ S, U i := hS_cover hy
      rcases Set.mem_iUnion.mp h_in_S with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨hiS, hyU⟩
      have h_i_in_range : i ∈ Set.range f := by
        have h : i ∈ S := hiS
        have h2 : S = Set.range f := hf_range
        rw [h2] at h
        exact h
      rcases Set.mem_range.mp h_i_in_range with ⟨n, hfn⟩
      have h4 : y ∈ U (f n) := by rw [hfn] <;> exact hyU
      have h5 : y ∈ A (n + 1) := by
        dsimp only [A]
        constructor
        · exact hy
        · have h6 : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
          have h7 : y ∈ (⋃ i ∈ Finset.range (n + 1), U (f i)) := by
            exact Set.mem_biUnion h6 h4
          exact h7
      exact Set.mem_iUnion.mpr ⟨n + 1, h5⟩

  have h_cont : μ (⋃ n, A n) = ⨆ n, μ (A n) :=
    Monotone.measure_iUnion hA_mono

  have h_rpow_lt : Real.rpow r (2 * τ) < Real.rpow r τ := by
    have h1 : τ < 2 * τ := by linarith
    have h2 : 0 < r := hr
    have h3 : r < 1 := hr_small
    exact Real.rpow_lt_rpow_of_exponent_gt h2 h3 h1

  have rτ_gt_r2τ : ENNReal.ofReal (Real.rpow r (2 * τ)) <
      ENNReal.ofReal (Real.rpow r τ) := by
    have h_pos2 : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
    exact (ENNReal.ofReal_lt_ofReal_iff h_pos2).mpr h_rpow_lt

  have h_main : ∃ n : ℕ, μ (A n) ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) := by
    by_contra h
    have h' : ∀ n, μ (A n) < ENNReal.ofReal (Real.rpow r (2 * τ)) := by simpa using h
    have h'' : ∀ n, μ (A n) ≤ ENNReal.ofReal (Real.rpow r (2 * τ)) := by
      intro n; exact le_of_lt (h' n)
    have h3 : (⨆ n, μ (A n)) ≤ ENNReal.ofReal (Real.rpow r (2 * τ)) := by
      exact iSup_le h''
    have h4 : μ (⋃ n, A n) ≤ ENNReal.ofReal (Real.rpow r (2 * τ)) := by
      rw [h_cont] <;> exact h3
    rw [hA_union] at h4
    have h5 : ENNReal.ofReal (Real.rpow r τ) ≤ μ H_x := hHx_measure
    have h6 : μ H_x ≤ ENNReal.ofReal (Real.rpow r (2 * τ)) := h4
    exact not_le.mpr rτ_gt_r2τ (le_trans h5 h6)

  rcases h_main with ⟨n, hn_measure⟩

  let T_x : Finset (AffineSubspace ℝ Point) :=
    Finset.image (fun (i : ℕ) => (f i).val) (Finset.range n)
  let Y_x : Set Point := A n

  have hY_sub_Hx : Y_x ⊆ H_x := by
    intro z hz; exact hz.1

  have hY_sub_union : Y_x ⊆ ⋃ ℓ ∈ T_x, WBTG.tubeLine r ℓ := by
    intro y hy
    have h5 : y ∈ ⋃ i ∈ Finset.range n, U (f i) := hy.2
    rcases Set.mem_iUnion.mp h5 with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨h_in, hyU⟩
    let ℓ : AffineSubspace ℝ Point := (f i).val
    have hℓ_in_Tx : ℓ ∈ T_x := by
      dsimp only [T_x]
      exact Finset.mem_image.mpr ⟨i, h_in, rfl⟩
    have h7 : y ∈ WBTG.tubeLine r ℓ := hyU
    exact Set.mem_biUnion hℓ_in_Tx h7

  have h_lines : ∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨i, _hi, rfl⟩
    have h_prop : (f i).val ∈ Bad := (f i).property
    have h1 : x ∈ ((f i).val : Set Point) ∧ Module.finrank ℝ ((f i).val).direction = 1 := by
      dsimp only [Bad, WBTG.BadTubesG] at h_prop
      exact ⟨h_prop.1, h_prop.2.1⟩
    exact h1

  -- Key: for each ℓ ∈ T_x, tube_r(ℓ) ∩ Y_x = tube_r(ℓ) ∩ G_x
  have h_bounds : ∀ ℓ ∈ T_x,
      ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤
        μ (WBTG.tubeLine r ℓ ∩ Y_x) ∧
      μ (WBTG.tubeLine r ℓ ∩ Y_x) ≤
        ENNReal.ofReal (Real.rpow r (σ - τ)) := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨i, hi, rfl⟩
    let p : ι := f i
    have hp_bad : p.val ∈ Bad := p.property
    have h_x_mem : x ∈ (p.val : Set Point) := hp_bad.1
    have h_finrank : Module.finrank ℝ p.val.direction = 1 := hp_bad.2.1
    have h_mass_strict : μ {b₂ | b₂ ∈ WBTG.tubeLine r p.val ∧ (x, b₂) ∈ G} >
        ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := hp_bad.2.2
    have h_mass : μ {b₂ | b₂ ∈ WBTG.tubeLine r p.val ∧ (x, b₂) ∈ G} ≥
        ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := le_of_lt h_mass_strict

    have h_tube_sub_HBar : WBTG.tubeLine r p.val ⊆
        {b₂ | (x, b₂) ∈ WBTG.HBarG_r μ G K' σ τ r} := by
      intro y hy
      exact ⟨p.val, hp_bad, hy⟩

    have h6 : WBTG.tubeLine r p.val ⊆ ⋃ j ∈ Finset.range n, U (f j) := by
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩

    have h_eq1 : WBTG.tubeLine r p.val ∩ Y_x = WBTG.tubeLine r p.val ∩ H_x := by
      dsimp only [Y_x, A]
      ext z
      simp only [Set.mem_inter_iff]
      have h7 : WBTG.tubeLine r p.val ⊆ (⋃ j ∈ Finset.range n, U (f j)) := h6
      constructor
      · intro h; exact ⟨h.1, h.2.1⟩
      · intro h; exact ⟨h.1, h.2, h7 h.1⟩

    have h_eq2 : WBTG.tubeLine r p.val ∩ H_x =
        WBTG.tubeLine r p.val ∩ G_x := by
      dsimp only [H_x, WBTG.HG_r]
      have h7 : WBTG.tubeLine r p.val ⊆
          {b₂ | (x, b₂) ∈ WBTG.HBarG_r μ G K' σ τ r} := h_tube_sub_HBar
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h; exact ⟨h.1, h.2.1⟩
      · intro h; exact ⟨h.1, h.2, h7 h.1⟩

    have h_eq : WBTG.tubeLine r p.val ∩ Y_x =
        WBTG.tubeLine r p.val ∩ G_x := by
      rw [h_eq1, h_eq2]

    rw [h_eq]

    -- Lower bound: directly from badness
    have h_set_eq : {b₂ | b₂ ∈ WBTG.tubeLine r p.val ∧ (x, b₂) ∈ G} =
                     WBTG.tubeLine r p.val ∩ G_x := by
      ext y
      simp [G_x, WBTG.tubeLine] <;> aesop

    have h_lower1 : μ (WBTG.tubeLine r p.val ∩ G_x) ≥
        ENNReal.ofReal (K' * Real.rpow r (σ + τ)) := by
      rw [← h_set_eq]
      exact h_mass

    have hK'_nonneg : 0 ≤ K' := by
      have h1 : 0 ≤ Real.rpow r (2 * τ) := Real.rpow_nonneg (by linarith) _
      linarith [hK'_lower]

    have h_mul : K' * Real.rpow r (σ + τ) ≥ Real.rpow r (σ + 3 * τ) := by
      have h1 : Real.rpow r (2 * τ) * Real.rpow r (σ + τ) = Real.rpow r (σ + 3 * τ) := by
        have h : Real.rpow r ((2 * τ) + (σ + τ)) =
            Real.rpow r (2 * τ) * Real.rpow r (σ + τ) :=
          Real.rpow_add (by linarith) (2 * τ) (σ + τ)
        have h2 : (2 * τ) + (σ + τ) = σ + 3 * τ := by ring
        rw [h2] at h
        exact h.symm
      calc
        K' * Real.rpow r (σ + τ)
          ≥ Real.rpow r (2 * τ) * Real.rpow r (σ + τ) := by
            exact mul_le_mul_of_nonneg_right hK'_lower (Real.rpow_nonneg (by linarith) _)
        _ = Real.rpow r (σ + 3 * τ) := h1

    have h_lower_final : ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤
        μ (WBTG.tubeLine r p.val ∩ G_x) := by
      calc ENNReal.ofReal (Real.rpow r (σ + 3 * τ))
        ≤ ENNReal.ofReal (K' * Real.rpow r (σ + τ)) :=
          ENNReal.ofReal_le_ofReal h_mul
      _ ≤ μ (WBTG.tubeLine r p.val ∩ G_x) := h_lower1

    -- Upper bound: from hG_forward
    have hG_forward' : μ {b₂ | b₂ ∈ WBTG.tubeLine r p.val ∧ (x, b₂) ∈ G} ≤
        ENNReal.ofReal (K * Real.rpow r σ) := by
      have h10 := hG_forward x hx_supp p.val h_x_mem h_finrank r hr
      have h11 : (ν₂ {b₂ | b₂ ∈ WBTG.tubeLine r p.val ∧ (x, b₂) ∈ G} : ENNReal) =
          μ {b₂ | b₂ ∈ WBTG.tubeLine r p.val ∧ (x, b₂) ∈ G} := h_coe _
      rw [h11] at h10
      exact h10

    have h_upper1 : μ (WBTG.tubeLine r p.val ∩ G_x) ≤
        ENNReal.ofReal (K * Real.rpow r σ) := by
      rw [← h_set_eq]
      exact hG_forward'

    have h_K_bound : K * Real.rpow r σ ≤ Real.rpow r (σ - τ) := by
      have h11 : K * Real.rpow r τ ≤ 1 := hK_small
      have h12 : Real.rpow r σ = Real.rpow r τ * Real.rpow r (σ - τ) := by
        have h13 : Real.rpow r (τ + (σ - τ)) =
            Real.rpow r τ * Real.rpow r (σ - τ) :=
          Real.rpow_add (by linarith) τ (σ - τ)
        have h14 : τ + (σ - τ) = σ := by ring
        rw [h14] at h13
        exact h13
      have h15 : 0 ≤ Real.rpow r (σ - τ) := Real.rpow_nonneg (by linarith) _
      calc
        K * Real.rpow r σ
          = K * (Real.rpow r τ * Real.rpow r (σ - τ)) := by rw [h12]
        _ = (K * Real.rpow r τ) * Real.rpow r (σ - τ) := by ring
        _ ≤ 1 * Real.rpow r (σ - τ) := by
          exact mul_le_mul_of_nonneg_right h11 h15
        _ = Real.rpow r (σ - τ) := by ring

    have h_upper_final : μ (WBTG.tubeLine r p.val ∩ G_x) ≤
        ENNReal.ofReal (Real.rpow r (σ - τ)) := by
      calc μ (WBTG.tubeLine r p.val ∩ G_x)
        ≤ ENNReal.ofReal (K * Real.rpow r σ) := h_upper1
      _ ≤ ENNReal.ofReal (Real.rpow r (σ - τ)) :=
          ENNReal.ofReal_le_ofReal h_K_bound

    exact ⟨h_lower_final, h_upper_final⟩

  -- Convert conclusion from μ to ν₂
  have hY_measure_nnreal : ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) := by
    have h1 : (ν₂ Y_x : ENNReal) = μ Y_x := h_coe Y_x
    rw [h1]
    exact hn_measure

  have h_bounds_nnreal : ∀ ℓ ∈ T_x,
      ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤
        ν₂ (WBTG.tubeLine r ℓ ∩ Y_x) ∧
      ν₂ (WBTG.tubeLine r ℓ ∩ Y_x) ≤
        ENNReal.ofReal (Real.rpow r (σ - τ)) := by
    intro ℓ hℓ
    have h := h_bounds ℓ hℓ
    have h1 : (ν₂ (WBTG.tubeLine r ℓ ∩ Y_x) : ENNReal) =
        μ (WBTG.tubeLine r ℓ ∩ Y_x) := h_coe (WBTG.tubeLine r ℓ ∩ Y_x)
    constructor
    · rw [h1]; exact h.1
    · rw [h1]; exact h.2

  -- Measurability of Y_x
  have hHBarG_meas : MeasurableSet (WBTG.HBarG_r ν₂ G K' σ τ r) := by
    have h_eq : HBarG_r_strict ν₂ G K' σ τ r = WBTG.HBarG_r ν₂ G K' σ τ r := by
      ext p
      simp [HBarG_r_strict, WBTG.HBarG_r, BadTubesG_strict, WBTG.BadTubesG]
      <;> rfl
    rw [←h_eq]
    have hK'_nonneg : 0 ≤ K' := by
      have h1 : 0 ≤ Real.rpow r (2 * τ) := Real.rpow_nonneg (by linarith) _
      linarith
    exact HBarG_r_strict_measurable ν₂ G hG_meas K' σ τ r hr hK'_nonneg (by linarith)
  have hHG_meas : MeasurableSet (WBTG.HG_r G ν₂ K' σ τ r) :=
    hG_meas.inter hHBarG_meas
  have hHx_meas : MeasurableSet H_x := by
    have h1 : H_x = {b₂ | (x, b₂) ∈ WBTG.HG_r G ν₂ K' σ τ r} := by rfl
    rw [h1]
    exact hHG_meas.preimage (by fun_prop)
  have hUnion_meas : MeasurableSet (⋃ i ∈ Finset.range n, U (f i)) := by
    apply Finset.measurableSet_biUnion
    intro i _
    exact isOpen_thickening.measurableSet
  have hYx_meas : MeasurableSet Y_x := by
    dsimp only [Y_x, A]
    exact hHx_meas.inter hUnion_meas

  exact ⟨T_x, Y_x, hYx_meas, h_lines, hY_sub_Hx, hY_sub_union, hY_measure_nnreal, h_bounds_nnreal⟩

end RadialBootstrapping
