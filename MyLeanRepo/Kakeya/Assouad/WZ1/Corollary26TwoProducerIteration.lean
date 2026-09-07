import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredHierarchyIteration
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26BackwardSchedule

/-!
# Two-producer hierarchy iteration (without endpoint anchoring)

Builds the dependent iteration using `BackwardScheduleData`, which packages the
intermediate one-scale producer for levels `0 .. N-2` and the terminal-scale
producer for level `N-1`.

This module produces the final shading and all per-level trapezoid properties
EXCEPT active endpoints and unique parent nesting.
-/

namespace Kakeya.Assouad

open WZ1VerticalTrapezoid

/-! ## Level input loss -/

/-- Input loss at level j: `s.c 0` for j=0, `s.e (j-1)` for j>0. -/
def levelInputLoss {N sigma hierarchyLoss}
    (s : BackwardScheduleData N sigma hierarchyLoss) (j : ℕ) (hj : j < N) : ℝ :=
  match j with
  | 0 => s.c ⟨0, by omega⟩
  | k + 1 => s.e ⟨k, by omega⟩

lemma levelInputLoss_pos {N sigma hierarchyLoss}
    (s : BackwardScheduleData N sigma hierarchyLoss) (j : ℕ) (hj : j < N) :
    0 < levelInputLoss s j hj := by
  cases j with
  | zero => exact s.c_pos ⟨0, by omega⟩
  | succ k => exact s.e_pos ⟨k, by omega⟩

lemma levelInputLoss_le_c {N sigma hierarchyLoss}
    (s : BackwardScheduleData N sigma hierarchyLoss) (j : ℕ) (hj : j < N) :
    levelInputLoss s j hj ≤ s.c ⟨j, hj⟩ := by
  cases j with
  | zero => simp [levelInputLoss]
  | succ k =>
    have h1 : s.e ⟨k, by omega⟩ ≤ s.c ⟨k + 1, hj⟩ := by
      have h2 := s.e_le_c_next ⟨k, by omega⟩ (by omega)
      simpa using h2
    simpa [levelInputLoss] using h1

lemma levelInputLoss_le_e {N sigma hierarchyLoss}
    (s : BackwardScheduleData N sigma hierarchyLoss) (j : ℕ) (hj : j < N) :
    levelInputLoss s j hj ≤ s.e ⟨j, hj⟩ := by
  cases j with
  | zero =>
    have h1 : s.c ⟨0, by omega⟩ ≤ s.e ⟨0, by omega⟩ / 100 :=
      s.c_le_e_div_100 ⟨0, by omega⟩
    have h2 : s.e ⟨0, by omega⟩ / 100 ≤ s.e ⟨0, by omega⟩ := by
      have h3 : 0 < s.e ⟨0, by omega⟩ := s.e_pos ⟨0, by omega⟩
      linarith
    simpa [levelInputLoss] using h1.trans h2
  | succ k =>
    have h1 : s.e ⟨k, by omega⟩ ≤ s.c ⟨k + 1, hj⟩ := by
      have h2 := s.e_le_c_next ⟨k, by omega⟩ (by omega)
      simpa using h2
    have h3 : s.c ⟨k + 1, hj⟩ ≤ s.e ⟨k + 1, hj⟩ / 100 :=
      s.c_le_e_div_100 ⟨k + 1, hj⟩
    have h4 : s.e ⟨k + 1, hj⟩ / 100 ≤ s.e ⟨k + 1, hj⟩ := by
      have h5 : 0 < s.e ⟨k + 1, hj⟩ := s.e_pos ⟨k + 1, hj⟩
      linarith
    simpa [levelInputLoss] using h1.trans (h3.trans h4)

/-! ## Scale window verification -/

/-- Verify the Lemma 24 power window for an intermediate level. -/
lemma scale_window_bounds
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (s : BackwardScheduleData N sigma hierarchyLoss)
    (j : Fin N) (hj : (j : ℕ) + 1 < N)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (hrho : rho.1 = Real.rpow delta (((j : ℝ) + 1) / (N : ℝ))) :
    Real.rpow delta (1 - s.e j) ≤ rho.1 ∧
    rho.1 ≤ Real.rpow delta (s.e j) := by
  by_cases h : delta < 1
  · have h1 := s.window_lower j hj hdelta_pos h
    have h2 := s.window_upper j hj hdelta_pos h
    rw [hrho]
    exact ⟨h1, h2⟩
  · have h' : delta = 1 := by linarith
    have h3 : rho.1 = 1 := by
      rw [hrho, h']; simp
    rw [h3, h']
    simp

/-- The terminal hierarchy scale equals delta. -/
lemma terminal_scale_eq_delta_twoProd {delta : ℝ} {N : ℕ} (hN_pos : 0 < N)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1) :
    (rhoAt hN_pos hdelta_pos hdelta_one (N - 1) (by omega)).1 = delta := by
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have h_exp : (((N - 1 : ℕ) : ℝ) + 1) / (N : ℝ) = 1 := by
    have h2 : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      have h21 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ N by omega)] <;> norm_num
      rw [h21] <;> ring
    rw [h2] <;> field_simp [hN_pos'.ne'] <;> ring
  have h_main : (rhoAt hN_pos hdelta_pos hdelta_one (N - 1) (by omega)).1 =
      Real.rpow delta ((((N - 1 : ℕ) : ℝ) + 1) / (N : ℝ)) := by rfl
  rw [h_main, h_exp]
  exact Real.rpow_one delta

/-! ## Dependent level construction -/

/--
Build source and one-scale data for level `j` by forward dependent recursion.
Uses the intermediate producer for `j+1 < N` and the terminal producer for
`j = N-1`.
-/
noncomputable def buildTwoProdLevelData
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (s : BackwardScheduleData N sigma hierarchyLoss)
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hdelta_le_dmin : delta ≤ BackwardScheduleData.d_min s)
    (source0 : WZ1PlaninessGraininessPackage sigma (s.c ⟨0, by omega⟩) delta)
    (j : ℕ) (hj : j < N) :
    Σ (src : WZ1PlaninessGraininessPackage sigma (levelInputLoss s j hj) delta),
      WZ1LocallyLinearOneScaleData src (s.e ⟨j, hj⟩)
        (rhoAt hN_pos hdelta_pos hdelta_one j hj) :=
  match j with
  | 0 =>
    let jfin : Fin N := ⟨0, by omega⟩
    have h_int : (0 : ℕ) + 1 < N := by
      have hN2 : 2 ≤ N := s.hN_two
      omega
    let inputLoss := levelInputLoss s 0 (by omega)
    have h_inputLoss_pos : 0 < inputLoss := levelInputLoss_pos s 0 (by omega)
    have h_inputLoss_le_c : inputLoss ≤ s.c jfin := levelInputLoss_le_c s 0 (by omega)
    have h_delta_le_d : delta ≤ s.d jfin := le_trans hdelta_le_dmin (s.d_min_le_d jfin)
    let rho := rhoAt hN_pos hdelta_pos hdelta_one 0 (by omega)
    have hrho : rho.1 = Real.rpow delta (((jfin : ℝ) + 1) / (N : ℝ)) := by
      simp [rho, rhoAt, hierarchyAdmissibleScale, hierarchyScale, jfin]
      <;> norm_cast
    have h_bounds := scale_window_bounds s jfin h_int hdelta_pos hdelta_one rho hrho
    let produce := s.produce_intermediate jfin h_int
    let h_data := produce inputLoss h_inputLoss_pos h_inputLoss_le_c
      delta hdelta_pos h_delta_le_d source0 rho h_bounds.1 h_bounds.2
    ⟨source0, h_data.some⟩
  | k + 1 =>
    let prev := buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 k (by omega)
    have h_inc : levelInputLoss s k (by omega) ≤ s.e ⟨k, by omega⟩ :=
      levelInputLoss_le_e s k (by omega)
    let sourceNext : WZ1PlaninessGraininessPackage sigma (s.e ⟨k, by omega⟩) delta :=
      prev.2.toPlaninessGraininessPackage h_inc hdelta_pos hdelta_one
    have h_source_cast : s.e ⟨k, by omega⟩ = levelInputLoss s (k + 1) hj := by
      simp [levelInputLoss] <;> rfl
    let sourceNext' : WZ1PlaninessGraininessPackage sigma (levelInputLoss s (k + 1) hj) delta :=
      h_source_cast.symm ▸ sourceNext
    let jfin : Fin N := ⟨k + 1, hj⟩
    let rho := rhoAt hN_pos hdelta_pos hdelta_one (k + 1) hj
    have h_inputLoss_pos : 0 < levelInputLoss s (k + 1) hj :=
      levelInputLoss_pos s (k + 1) hj
    have h_inputLoss_le_c : levelInputLoss s (k + 1) hj ≤ s.c jfin :=
      levelInputLoss_le_c s (k + 1) hj
    have h_delta_le_d : delta ≤ s.d jfin := le_trans hdelta_le_dmin (s.d_min_le_d jfin)
    let data : WZ1LocallyLinearOneScaleData sourceNext' (s.e jfin) rho :=
      if h_int : (k + 1) + 1 < N then
        have hrho : rho.1 = Real.rpow delta (((jfin : ℝ) + 1) / (N : ℝ)) := by
          simp [rho, rhoAt, hierarchyAdmissibleScale, hierarchyScale, jfin] <;> norm_cast
        have h_bounds := scale_window_bounds s jfin h_int hdelta_pos hdelta_one rho hrho
        let produce := s.produce_intermediate jfin h_int
        let h_data := produce (levelInputLoss s (k + 1) hj) h_inputLoss_pos h_inputLoss_le_c
          delta hdelta_pos h_delta_le_d sourceNext' rho h_bounds.1 h_bounds.2
        h_data.some
      else
        have h_last : k + 1 = N - 1 := by omega
        let lastFin : Fin N := ⟨N - 1, by omega⟩
        have h_jfin_eq : jfin = lastFin := by apply Fin.ext; omega
        have h_inputLoss_le_c' : levelInputLoss s (k + 1) hj ≤ s.c lastFin := by
          rw [h_jfin_eq] at h_inputLoss_le_c; exact h_inputLoss_le_c
        have h_delta_le_d' : delta ≤ s.d lastFin := by
          rw [h_jfin_eq] at h_delta_le_d; exact h_delta_le_d
        have h_k_eq : k + 1 = N - 1 := by omega
        have h_rho_delta : rho.1 = delta := by
          have h_rho_eq : rho.1 = (rhoAt hN_pos hdelta_pos hdelta_one (N - 1) (by omega)).1 := by
            simp [rho, rhoAt, hierarchyAdmissibleScale, h_k_eq] <;> rfl
          rw [h_rho_eq]
          exact terminal_scale_eq_delta_twoProd hN_pos hdelta_pos hdelta_one
        let h_data := s.produce_terminal (levelInputLoss s (k + 1) hj)
          h_inputLoss_pos h_inputLoss_le_c' delta hdelta_pos h_delta_le_d'
          sourceNext' rho h_rho_delta
        have h_e : s.e jfin = s.targetLoss := by
          have h1 : (jfin : ℕ) = N - 1 := by omega
          rw [show jfin = ⟨N - 1, by omega⟩ from Fin.ext h1]
          exact s.e_last
        h_e.symm ▸ h_data.some
    ⟨sourceNext', data⟩

/-- At level k+1, source.shading equals data_k.shading. -/
lemma buildTwoProdLevelData_source_shading
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (s : BackwardScheduleData N sigma hierarchyLoss)
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hdelta_le_dmin : delta ≤ BackwardScheduleData.d_min s)
    (source0 : WZ1PlaninessGraininessPackage sigma (s.c ⟨0, by omega⟩) delta)
    {k : ℕ} (hk : k + 1 < N) :
    (buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 (k + 1) hk).1.shading =
    (buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 k (by omega)).2.shading := by
  simp [buildTwoProdLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage]

/-- Subshading chain: data_k.shading.union ⊆ data_j.shading.union for j ≤ k. -/
lemma buildTwoProdLevelData_chain
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (s : BackwardScheduleData N sigma hierarchyLoss)
    (hN_pos : 0 < N) (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hdelta_le_dmin : delta ≤ BackwardScheduleData.d_min s)
    (source0 : WZ1PlaninessGraininessPackage sigma (s.c ⟨0, by omega⟩) delta)
    {j k : ℕ} (hj : j < N) (hk : k < N) (hjk : j ≤ k) :
    (buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 k hk).2.shading.union ⊆
    (buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 j hj).2.shading.union := by
  induction k with
  | zero =>
    have h_j0 : j = 0 := by omega
    subst h_j0; exact Set.Subset.refl _
  | succ k ih =>
    by_cases h_jk : j = k + 1
    · subst h_jk; exact Set.Subset.refl _
    · have h_j_le_k : j ≤ k := by omega
      set b_k1 := buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 (k + 1) (by omega) with hb_k1
      set b_k := buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 k (by omega) with hb_k
      have h1 : b_k1.2.shading.union ⊆ b_k1.1.shading.union :=
        IsSubshading.union_subset b_k1.2.subshading
      have h_src_eq : b_k1.1.shading = b_k.2.shading :=
        buildTwoProdLevelData_source_shading s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 (by omega)
      have h_src_union_eq : b_k1.1.shading.union = b_k.2.shading.union :=
        congr_arg (fun (s : Kakeya.Streamlined.TubeShading _) => s.union) h_src_eq
      rw [h_src_union_eq] at h1
      exact Set.Subset.trans h1 (ih (by omega) h_j_le_k)

/-! ## Main construction lemma -/

/--
Construct the full hierarchy data without endpoint anchoring, using the
intermediate producer for levels `0 .. N-2` and the terminal producer for
level `N-1`.
-/
lemma construct_hierarchy_no_anchoring
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (hN_two : 2 ≤ N)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (s : BackwardScheduleData N sigma hierarchyLoss)
    (hdelta_le_dmin : delta ≤ BackwardScheduleData.d_min s)
    (source0 : WZ1PlaninessGraininessPackage sigma (s.c ⟨0, by omega⟩) delta) :
    ∃ (Z : Kakeya.Streamlined.TubeShading source0.family)
      (hZ_sub : IsSubshading Z source0.shading)
      (hZ_extremal : WZ1ExtremalPair sigma s.targetLoss source0.family source0.uniform Z)
      (trapezoids : Fin N → Finset WZ1VerticalTrapezoid)
      (h_level_nonempty : ∀ j, (trapezoids j).Nonempty)
      (h_height_eq : ∀ j, ∀ t ∈ trapezoids j,
          t.height = wz1Corollary26Scale delta N j)
      (h_slope_bound : ∀ j, ∀ t ∈ trapezoids j, |t.slope| ≤ 2)
      (h_length_bounds : ∀ j, ∀ t ∈ trapezoids j,
          Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
          t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
      (h_separated_cores : ∀ j, ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
          ∀ z ∈ t.core, ∀ w ∈ s.core,
            Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|)
      (h_slope_approximation : ∀ j, ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
          horizontalSlice Z.union z ≠ ∅ →
            |source0.global_grains.slope z - t.affine z| ≤ wz1Corollary26Scale delta N j)
      (h_active_height_coverage : ∀ j, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
          horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core)
      (multiplicity : ℕ)
      (h_multiplicity_pos : 0 < multiplicity)
      (h_constant_multiplicity : Z.HasConstantMultiplicity multiplicity (2 * multiplicity)),
      True := by
  have hN_pos : 0 < N := by linarith
  let last : ℕ := N - 1
  have hlast_lt : last < N := by omega
  let buildAt (j : ℕ) (hj : j < N) :=
    buildTwoProdLevelData s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 j hj
  let dataLast := (buildAt last hlast_lt).2
  let sourceLast := (buildAt last hlast_lt).1
  -- Family/slope transport
  have h_family_eq : ∀ (j : ℕ) (hj : j < N),
      (buildAt j hj).1.family = source0.family := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j' ih =>
      simp [buildAt, buildTwoProdLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage]
      <;> exact ih (by omega)
  have h_slope_eq : ∀ (j : ℕ) (hj : j < N),
      (buildAt j hj).1.global_grains.slope = source0.global_grains.slope := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j' ih =>
      simp [buildAt, buildTwoProdLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage]
      <;> exact ih (by omega)
  -- Final shading Z
  let Z : Kakeya.Streamlined.TubeShading source0.family :=
    (h_family_eq last hlast_lt) ▸ dataLast.shading
  have hZ_union_eq : Z.union = dataLast.shading.union :=
    transport_union (h_family_eq last hlast_lt) dataLast.shading
  let shading_j (j : ℕ) (hj : j < N) : Kakeya.Streamlined.TubeShading source0.family :=
    (h_family_eq j hj) ▸ (buildAt j hj).2.shading
  have h_uniform_transport : ∀ (j : ℕ) (hj : j < N),
      (h_family_eq j hj) ▸ (buildAt j hj).1.uniform = source0.uniform := by
    intro j hj
    induction j with
    | zero => dsimp only [buildAt, buildTwoProdLevelData] <;> rfl
    | succ j' ih =>
      simp [buildAt, buildTwoProdLevelData, WZ1LocallyLinearOneScaleData.toPlaninessGraininessPackage]
      <;> exact ih (by omega)
  -- Per-tube subshading chain
  have h_chain_shading : ∀ (j k : ℕ) (hj : j < N) (hk : k < N) (hjk : j ≤ k),
      IsSubshading (shading_j k hk) (shading_j j hj) := by
    intro j k hj hk hjk
    induction k with
    | zero =>
      have h_j0 : j = 0 := by omega
      subst h_j0
      exact fun _ => Set.Subset.refl _
    | succ k ih =>
      by_cases h_jk : j = k + 1
      · subst h_jk
        exact fun _ => Set.Subset.refl _
      · have h_j_le_k : j ≤ k := by omega
        have h_data_sub : IsSubshading (buildAt (k + 1) hk).2.shading (buildAt (k + 1) hk).1.shading :=
          (buildAt (k + 1) hk).2.subshading
        have h_src_eq : (buildAt (k + 1) hk).1.shading = (buildAt k (by omega)).2.shading :=
          buildTwoProdLevelData_source_shading s hN_pos hdelta_pos hdelta_one hdelta_le_dmin source0 hk
        have hsub' : IsSubshading (buildAt (k + 1) hk).2.shading (buildAt k (by omega)).2.shading := by
          rw [h_src_eq] at h_data_sub
          exact h_data_sub
        have h1 : IsSubshading (shading_j (k + 1) hk) (shading_j k (by omega)) :=
          transport_isSubshading (h_family_eq (k + 1) hk) hsub'
        have h2 := ih (by omega) h_j_le_k
        exact fun i => Set.Subset.trans (h1 i) (h2 i)
  -- Extremality at targetLoss
  have h_e_last : s.e ⟨last, hlast_lt⟩ = s.targetLoss := by
    have h1 : (⟨last, hlast_lt⟩ : Fin N) = ⟨N - 1, by omega⟩ := by
      apply Fin.ext
      simp [last]
    rw [h1]
    exact s.e_last
  have h_ext_raw : WZ1ExtremalPair sigma (s.e ⟨last, hlast_lt⟩)
      sourceLast.family sourceLast.uniform dataLast.shading :=
    dataLast.extremal
  have h_ext_target : WZ1ExtremalPair sigma s.targetLoss
      sourceLast.family sourceLast.uniform dataLast.shading := by
    simpa [h_e_last] using h_ext_raw
  have hZ_extremal : WZ1ExtremalPair sigma s.targetLoss source0.family source0.uniform Z := by
    have h_fam : sourceLast.family = source0.family := h_family_eq last hlast_lt
    have h_unif : h_fam ▸ sourceLast.uniform = source0.uniform :=
      h_uniform_transport last hlast_lt
    have hZ' : h_fam ▸ dataLast.shading = Z := by rfl
    exact transport_extremal h_fam h_unif hZ' h_ext_target
  have hZ_sub : IsSubshading Z source0.shading := by
    have h1 : IsSubshading Z (shading_j 0 (by omega)) :=
      h_chain_shading 0 last (by omega) hlast_lt (by omega)
    have h_data_sub : IsSubshading (buildAt 0 (by omega)).2.shading (buildAt 0 (by omega)).1.shading :=
      (buildAt 0 (by omega)).2.subshading
    have h2 : IsSubshading (shading_j 0 (by omega)) source0.shading :=
      transport_isSubshading (h_family_eq 0 (by omega)) h_data_sub
    exact fun i => Set.Subset.trans (h1 i) (h2 i)
  -- Union chain for coverage/slope approximation
  have h_chain_union : ∀ (j : ℕ) (hj : j < N),
      Z.union ⊆ (buildAt j hj).2.shading.union := by
    intro j hj
    have h1 : IsSubshading Z (shading_j j hj) :=
      h_chain_shading j last hj hlast_lt (by omega)
    have h2 : Z.union ⊆ (shading_j j hj).union := IsSubshading.union_subset h1
    have h3 : (shading_j j hj).union = (buildAt j hj).2.shading.union :=
      transport_union (h_family_eq j hj) (buildAt j hj).2.shading
    rw [h3] at h2
    exact h2
  -- Trapezoids
  let origTrapezoids (j : Fin N) : Finset WZ1VerticalTrapezoid :=
    (buildAt (j : ℕ) j.isLt).2.trapezoids
  let rho_j (j : Fin N) : ℝ := wz1Corollary26Scale delta N j
  have h_rho_eq : ∀ (j : Fin N), rho_j j = (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).1 := by
    intro j
    simp [rho_j, rhoAt, hierarchyScale_eq_wz1Scale, hierarchyScale] <;> rfl
  -- Transfer coverage
  have h_transfer_coverage : ∀ (j : Fin N), ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ origTrapezoids j, z ∈ t.core := by
    intro j z hz hactive
    have h_union : Z.union ⊆ (buildAt (j : ℕ) j.isLt).2.shading.union :=
      h_chain_union (j : ℕ) j.isLt
    have h_slice_sub : horizontalSlice Z.union z ⊆
        horizontalSlice (buildAt (j : ℕ) j.isLt).2.shading.union z := by
      intro p hp; exact ⟨h_union hp.1, hp.2⟩
    have h : horizontalSlice (buildAt (j : ℕ) j.isLt).2.shading.union z ≠ ∅ :=
      Set.Nonempty.mono h_slice_sub (Set.nonempty_iff_ne_empty.mpr hactive) |>.ne_empty
    exact (buildAt (j : ℕ) j.isLt).2.active_height_coverage z hz h
  -- Transfer slope approximation
  have h_transfer_approx : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j, ∀ z ∈ t.core,
      horizontalSlice Z.union z ≠ ∅ → |source0.global_grains.slope z - t.affine z| ≤ rho_j j := by
    intro j t ht z hz hactive
    have h_union : Z.union ⊆ (buildAt (j : ℕ) j.isLt).2.shading.union :=
      h_chain_union (j : ℕ) j.isLt
    have h_slice_sub : horizontalSlice Z.union z ⊆
        horizontalSlice (buildAt (j : ℕ) j.isLt).2.shading.union z := by
      intro p hp; exact ⟨h_union hp.1, hp.2⟩
    have h : horizontalSlice (buildAt (j : ℕ) j.isLt).2.shading.union z ≠ ∅ :=
      Set.Nonempty.mono h_slice_sub (Set.nonempty_iff_ne_empty.mpr hactive) |>.ne_empty
    have h_approx_raw := (buildAt (j : ℕ) j.isLt).2.slope_approximation t ht z hz h
    have h_slope : (buildAt (j : ℕ) j.isLt).1.global_grains.slope = source0.global_grains.slope :=
      h_slope_eq (j : ℕ) j.isLt
    rw [h_slope] at h_approx_raw
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one (j : ℕ) j.isLt).1 = rho_j j :=
      (h_rho_eq j).symm
    rw [h_rho] at h_approx_raw
    exact h_approx_raw
  -- Length bounds
  have h_length_bounds_all : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j,
      Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
      t.length ≤ Real.sqrt (rho_j j) := by
    intro j t ht
    have h_raw := (buildAt (j : ℕ) j.isLt).2.length_bounds t ht
    have h_out_le : s.e ⟨(j : ℕ), j.isLt⟩ ≤ hierarchyLoss :=
      le_trans (s.e_le_targetLoss ⟨(j : ℕ), j.isLt⟩) s.targetLoss_le_hierarchyLoss
    have h_rho_pos : 0 < rho_j j := by
      rw [h_rho_eq j]
      exact lt_of_lt_of_le hdelta_pos (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).2.1
    have h_rpow_le : Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤
        Real.rpow (rho_j j) (1 / 2 + s.e ⟨(j : ℕ), j.isLt⟩) :=
      Real.rpow_le_rpow_of_exponent_ge h_rho_pos
        (rhoAt hN_pos hdelta_pos hdelta_one j j.isLt).2.2 (by linarith)
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one (j : ℕ) j.isLt).1 = rho_j j :=
      (h_rho_eq j).symm
    rw [h_rho] at h_raw
    exact ⟨h_rpow_le.trans h_raw.1, h_raw.2⟩
  -- Direct properties from data
  have h_height_all : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j, t.height = rho_j j := by
    intro j t ht
    have h_raw := (buildAt (j : ℕ) j.isLt).2.height_eq t ht
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one (j : ℕ) j.isLt).1 = rho_j j :=
      (h_rho_eq j).symm
    rw [h_rho] at h_raw
    exact h_raw
  have h_slope_all : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j, |t.slope| ≤ 2 := by
    intro j t ht
    exact (buildAt (j : ℕ) j.isLt).2.slope_bound t ht
  have h_sep_all : ∀ (j : Fin N), ∀ t ∈ origTrapezoids j, ∀ s ∈ origTrapezoids j,
      t ≠ s → ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (rho_j j) ≤ |z - w| := by
    intro j t ht s hs hne z hz w hw
    have h_raw := (buildAt (j : ℕ) j.isLt).2.separated_cores t ht s hs hne z hz w hw
    have h_rho : (rhoAt hN_pos hdelta_pos hdelta_one (j : ℕ) j.isLt).1 = rho_j j :=
      (h_rho_eq j).symm
    rw [h_rho] at h_raw
    exact h_raw
  have h_nonempty_all : ∀ (j : Fin N), (origTrapezoids j).Nonempty := by
    intro j
    exact (buildAt (j : ℕ) j.isLt).2.trapezoids_nonempty
  let m : ℕ := dataLast.multiplicity
  have hm_pos : 0 < m := dataLast.multiplicity_pos
  have hZ_mult : Z.HasConstantMultiplicity m (2 * m) := by
    have h_fam : sourceLast.family = source0.family := h_family_eq last hlast_lt
    have h_transport : ∀ (F F' : Kakeya.Streamlined.TubeFamily delta) (hF : F = F')
        (Y : Kakeya.Streamlined.TubeShading F) (m M : ℕ),
        Y.HasConstantMultiplicity m M →
        (hF ▸ Y : Kakeya.Streamlined.TubeShading F').HasConstantMultiplicity m M := by
      intro F F' hF Y m M h
      subst hF
      exact h
    exact h_transport sourceLast.family source0.family h_fam dataLast.shading m (2 * m) dataLast.constant_multiplicity
  exact ⟨Z, hZ_sub, hZ_extremal, origTrapezoids, h_nonempty_all, h_height_all,
    h_slope_all, h_length_bounds_all, h_sep_all, h_transfer_approx,
    h_transfer_coverage, m, hm_pos, hZ_mult, trivial⟩

/-! ## Unique parent nesting -/

/--
Prove the unique numerical parent relation between adjacent hierarchy levels.

For each child trapezoid, its active endpoints are covered by the parent level.
By separation and the strict scale decrease, the child core fits inside a unique
parent core.  Slope approximation at the endpoints gives numerical nesting.

The `delta = 1` boundary case is handled separately: all scales equal 1, all
lengths equal 1, and there can be at most one trapezoid per level.
-/
lemma prove_unique_parent
    {N : ℕ} {delta : ℝ} {hierarchyLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : Kakeya.Streamlined.TubeShading F}
    {sourceSlope : ℝ → ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hZ_ball : Z.union ⊆ Metric.closedBall (0 : Point3) 1)
    (trapezoids : Fin N → Finset WZ1VerticalTrapezoid)
    (h_nonempty : ∀ j, (trapezoids j).Nonempty)
    (h_height_eq : ∀ j, ∀ t ∈ trapezoids j,
        t.height = wz1Corollary26Scale delta N j)
    (h_length_bounds : ∀ j, ∀ t ∈ trapezoids j,
        Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
        t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (h_separated : ∀ j, ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
        ∀ z ∈ t.core, ∀ w ∈ s.core,
          Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|)
    (h_coverage : ∀ j, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core)
    (h_slope_approx : ∀ j, ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
        horizontalSlice Z.union z ≠ ∅ →
          |sourceSlope z - t.affine z| ≤ wz1Corollary26Scale delta N j)
    (h_active_endpoints : ∀ j, ∀ t ∈ trapezoids j,
        horizontalSlice Z.union t.left ≠ ∅ ∧
        horizontalSlice Z.union t.right ≠ ∅) :
    ∀ (parentLevel childLevel : Fin N),
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! parent, parent ∈ trapezoids parentLevel ∧
            child.IsNumericallyNestedIn parent := by
  let rho_j (j : Fin N) : ℝ := wz1Corollary26Scale delta N j
  have h_rho_pos : ∀ j, 0 < rho_j j := by
    intro j; exact Real.rpow_pos_of_pos hdelta_pos _
  have h_approx : ∀ j, ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
      horizontalSlice Z.union z ≠ ∅ → |sourceSlope z - t.affine z| ≤ rho_j j := by
    simpa [rho_j] using h_slope_approx
  have h_sep : ∀ j, ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (rho_j j) ≤ |z - w| := by
    simpa [rho_j] using h_separated
  have h_height : ∀ j, ∀ t ∈ trapezoids j, t.height = rho_j j := by
    simpa [rho_j] using h_height_eq
  have h_length : ∀ j, ∀ t ∈ trapezoids j,
      Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
      t.length ≤ Real.sqrt (rho_j j) := by
    simpa [rho_j] using h_length_bounds
  have h_active_ep : ∀ j, ∀ t ∈ trapezoids j,
      horizontalSlice Z.union t.left ≠ ∅ ∧ horizontalSlice Z.union t.right ≠ ∅ :=
    h_active_endpoints
  have h_cov : ∀ j, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core :=
    h_coverage
  intro parentLevel childLevel h_adj child hchild
  by_cases hdelta_lt_one : delta < 1
  · -- delta < 1: scales are strictly decreasing
    have h_child_lt_parent : rho_j childLevel < rho_j parentLevel := by
      have h1 : (parentLevel : ℕ) < (childLevel : ℕ) := by omega
      have h_raw := hierarchyScale_strict_mono hdelta_pos hdelta_lt_one h1 childLevel.isLt
      have h_eq_c := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := childLevel)
      have h_eq_p := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := parentLevel)
      rw [h_eq_c, h_eq_p] at h_raw
      exact h_raw
    have h_rho_parent_pos : 0 < rho_j parentLevel := h_rho_pos parentLevel
    have h_rho_child_pos : 0 < rho_j childLevel := h_rho_pos childLevel
    have h_left_in_Icc : child.left ∈ Set.Icc (-1 : ℝ) 1 :=
      anchored_active_height_in_Icc hZ_ball (h_active_ep childLevel child hchild).1
    have h_right_in_Icc : child.right ∈ Set.Icc (-1 : ℝ) 1 :=
      anchored_active_height_in_Icc hZ_ball (h_active_ep childLevel child hchild).2
    have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
      h_cov parentLevel child.left h_left_in_Icc (h_active_ep childLevel child hchild).1
    have h_right_covered : ∃ p ∈ trapezoids parentLevel, child.right ∈ p.core :=
      h_cov parentLevel child.right h_right_in_Icc (h_active_ep childLevel child hchild).2
    have h_unique_core := unique_parent_core_containment
      h_rho_parent_pos h_rho_child_pos (h_sep parentLevel)
      (h_length childLevel child hchild |>.2) h_child_lt_parent
      h_left_covered h_right_covered
    rcases h_unique_core with ⟨parent, ⟨hp_mem, h_core_sub⟩, h_uniq_core⟩
    have h_child_left_active : horizontalSlice Z.union child.left ≠ ∅ :=
      (h_active_ep childLevel child hchild).1
    have h_child_right_active : horizontalSlice Z.union child.right ≠ ∅ :=
      (h_active_ep childLevel child hchild).2
    have h_child_approx_left := h_approx childLevel child hchild child.left
      (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
    have h_child_approx_right := h_approx childLevel child hchild child.right
      (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
    have h_parent_approx_left := h_approx parentLevel parent hp_mem child.left
      (h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)) h_child_left_active
    have h_parent_approx_right := h_approx parentLevel parent hp_mem child.right
      (h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)) h_child_right_active
    have h_nesting := numerical_nesting_from_endpoint_approximations
      (h_height childLevel child hchild) (h_height parentLevel parent hp_mem)
      h_core_sub h_child_approx_left h_child_approx_right
      h_parent_approx_left h_parent_approx_right
    refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
    intro q hq
    have hq_core_sub : child.core ⊆ q.core := hq.2.1
    exact h_uniq_core q ⟨hq.1, hq_core_sub⟩
  · -- delta = 1: all scales = 1, all lengths = 1, at most one trapezoid per level
    have hdelta_eq : delta = 1 := by linarith
    have h_rho_eq1 : ∀ (j : Fin N), rho_j j = 1 := by
      intro j
      simp [rho_j, wz1Corollary26Scale, hdelta_eq] <;> norm_num
    have h_len1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.length = 1 := by
      intro j t ht
      have hlb := h_length j t ht
      have hr : rho_j j = 1 := h_rho_eq1 j
      rw [hr] at hlb
      have h1 : Real.rpow (1 : ℝ) (1 / 2 + hierarchyLoss) = 1 := by simp
      have h2 : Real.sqrt (1 : ℝ) = 1 := by simp
      rw [h1, h2] at hlb <;> linarith
    have h_cores_in_Icc : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.core ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro j t ht
      have h_left_Icc : t.left ∈ Set.Icc (-1 : ℝ) 1 :=
        anchored_active_height_in_Icc hZ_ball (h_active_ep j t ht).1
      have h_right_Icc : t.right ∈ Set.Icc (-1 : ℝ) 1 :=
        anchored_active_height_in_Icc hZ_ball (h_active_ep j t ht).2
      intro z hz
      have h1 : t.left ≤ z := (Set.mem_Icc.mp hz).1
      have h2 : z ≤ t.right := (Set.mem_Icc.mp hz).2
      exact Set.mem_Icc.mpr ⟨by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).2],
        by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).2]⟩
    have h_sep1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
        ∀ z ∈ t.core, ∀ w ∈ s.core, (1 : ℝ) ≤ |z - w| := by
      intro j t ht s hs hne z hz w hw
      have h := h_sep j t ht s hs hne z hz w hw
      have hr : rho_j j = 1 := h_rho_eq1 j
      rw [hr] at h
      have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
      rw [hsqrt1] at h
      exact h
    have h_at_most_one : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t = s :=
      fun j => at_most_one_trapezoid_delta_one (h_len1 j) (h_sep1 j) (h_cores_in_Icc j)
    rcases h_nonempty parentLevel with ⟨parent, hp_mem⟩
    have h_parent_unique : ∀ q ∈ trapezoids parentLevel, q = parent :=
      fun q hq => h_at_most_one parentLevel q hq parent hp_mem
    have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
      h_cov parentLevel child.left
        (anchored_active_height_in_Icc hZ_ball (h_active_ep childLevel child hchild).1)
        (h_active_ep childLevel child hchild).1
    rcases h_left_covered with ⟨p_left, hp_left_mem, h_left_in⟩
    have hp_left_eq : p_left = parent := h_parent_unique p_left hp_left_mem
    have h_core_sub : child.core ⊆ parent.core := by
      rw [hp_left_eq] at h_left_in
      intro z hz
      have h1 : child.left ≤ z := (Set.mem_Icc.mp hz).1
      have h2 : z ≤ child.right := (Set.mem_Icc.mp hz).2
      have h3 : parent.left ≤ child.left := (Set.mem_Icc.mp h_left_in).1
      have h4 : child.right ≤ parent.right := by
        rcases h_cov parentLevel child.right
          (anchored_active_height_in_Icc hZ_ball (h_active_ep childLevel child hchild).2)
          (h_active_ep childLevel child hchild).2 with ⟨p_right, hp_right_mem, h_right_in⟩
        have hp_right_eq : p_right = parent := h_parent_unique p_right hp_right_mem
        rw [hp_right_eq] at h_right_in
        exact (Set.mem_Icc.mp h_right_in).2
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h_child_left_active : horizontalSlice Z.union child.left ≠ ∅ :=
      (h_active_ep childLevel child hchild).1
    have h_child_right_active : horizontalSlice Z.union child.right ≠ ∅ :=
      (h_active_ep childLevel child hchild).2
    have h_child_approx_left := h_approx childLevel child hchild child.left
      (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
    have h_child_approx_right := h_approx childLevel child hchild child.right
      (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
    have h_parent_approx_left := h_approx parentLevel parent hp_mem child.left
      (h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)) h_child_left_active
    have h_parent_approx_right := h_approx parentLevel parent hp_mem child.right
      (h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)) h_child_right_active
    have h_nesting := numerical_nesting_from_endpoint_approximations
      (h_height childLevel child hchild) (h_height parentLevel parent hp_mem)
      h_core_sub h_child_approx_left h_child_approx_right
      h_parent_approx_left h_parent_approx_right
    refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
    intro q hq
    have hq_mem : q ∈ trapezoids parentLevel := hq.1
    exact h_parent_unique q hq_mem

end Kakeya.Assouad
