module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.FullMetricOverlap
public import MyLeanRepo.RadialBootstrapping.GreedySelection

@[expose] public section

/-!
# Grid Geometry Count Bound

Pure geometric bound: for a subset S_x of the grid tubeFamily r where every
grid line L' satisfies x ∈ tube(2r, L'), the number of lines in S_x within
distance ρ of a given line L is O(ρ/r).
-/

open MeasureTheory Metric Set Finset
open scoped Classical ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

/-- Auxiliary: for a unit vector u, find an angle φ with u = (cos φ, sin φ). -/
lemma angle_of_unit_vector (u : Point) (hu_norm : ‖u‖ = 1) :
    ∃ (φ : ℝ), u 0 = Real.cos φ ∧ u 1 = Real.sin φ := by
  have h2 : ‖u‖ ^ 2 = 1 := by rw [hu_norm] <;> norm_num
  have h1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have h3 : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    linarith
  have h_u0_abs : -1 ≤ u 0 ∧ u 0 ≤ 1 := by
    have h : u 0 ^ 2 ≤ 1 := by nlinarith
    constructor <;> nlinarith
  let φ : ℝ := if 0 ≤ u 1 then Real.arccos (u 0) else -Real.arccos (u 0)
  have hcos : Real.cos φ = u 0 := by
    simp only [φ]
    split_ifs with h
    · rw [Real.cos_arccos] <;> linarith [h_u0_abs]
    · rw [Real.cos_neg, Real.cos_arccos] <;> linarith [h_u0_abs]
  have hsin : Real.sin φ = u 1 := by
    simp only [φ]
    split_ifs with h
    · have h_pos : 0 ≤ u 1 := h
      have h_sin_arccos : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - u 0 ^ 2) :=
        Real.sin_arccos (u 0)
      rw [h_sin_arccos]
      have h2 : u 1 ^ 2 = 1 - u 0 ^ 2 := by nlinarith
      have h3 : Real.sqrt (1 - u 0 ^ 2) = u 1 := by
        have h4 : Real.sqrt (1 - u 0 ^ 2) = Real.sqrt (u 1 ^ 2) := by rw [h2]
        rw [h4, Real.sqrt_sq h_pos]
      exact h3
    · have h_neg : u 1 < 0 := by linarith
      have h_sin_arccos : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - u 0 ^ 2) :=
        Real.sin_arccos (u 0)
      rw [Real.sin_neg, h_sin_arccos]
      have h2 : u 1 ^ 2 = 1 - u 0 ^ 2 := by nlinarith
      have h3 : Real.sqrt (1 - u 0 ^ 2) = -u 1 := by
        have h4 : Real.sqrt (1 - u 0 ^ 2) = Real.sqrt (u 1 ^ 2) := by rw [h2]
        have h5 : Real.sqrt (u 1 ^ 2) = |u 1| := by
          rw [Real.sqrt_sq_eq_abs]
        have h6 : |u 1| = -u 1 := by
          rw [abs_of_neg h_neg]
        rw [h4, h5, h6]
      rw [h3] <;> ring
  exact ⟨φ, hcos.symm, hsin.symm⟩

/-- Direction distance between a grid line and any line L equals
    |cos(θ - φ)| where φ is the direction angle of L. -/
lemma lineDirDist_gridLine_eq_cos (θ a : ℝ) (L : Line2) (φ : ℝ)
    (hcos : L.unitDirection 0 = Real.cos φ)
    (hsin : L.unitDirection 1 = Real.sin φ) :
    lineDirDist (lineOfAngleOffset θ a) L = |Real.cos (θ - φ)| := by
  have h_udir_norm : ‖L.unitDirection‖ = 1 := L.unitDirection_norm
  have h1 : L.unitDirection ∈ L.toAffine.direction := by
    simp [Line2.unitDirection, L.directionVector_mem]
    <;> exact L.toAffine.direction.smul_mem _ L.directionVector_mem
  have h2 : L.unitDirection ≠ 0 := by
    intro h
    have h3 : ‖L.unitDirection‖ = 0 := by rw [h] <;> simp
    rw [h_udir_norm] at h3 <;> norm_num at h3
  have h_span : Submodule.span ℝ {L.unitDirection} = L.toAffine.direction := by
    exact Eq.symm (Line2.direction_eq_span_unit L)
  have h_dir_same : (lineOfAngleOffset θ a).toAffine.direction =
      (lineOfAngleOffset θ 0).toAffine.direction := by
    have h1 : (lineOfAngleOffset θ a).toAffine.direction = Submodule.span ℝ {dirVec θ} :=
      lineOfAngleOffset_aff_direction θ a
    have h2 : (lineOfAngleOffset θ 0).toAffine.direction = Submodule.span ℝ {dirVec θ} :=
      lineOfAngleOffset_aff_direction θ 0
    exact Eq.trans h1 h2.symm
  have h_main : submoduleDirDist (lineOfAngleOffset θ 0).toAffine.direction
        (Submodule.span ℝ {L.unitDirection}) =
      |Real.cos (θ - φ)| :=
    dirDist_lineOfAngle_span θ φ L.unitDirection h_udir_norm hcos hsin
  have h4 : lineDirDist (lineOfAngleOffset θ a) L =
      submoduleDirDist (lineOfAngleOffset θ 0).toAffine.direction (Submodule.span ℝ {L.unitDirection}) := by
    simp only [lineDirDist]
    rw [h_dir_same, h_span]
  rw [h4]
  exact h_main

/-- Pure grid geometry count bound. -/
lemma grid_geometry_count_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (S_x : Finset Line2)
    (hS_sub : S_x ⊆ tubeFamily r)
    (hS_near_x : ∀ L ∈ S_x, x ∈ tube (2 * r) L)
    (L : Line2) (ρ : ℝ) (hρ : r ≤ ρ) (hρ1 : ρ ≤ 1) :
    (S_x.filter (fun L' => L' ∈ Metric.ball L ρ)).card ≤
      (1230 * Real.pi + 369) * ρ / r := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  set nθ : ℕ := numAngles r with hnθ
  have h_nθ_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]; apply Nat.ceil_pos.mpr
    exact div_pos Real.pi_pos hΔ_pos

  -- Get direction angle φ of L
  have h_udir_norm : ‖L.unitDirection‖ = 1 := L.unitDirection_norm
  rcases angle_of_unit_vector L.unitDirection h_udir_norm with ⟨φ, hcos, hsin⟩

  -- Define θ0 = φ + π/2 reduced to [0, π)
  let θ0_raw : ℝ := φ + Real.pi / 2
  let nπ : ℤ := Int.floor (θ0_raw / Real.pi)
  let θ0 : ℝ := θ0_raw - (nπ : ℝ) * Real.pi
  have hθ0_nonneg : 0 ≤ θ0 := by
    have h : (nπ : ℝ) ≤ θ0_raw / Real.pi := Int.floor_le _
    have h2 : (nπ : ℝ) * Real.pi ≤ θ0_raw := by
      calc (nπ : ℝ) * Real.pi
        ≤ (θ0_raw / Real.pi) * Real.pi := by gcongr
      _ = θ0_raw := by field_simp [Real.pi_pos.ne'] <;> ring
    linarith [show θ0 = θ0_raw - (nπ : ℝ) * Real.pi from rfl]
  have hθ0_lt_pi : θ0 < Real.pi := by
    have h : θ0_raw / Real.pi < (nπ : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 : θ0_raw < ((nπ : ℝ) + 1) * Real.pi := by
      calc θ0_raw
        = (θ0_raw / Real.pi) * Real.pi := by field_simp [Real.pi_pos.ne'] <;> ring
      _ < ((nπ : ℝ) + 1) * Real.pi := by gcongr
    linarith [show θ0 = θ0_raw - (nπ : ℝ) * Real.pi from rfl]

  have h_sin_eq : ∀ (θ : ℝ), |Real.sin (θ - θ0)| = |Real.cos (θ - φ)| := by
    intro θ
    have h5 : θ - θ0 = θ - φ - Real.pi / 2 + (nπ : ℝ) * Real.pi := by
      simp [θ0] <;> ring
    rw [h5]
    have h6 : Real.sin (θ - φ - Real.pi / 2 + (nπ : ℝ) * Real.pi) =
        (-1 : ℝ) ^ (nπ : ℤ) * Real.sin (θ - φ - Real.pi / 2) := by
      rw [Real.sin_add_int_mul_pi]
    rw [h6]
    have h7 : |(-1 : ℝ) ^ (nπ : ℤ)| = 1 := by rw [abs_zpow] <;> norm_num
    have h8 : Real.sin (θ - φ - Real.pi / 2) = -Real.cos (θ - φ) := by
      rw [Real.sin_sub] <;> simp [Real.cos_pi_div_two, Real.sin_pi_div_two] <;> ring
    rw [h8, abs_mul, h7, one_mul, abs_neg]

  -- Define valid angles
  let valid_angles : Finset ℕ :=
    (angleSet r).filter (fun k => |Real.sin (angleVal r k - θ0)| < ρ)

  have hρ_nonneg : 0 ≤ ρ := by linarith
  have hρ_le_one : ρ ≤ 1 := hρ1
  have hρ_ge_neg_one : -1 ≤ ρ := by linarith
  let α : ℝ := Real.arcsin ρ
  have hα_nonneg : 0 ≤ α := Real.arcsin_nonneg.mpr hρ_nonneg
  have hα_le : α ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two ρ
  have h_sinα : Real.sin α = ρ := Real.sin_arcsin hρ_ge_neg_one hρ_le_one
  have hL_angle : 2 * α ≤ Real.pi * ρ := by
    have h1 : α ≤ (Real.pi / 2) * ρ := arcsin_le_pi_div_two_mul (h0 := hρ_nonneg) (h1 := hρ_le_one)
    have h2 : 2 * α ≤ 2 * ((Real.pi / 2) * ρ) := by gcongr
    have h3 : 2 * ((Real.pi / 2) * ρ) = Real.pi * ρ := by ring
    linarith

  have h_exists : ∀ (k : ℕ), k ∈ valid_angles →
      ∃ (m : ℤ), |angleVal r k - θ0 - (m : ℝ) * Real.pi| < α := by
    intro k hk
    have h : |Real.sin (angleVal r k - θ0)| < ρ := (Finset.mem_filter.mp hk).2
    exact sin_lt_implies_near_multiple_pi (angleVal r k - θ0) ρ hρ_nonneg hρ_le_one h

  have h_exists_total : ∀ (k : ℕ), ∃ (m : ℤ), k ∈ valid_angles →
      |angleVal r k - θ0 - (m : ℝ) * Real.pi| < α := by
    intro k
    by_cases hk : k ∈ valid_angles
    · rcases h_exists k hk with ⟨m, hm⟩
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => False.elim (hk h)⟩
  choose m hm using h_exists_total

  have h_m_range : ∀ k ∈ valid_angles, m k ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro k hk
    have h_k2 : k ∈ angleSet r := (Finset.mem_filter.mp hk).1
    have h_k3 : k < nθ := by
      simp only [angleSet] at h_k2 <;> exact Finset.mem_range.mp h_k2
    have h_k_pos : 0 < (nθ : ℝ) := by exact_mod_cast h_nθ_pos
    have h_ang_nonneg : 0 ≤ angleVal r k := by
      have h : angleVal r k = (k : ℝ) * Real.pi / (nθ : ℝ) := by simp [angleVal] <;> ring
      rw [h]; positivity
    have h_ang_lt : angleVal r k < Real.pi := by
      have h : angleVal r k = (k : ℝ) * Real.pi / (nθ : ℝ) := by simp [angleVal] <;> ring
      rw [h]
      have h4 : (k : ℝ) < (nθ : ℝ) := by exact_mod_cast h_k3
      have h5 : (k : ℝ) * Real.pi < (nθ : ℝ) * Real.pi := mul_lt_mul_of_pos_right h4 Real.pi_pos
      calc (k : ℝ) * Real.pi / (nθ : ℝ)
        < ((nθ : ℝ) * Real.pi) / (nθ : ℝ) := by gcongr
      _ = Real.pi := by field_simp [h_k_pos.ne'] <;> ring
    have h_t1 : -Real.pi < angleVal r k - θ0 := by linarith [hθ0_lt_pi]
    have h_t2 : angleVal r k - θ0 < Real.pi := by linarith [hθ0_nonneg]
    have h_m1 : |angleVal r k - θ0 - (m k : ℝ) * Real.pi| < α := hm k hk
    have h_m4 : (m k : ℝ) * Real.pi - α < angleVal r k - θ0 := by linarith [abs_lt.mp h_m1]
    have h_m5 : angleVal r k - θ0 < (m k : ℝ) * Real.pi + α := by linarith [abs_lt.mp h_m1]
    have h_m6 : (m k : ℝ) * Real.pi < Real.pi + α := by linarith
    have h_m7 : -Real.pi - α < (m k : ℝ) * Real.pi := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have h_m8 : (m k : ℝ) < 1 + α / Real.pi := by
      have h : (m k : ℝ) * Real.pi < Real.pi + α := h_m6
      calc (m k : ℝ)
        = ((m k : ℝ) * Real.pi) / Real.pi := by field_simp [hpi.ne'] <;> ring
      _ < (Real.pi + α) / Real.pi := by gcongr
      _ = 1 + α / Real.pi := by field_simp [hpi.ne'] <;> ring
    have h_m9 : -1 - α / Real.pi < (m k : ℝ) := by
      have h : -Real.pi - α < (m k : ℝ) * Real.pi := h_m7
      calc -1 - α / Real.pi
        = (-Real.pi - α) / Real.pi := by field_simp [hpi.ne'] <;> ring
      _ < ((m k : ℝ) * Real.pi) / Real.pi := by gcongr
      _ = (m k : ℝ) := by field_simp [hpi.ne'] <;> ring
    have hα2 : α / Real.pi ≤ 1 / 2 := by
      have h : α ≤ Real.pi / 2 := hα_le
      have hpi : 0 < Real.pi := Real.pi_pos
      calc α / Real.pi
        ≤ (Real.pi / 2) / Real.pi := by gcongr
      _ = 1 / 2 := by field_simp [hpi.ne'] <;> ring
    have h_m10 : (m k : ℝ) < 3 / 2 := by linarith [h_m8, hα2]
    have h_m11 : -3 / 2 < (m k : ℝ) := by linarith [h_m9, hα2]
    have h_m12 : m k = -1 ∨ m k = 0 ∨ m k = 1 :=
      int_in_short_interval (m k) h_m11 h_m10
    rcases h_m12 with (h13 | h13 | h13)
    · have h14 : (-1 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14
    · have h14 : (0 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14
    · have h14 : (1 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14

  let F (mval : ℤ) : Finset ℕ := valid_angles.filter (fun k => m k = mval)
  have h_per_m : ∀ (mval : ℤ), mval ∈ ({-1, 0, 1} : Finset ℤ) →
      ((F mval).card : ℝ) ≤ (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1 := by
    intro mval _
    let S_m := F mval
    have h1 : ∀ k ∈ S_m, angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α) := by
      intro k hk
      have h2 : k ∈ valid_angles := (Finset.mem_filter.mp hk).1
      have h3 : m k = mval := (Finset.mem_filter.mp hk).2
      have h4 : |angleVal r k - θ0 - (m k : ℝ) * Real.pi| < α := hm k h2
      rw [h3] at h4
      have h4' : -α < angleVal r k - θ0 - (mval : ℝ) * Real.pi ∧
          angleVal r k - θ0 - (mval : ℝ) * Real.pi < α := abs_lt.mp h4
      simp only [Set.mem_Ioo]
      constructor <;> linarith [h4'.1, h4'.2]
    have h2 : S_m ⊆ (angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α)) := by
      intro k hk
      have h3 : k ∈ valid_angles := (Finset.mem_filter.mp hk).1
      have h4 : k ∈ angleSet r := (Finset.mem_filter.mp h3).1
      exact Finset.mem_filter.mpr ⟨h4, h1 k hk⟩
    have h3 : S_m.card ≤ ((angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α))).card :=
      Finset.card_le_card h2
    have h4 : ((angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α))).card ≤
        Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) + 1 :=
      angle_grid_count_le r hr (2 * α) (by positivity) ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α) (by linarith)
    have h5 : S_m.card ≤ Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) + 1 :=
      le_trans h3 h4
    exact_mod_cast h5

  have h_partition : valid_angles ⊆ Finset.biUnion ({-1, 0, 1} : Finset ℤ) F := by
    intro k hk
    have h5 : m k ∈ ({-1, 0, 1} : Finset ℤ) := h_m_range k hk
    exact Finset.mem_biUnion.mpr ⟨m k, h5, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  have h_angle_card : valid_angles.card ≤ ∑ mval ∈ ({-1, 0, 1} : Finset ℤ), (F mval).card := by
    have h5 : valid_angles.card ≤ (Finset.biUnion ({-1, 0, 1} : Finset ℤ) F).card :=
      Finset.card_le_card h_partition
    have h_disj : ∀ m1 m2 : ℤ, m1 ≠ m2 → Disjoint (F m1) (F m2) := by
      intro m1 m2 hne
      rw [Finset.disjoint_left]
      intro k hk1
      have h_eq1 : m k = m1 := (Finset.mem_filter.mp hk1).2
      intro hk2
      have h_eq2 : m k = m2 := (Finset.mem_filter.mp hk2).2
      have h_cont : m1 = m2 := by rw [← h_eq1, h_eq2]
      exact hne h_cont
    have h6 : (Finset.biUnion ({-1, 0, 1} : Finset ℤ) F).card =
        ∑ mval ∈ ({-1, 0, 1} : Finset ℤ), (F mval).card := by
      rw [Finset.card_biUnion (fun i _ j _ hne => h_disj i j hne)]
    rw [h6] at h5
    exact h5

  have h_angle_count : (valid_angles.card : ℝ) ≤
      3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) :=
    angle_count_lemma nθ α valid_angles F h_per_m h_angle_card

  -- Bound ceil term
  have h_nθ_bound : (nθ : ℝ) ≤ Real.pi / Δ + 1 := by
    dsimp only [nθ, numAngles]
    have h : (Nat.ceil (Real.pi / Δ) : ℝ) ≤ Real.pi / Δ + 1 := by
      have h' : (Nat.ceil (Real.pi / Δ) : ℝ) < Real.pi / Δ + 1 := nat_ceil_lt_add_one (Real.pi / Δ) (by positivity)
      linarith
    exact h
  have h_ceil_bound : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) ≤ 10 * Real.pi * ρ / r + 2 := by
    have h1 : (2 * α) * (nθ : ℝ) / Real.pi ≤ ρ * (nθ : ℝ) := by
      have h2 : 2 * α ≤ Real.pi * ρ := hL_angle
      have h3 : 0 < Real.pi := Real.pi_pos
      calc (2 * α) * (nθ : ℝ) / Real.pi
        ≤ (Real.pi * ρ) * (nθ : ℝ) / Real.pi := by gcongr
      _ = ρ * (nθ : ℝ) := by field_simp [h3.ne'] <;> ring
    have h4 : ρ * (nθ : ℝ) ≤ ρ * (Real.pi / Δ + 1) := by gcongr
    have h5 : Δ = r / 10 := by dsimp only [Δ, delta] <;> ring
    have h6 : ρ * (Real.pi / Δ + 1) = 10 * Real.pi * ρ / r + ρ := by
      rw [h5] <;> field_simp [hr.ne'] <;> ring
    have h7 : (2 * α) * (nθ : ℝ) / Real.pi ≤ 10 * Real.pi * ρ / r + ρ := by linarith
    have h8 : 10 * Real.pi * ρ / r + ρ ≤ 10 * Real.pi * ρ / r + 1 := by
      have h9 : ρ ≤ 1 := hρ1
      linarith
    have hα_pos : 0 < α := by
      have hρ_pos : 0 < ρ := by linarith
      exact Real.arcsin_pos.mpr hρ_pos
    have h_pos_arg : 0 < (2 * α) * (nθ : ℝ) / Real.pi := by positivity
    have h9 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) ≤ (2 * α) * (nθ : ℝ) / Real.pi + 1 := by
      have h10 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) < (2 * α) * (nθ : ℝ) / Real.pi + 1 :=
        nat_ceil_lt_add_one ((2 * α) * (nθ : ℝ) / Real.pi) h_pos_arg
      linarith
    have h10 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) ≤ 10 * Real.pi * ρ / r + 2 := by
      have h11 : (2 * α) * (nθ : ℝ) / Real.pi ≤ 10 * Real.pi * ρ / r + 1 := by
        calc (2 * α) * (nθ : ℝ) / Real.pi
          ≤ 10 * Real.pi * ρ / r + ρ := h7
        _ ≤ 10 * Real.pi * ρ / r + 1 := by
          have h12 : ρ ≤ 1 := hρ1
          linarith
      calc (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ)
        ≤ (2 * α) * (nθ : ℝ) / Real.pi + 1 := h9
      _ ≤ (10 * Real.pi * ρ / r + 1) + 1 := by gcongr
      _ = 10 * Real.pi * ρ / r + 2 := by ring
    exact h10

  have h_valid_angles_bound : (valid_angles.card : ℝ) ≤ 30 * Real.pi * ρ / r + 9 := by
    calc (valid_angles.card : ℝ)
      ≤ 3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) := h_angle_count
    _ ≤ 3 * ((10 * Real.pi * ρ / r + 2) + 1) := by gcongr
    _ = 30 * Real.pi * ρ / r + 9 := by ring

  -- Define preimage
  let S_filtered : Finset Line2 := S_x.filter (fun L' => L' ∈ Metric.ball L ρ)
  let preimage : Finset (ℕ × ℕ) :=
    (angleSet r ×ˢ offsetSet r).filter (fun ⟨k, j⟩ =>
      let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
      L' ∈ S_filtered)

  have h_surj : S_filtered ⊆ preimage.image (fun ⟨k, j⟩ => lineOfAngleOffset (angleVal r k) (offsetVal r j)) := by
    intro L' hL'
    have h1 : L' ∈ S_x := (Finset.mem_filter.mp hL').1
    have h2 : L' ∈ tubeFamily r := hS_sub h1
    rcases Finset.mem_image.mp h2 with ⟨⟨k, j⟩, hkj, rfl⟩
    have h3 : (k, j) ∈ preimage := by
      simp only [preimage, Finset.mem_filter, Finset.mem_product] at * <;> tauto
    exact Finset.mem_image.mpr ⟨(k, j), h3, rfl⟩

  have h_card_le : S_filtered.card ≤ preimage.card := by
    have h : S_filtered.card ≤ (preimage.image (fun ⟨k, j⟩ => lineOfAngleOffset (angleVal r k) (offsetVal r j))).card :=
      Finset.card_le_card h_surj
    have h_img : (preimage.image (fun ⟨k, j⟩ => lineOfAngleOffset (angleVal r k) (offsetVal r j))).card ≤ preimage.card :=
      Finset.card_image_le
    exact le_trans h h_img

  -- For each k, bound offsets by 41
  have h_offset_bound : ∀ (k : ℕ), k ∈ valid_angles →
      ((offsetSet r).filter (fun j =>
        let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
        L' ∈ S_filtered)).card ≤ 41 := by
    intro k hk
    let a0 : ℝ := dot x (normalVec (angleVal r k))
    let S_off := (offsetSet r).filter (fun j =>
        let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
        L' ∈ S_filtered)
    have h1 : ∀ j ∈ S_off, |offsetVal r j - a0| < 2 * r := by
      intro j hj
      have h2 : (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∈ S_filtered :=
        (Finset.mem_filter.mp hj).2
      have h3 : (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∈ S_x :=
        (Finset.mem_filter.mp h2).1
      have h4 : x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) :=
        hS_near_x _ h3
      have h5 : |dot x (normalVec (angleVal r k)) - offsetVal r j| < 2 * r :=
        (grid_tube_member (angleVal r k) (offsetVal r j) r hr x).mp h4
      have h6 : |offsetVal r j - a0| = |dot x (normalVec (angleVal r k)) - offsetVal r j| := by
        rw [show a0 = dot x (normalVec (angleVal r k)) from rfl, abs_sub_comm]
      rw [h6]
      exact h5
    have h_sub : S_off ⊆ (offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, h1 j hj⟩
    have h6 : S_off.card ≤ ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card :=
      Finset.card_le_card h_sub
    have h7 : ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card ≤ 41 :=
      offset_packing_bound r hr a0
    exact le_trans h6 h7

  -- Group preimage by first coordinate
  have h_preimage_bound : preimage.card ≤ valid_angles.card * 41 := by
    let images (k : ℕ) : Finset (ℕ × ℕ) :=
      ((offsetSet r).filter (fun j =>
        let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
        L' ∈ S_filtered)).image (fun j => (k, j))
    have h1 : preimage ⊆ Finset.biUnion valid_angles images := by
      intro ⟨k, j⟩ hkj
      have h_pair_in : (k, j) ∈ angleSet r ×ˢ offsetSet r := (Finset.mem_filter.mp hkj).1
      have h_k_in : k ∈ angleSet r := (Finset.mem_product.mp h_pair_in).1
      have h_j_in : j ∈ offsetSet r := (Finset.mem_product.mp h_pair_in).2
      let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
      have hL'_in : L' ∈ S_filtered := (Finset.mem_filter.mp hkj).2
      have h_dist : dist L' L < ρ := (Finset.mem_filter.mp hL'_in).2
      have h_dir : lineDirDist L' L < ρ := by
        have h : lineDirDist L' L ≤ dist L' L := by
          have h' : dist L' L = lineDirDist L' L + lineOffsetDist L' L := by rfl
          have h'' : 0 ≤ lineOffsetDist L' L := dist_nonneg
          linarith
        linarith
      have h_eq : lineDirDist L' L = |Real.cos (angleVal r k - φ)| :=
        lineDirDist_gridLine_eq_cos (angleVal r k) (offsetVal r j) L φ hcos hsin
      rw [h_eq] at h_dir
      have h_sin : |Real.sin (angleVal r k - θ0)| < ρ := by
        rw [h_sin_eq (angleVal r k)] <;> exact h_dir
      have h_k_valid : k ∈ valid_angles := by
        simp only [valid_angles, Finset.mem_filter] <;> exact ⟨h_k_in, h_sin⟩
      have h_j_filter : j ∈ (offsetSet r).filter (fun j =>
          let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
          L' ∈ S_filtered) := by
        simp only [Finset.mem_filter] <;> exact ⟨h_j_in, hL'_in⟩
      exact Finset.mem_biUnion.mpr ⟨k, h_k_valid, Finset.mem_image.mpr ⟨j, h_j_filter, rfl⟩⟩
    have h2 : preimage.card ≤ (Finset.biUnion valid_angles images).card :=
      Finset.card_le_card h1
    have h_disj_images : ∀ (k1 k2 : ℕ), k1 ≠ k2 → Disjoint (images k1) (images k2) := by
      intro k1 k2 hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨j2, _, h_eq⟩
      simp [hne] at h_eq <;> tauto
    have h3 : (Finset.biUnion valid_angles images).card ≤ ∑ k ∈ valid_angles, (images k).card := by
      have h_disj' : Set.PairwiseDisjoint (valid_angles : Set ℕ) images := by
        intro k1 _ k2 _ hne
        exact h_disj_images k1 k2 hne
      rw [Finset.card_biUnion h_disj']
      <;> rfl
    have h4 : ∑ k ∈ valid_angles, (images k).card ≤ ∑ k ∈ valid_angles, (41 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      have h5 : (images k).card ≤ ((offsetSet r).filter (fun j =>
          let L' := lineOfAngleOffset (angleVal r k) (offsetVal r j)
          L' ∈ S_filtered)).card := Finset.card_image_le
      exact le_trans h5 (h_offset_bound k hk)
    have h5 : ∑ k ∈ valid_angles, (41 : ℕ) = valid_angles.card * 41 := by
      rw [Finset.sum_const] <;> ring
    rw [h5] at h4
    exact le_trans h2 (le_trans h3 h4)

  have h_final : (S_filtered.card : ℝ) ≤ (valid_angles.card : ℝ) * 41 := by
    exact_mod_cast le_trans h_card_le h_preimage_bound

  have h_main : (S_filtered.card : ℝ) ≤ (1230 * Real.pi + 369) * ρ / r := by
    calc (S_filtered.card : ℝ)
      ≤ (valid_angles.card : ℝ) * 41 := h_final
    _ ≤ (30 * Real.pi * ρ / r + 9) * 41 := by gcongr
    _ = 1230 * Real.pi * ρ / r + 369 := by ring
    _ ≤ (1230 * Real.pi + 369) * ρ / r := by
      have h6 : 0 ≤ ρ / r := by positivity
      have h7 : 1 ≤ ρ / r := by
        have h71 : r ≤ ρ := hρ
        have h72 : 0 < r := hr
        exact (one_le_div h72).mpr h71
      have h8 : 369 * (1 : ℝ) ≤ 369 * (ρ / r) := by
        gcongr
      have h10 : 1 ≤ ρ / r := by
        have h11 : 0 < r := hr
        have h12 : r ≤ ρ := hρ
        exact (one_le_div h11).mpr h12
      have h13 : 369 ≤ 369 * (ρ / r) := by
        have h14 : 0 ≤ ρ / r := by positivity
        nlinarith
      have h9 : 1230 * Real.pi * ρ / r + 369 ≤ (1230 * Real.pi + 369) * ρ / r := by
        have h15 : 1230 * Real.pi * ρ / r + 369 ≤ 1230 * Real.pi * ρ / r + 369 * (ρ / r) := by
          gcongr
        have h16 : 1230 * Real.pi * ρ / r + 369 * (ρ / r) = (1230 * Real.pi + 369) * ρ / r := by ring
        linarith
      exact h9
  exact_mod_cast h_main

end RadialBootstrapping
