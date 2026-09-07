module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.FullMetricOverlap

@[expose] public section

set_option maxHeartbeats 500000

/-!
# Generalized tube family overlap bound

Removes the B(0,1) requirement from `tubeFamily_overlap_bound` by adding
the hypothesis `ξ ≤ 1`, which is always satisfied in our application
(ξ = r^κ / 4 < 1/4).

The original proof uses B(0,1) only to show `ξ' ≤ 2`, which absorbs the
`+6` ceiling constant as `12/ξ'`. With `ξ ≤ 1`, we instead absorb it as
`6/ξ`, yielding the tighter constant `(120π + 18)/ξ` for angle count.
-/

open Metric Set Finset
open scoped Classical

noncomputable section

namespace RadialBootstrapping

/-- Generalized overlap bound: works for arbitrary x,y, requiring only ξ ≤ 1. -/
lemma tubeFamily_overlap_bound_general (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ_le_one : ξ ≤ 1) (h_small : 4 * r / ξ ≤ 1)
    (x y : Point) (hxy : ξ ≤ dist x y) :
    (((tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card : ℝ) ≤
      20000 / ξ := by
  set ξ' : ℝ := dist x y with hξ'_def
  have hξ'_pos : 0 < ξ' := by have h : 0 < ξ := hξ; linarith [hxy]
  have hξ'_le : ξ ≤ ξ' := hxy
  have h_small' : 4 * r / ξ' ≤ 1 := by
    have h : 4 * r / ξ' ≤ 4 * r / ξ := by gcongr <;> linarith
    exact h.trans h_small
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  set nθ : ℕ := numAngles r with hnθ
  have h_nθ_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]; apply Nat.ceil_pos.mpr
    exact div_pos Real.pi_pos hΔ_pos

  -- Find φ such that u = (x-y)/ξ' = (cos φ, sin φ)
  let v : Point := x - y
  have hnorm_v : ‖v‖ = ξ' := by simp [v, hξ'_def, dist_eq_norm]
  let u : Point := (1 / ξ') • v
  have hu_norm : ‖u‖ = 1 := by
    have h : ‖u‖ = |1 / ξ'| * ‖v‖ := by simpa [u, norm_smul] using rfl
    rw [h, abs_of_pos (by positivity), hnorm_v]
    <;> field_simp [hξ'_pos.ne'] <;> ring
  have h_norm2 : ‖u‖ ^ 2 = ∑ i : Fin 2, (u i)^2 := EuclideanSpace.real_norm_sq_eq u
  have h_sum : (∑ i : Fin 2, (u i)^2) = u 0 ^ 2 + u 1 ^ 2 := by
    simp [Fin.sum_univ_two] <;> ring
  have hu1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have h : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by rw [h_norm2, h_sum]
    have h2 : ‖u‖ ^ 2 = 1 := by rw [hu_norm] <;> norm_num
    linarith [h, h2]
  have h_u0_abs : -1 ≤ u 0 ∧ u 0 ≤ 1 := by
    have h : u 0 ^ 2 ≤ 1 := by nlinarith
    constructor <;> nlinarith
  let φ : ℝ := if 0 ≤ u 1 then Real.arccos (u 0) else -Real.arccos (u 0)
  have hcos : Real.cos φ = u 0 := by
    simp only [φ]; split_ifs with h
    · rw [Real.cos_arccos] <;> linarith [h_u0_abs]
    · rw [Real.cos_neg, Real.cos_arccos] <;> linarith [h_u0_abs]
  have hsin : Real.sin φ = u 1 := by
    simp only [φ]; split_ifs with h
    · have h_pos : 0 ≤ u 1 := h
      have h_sin_arccos : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - u 0 ^ 2) := Real.sin_arccos (u 0)
      rw [h_sin_arccos]
      have h2 : u 1 ^ 2 = 1 - u 0 ^ 2 := by nlinarith
      have h3 : Real.sqrt (1 - u 0 ^ 2) = u 1 := by
        have h4 : Real.sqrt (1 - u 0 ^ 2) = Real.sqrt (u 1 ^ 2) := by rw [h2]
        rw [h4, Real.sqrt_sq h_pos]
      rw [h3]
    · have h_neg : u 1 < 0 := by linarith
      rw [Real.sin_neg]
      have h_sin_arccos : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - u 0 ^ 2) := Real.sin_arccos (u 0)
      rw [h_sin_arccos]
      have h2 : u 1 ^ 2 = 1 - u 0 ^ 2 := by nlinarith
      have h3 : Real.sqrt (1 - u 0 ^ 2) = -u 1 := by
        have h41 : 0 ≤ -u 1 := by linarith
        have h4 : Real.sqrt (1 - u 0 ^ 2) = Real.sqrt ((-u 1) ^ 2) := by
          have h5 : 1 - u 0 ^ 2 = (-u 1) ^ 2 := by nlinarith
          rw [h5]
        rw [h4, Real.sqrt_sq h41]
      rw [h3] <;> ring

  let c : ℝ := 4 * r / ξ'
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le_one : c ≤ 1 := h_small'
  let α : ℝ := Real.arcsin c
  have hα_nonneg : 0 ≤ α := Real.arcsin_nonneg.mpr hc_nonneg
  have hα_le : α ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two c
  have h_sinα : Real.sin α = c := Real.sin_arcsin (by linarith) hc_le_one
  have hL_angle : 2 * α ≤ 4 * Real.pi * r / ξ' := by
    have h1 : α ≤ (Real.pi / 2) * c := arcsin_le_pi_div_two_mul c hc_nonneg hc_le_one
    have h2 : 2 * α ≤ 2 * ((Real.pi / 2) * c) := by gcongr
    have h3 : 2 * ((Real.pi / 2) * c) = Real.pi * c := by ring
    have h4 : Real.pi * c = 4 * Real.pi * r / ξ' := by dsimp only [c] <;> ring
    linarith

  -- θ0 in [0, π), congruent to φ + π/2 mod π
  let θ0_raw : ℝ := φ + Real.pi / 2
  let nπ : ℤ := Int.floor (θ0_raw / Real.pi)
  let θ0 : ℝ := θ0_raw - (nπ : ℝ) * Real.pi
  have hθ0_nonneg : 0 ≤ θ0 := by
    have h : (nπ : ℝ) ≤ θ0_raw / Real.pi := Int.floor_le (θ0_raw / Real.pi)
    have h2 : (nπ : ℝ) * Real.pi ≤ θ0_raw := by
      calc (nπ : ℝ) * Real.pi
        ≤ (θ0_raw / Real.pi) * Real.pi := by gcongr
      _ = θ0_raw := by field_simp [Real.pi_pos.ne'] <;> ring
    linarith [show θ0 = θ0_raw - (nπ : ℝ) * Real.pi from rfl]
  have hθ0_lt_pi : θ0 < Real.pi := by
    have h : θ0_raw / Real.pi < (nπ : ℝ) + 1 := Int.lt_floor_add_one (θ0_raw / Real.pi)
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
    have h7 : |(-1 : ℝ) ^ (nπ : ℤ)| = 1 := by
      rw [abs_zpow] <;> norm_num
    have h8 : Real.sin (θ - φ - Real.pi / 2) = -Real.cos (θ - φ) := by
      rw [Real.sin_sub]
      <;> simp [Real.cos_pi_div_two, Real.sin_pi_div_two] <;> ring
    rw [h8, abs_mul, h7, one_mul, abs_neg]

  -- Valid angles: |sin(angleVal r k - θ0)| < c
  let valid_angles : Finset ℕ := (angleSet r).filter (fun k => |Real.sin (angleVal r k - θ0)| < c)

  -- For each valid angle, find m : ℤ with |angleVal r k - θ0 - m*π| < α
  have h_exists : ∀ (k : ℕ), k ∈ valid_angles →
      ∃ (m : ℤ), |angleVal r k - θ0 - (m : ℝ) * Real.pi| < α := by
    intro k hk
    have h : |Real.sin (angleVal r k - θ0)| < c := (Finset.mem_filter.mp hk).2
    exact sin_lt_implies_near_multiple_pi (angleVal r k - θ0) c hc_nonneg hc_le_one h
  have h_exists_total : ∀ (k : ℕ), ∃ (m : ℤ), k ∈ valid_angles →
      |angleVal r k - θ0 - (m : ℝ) * Real.pi| < α := by
    intro k
    by_cases hk : k ∈ valid_angles
    · rcases h_exists k hk with ⟨m, hm⟩
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => False.elim (hk h)⟩
  choose m hm using h_exists_total

  -- m ∈ {-1, 0, 1} because angleVal r k - θ0 ∈ (-π, π) and α ≤ π/2
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
    have h_m10 : (m k : ℝ) < 3 / 2 := by
      have hα2 : α / Real.pi ≤ 1 / 2 := by
        have h : α ≤ Real.pi / 2 := hα_le
        have hpi : 0 < Real.pi := Real.pi_pos
        calc α / Real.pi
          ≤ (Real.pi / 2) / Real.pi := by gcongr
        _ = 1 / 2 := by field_simp [hpi.ne'] <;> ring
      linarith [h_m8, hα2]
    have h_m11 : -3 / 2 < (m k : ℝ) := by
      have hα2 : α / Real.pi ≤ 1 / 2 := by
        have h : α ≤ Real.pi / 2 := hα_le
        have hpi : 0 < Real.pi := Real.pi_pos
        calc α / Real.pi
          ≤ (Real.pi / 2) / Real.pi := by gcongr
        _ = 1 / 2 := by field_simp [hpi.ne'] <;> ring
      linarith [h_m9, hα2]
    have h_m12 : m k = -1 ∨ m k = 0 ∨ m k = 1 :=
      int_in_short_interval (m k) h_m11 h_m10
    rcases h_m12 with (h13 | h13 | h13)
    · have h14 : (-1 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14
    · have h14 : (0 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14
    · have h14 : (1 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14

  -- Per-m angle count using angle_grid_count_le
  have h2α_pos : 0 ≤ 2 * α := by positivity
  have h_per_m : ∀ (mval : ℤ), mval ∈ ({-1, 0, 1} : Finset ℤ) →
      ((valid_angles.filter (fun k => m k = mval)).card : ℝ) ≤
        (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1 := by
    intro mval _
    let S_m := valid_angles.filter (fun k => m k = mval)
    have h1 : ∀ k ∈ S_m, angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α) := by
      intro k hk
      have h2 : k ∈ valid_angles := (Finset.mem_filter.mp hk).1
      have h3 : m k = mval := (Finset.mem_filter.mp hk).2
      have h4 : |angleVal r k - θ0 - (m k : ℝ) * Real.pi| < α := hm k h2
      rw [h3] at h4
      have h4' : -α < angleVal r k - θ0 - (mval : ℝ) * Real.pi ∧
          angleVal r k - θ0 - (mval : ℝ) * Real.pi < α := abs_lt.mp h4
      simp only [Set.mem_Ioo]
      constructor
      · linarith [h4'.1]
      · linarith [h4'.2]
    have h2 : S_m ⊆ (angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α)) := by
      intro k hk
      have h3 : k ∈ valid_angles := (Finset.mem_filter.mp hk).1
      have h4 : k ∈ angleSet r := (Finset.mem_filter.mp h3).1
      exact Finset.mem_filter.mpr ⟨h4, h1 k hk⟩
    have h3 : S_m.card ≤ ((angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α))).card :=
      Finset.card_le_card h2
    have h4 : ((angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α))).card ≤
        Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) + 1 :=
      angle_grid_count_le r hr (2 * α) h2α_pos ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α) (by linarith)
    have h5 : S_m.card ≤ Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) + 1 :=
      le_trans h3 h4
    exact_mod_cast h5

  -- Total angle count via partition by m
  let M_finset : Finset ℤ := ({-1, 0, 1} : Finset ℤ)
  have h_partition : valid_angles ⊆ Finset.biUnion M_finset (fun mval => valid_angles.filter (fun k => m k = mval)) := by
    intro k hk
    have h5 : m k ∈ M_finset := h_m_range k hk
    exact Finset.mem_biUnion.mpr ⟨m k, h5, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  have h_disj : ∀ m1 m2 : ℤ, m1 ≠ m2 → Disjoint (valid_angles.filter (fun k => m k = m1)) (valid_angles.filter (fun k => m k = m2)) := by
    intro m1 m2 hne
    rw [Finset.disjoint_left]
    intro k hk1
    have h_eq1 : m k = m1 := (Finset.mem_filter.mp hk1).2
    intro hk2
    have h_eq2 : m k = m2 := (Finset.mem_filter.mp hk2).2
    have h_cont : m1 = m2 := by rw [← h_eq1, h_eq2]
    exact hne h_cont
  have h_angle_card : valid_angles.card ≤ ∑ mval ∈ M_finset, (valid_angles.filter (fun k => m k = mval)).card := by
    have h5 : valid_angles.card ≤ (Finset.biUnion M_finset (fun mval => valid_angles.filter (fun k => m k = mval))).card :=
      Finset.card_le_card h_partition
    have h6 : (Finset.biUnion M_finset (fun mval => valid_angles.filter (fun k => m k = mval))).card =
        ∑ mval ∈ M_finset, (valid_angles.filter (fun k => m k = mval)).card := by
      rw [Finset.card_biUnion (fun i _ j _ hne => h_disj i j hne)]
    rw [h6] at h5
    exact h5
  have h_angle_count : (valid_angles.card : ℝ) ≤
      3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) :=
    angle_count_lemma nθ α valid_angles
      (fun mval => valid_angles.filter (fun k => m k = mval))
      h_per_m
      h_angle_card

  -- Clear heavy hypotheses to avoid context bloat
  clear h_per_m h_disj h_partition h_angle_card h_exists hm m h_m_range

  -- nθ bound
  have h_nθ_eq : nθ = Nat.ceil (Real.pi / Δ) := by
    dsimp only [nθ, numAngles] <;> rfl
  have h_nθ_le : (nθ : ℝ) ≤ Real.pi / Δ + 1 :=
    nθ_bound_lemma r hr Δ hΔ_pos (by rfl) nθ h_nθ_eq

  -- Ceil bound
  have h_ceil : Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) ≤
      Nat.ceil ((40 * Real.pi + 4) / ξ') := by
    have h_pos3 : 0 ≤ (nθ : ℝ) / Real.pi := by positivity
    have h1 : (2 * α) * (nθ : ℝ) / Real.pi ≤ (4 * Real.pi * r / ξ') * (nθ : ℝ) / Real.pi := by
      have h : (2 * α) * ((nθ : ℝ) / Real.pi) ≤ (4 * Real.pi * r / ξ') * ((nθ : ℝ) / Real.pi) :=
        mul_le_mul_of_nonneg_right hL_angle h_pos3
      have h_goal : (2 * α) * (nθ : ℝ) / Real.pi = (2 * α) * ((nθ : ℝ) / Real.pi) := by ring
      have h_rhs : (4 * Real.pi * r / ξ') * (nθ : ℝ) / Real.pi = (4 * Real.pi * r / ξ') * ((nθ : ℝ) / Real.pi) := by ring
      rw [h_goal, h_rhs]
      exact h
    have h2 : (4 * Real.pi * r / ξ') * (nθ : ℝ) / Real.pi = (4 * r / ξ') * (nθ : ℝ) := by
      field_simp [Real.pi_pos.ne'] <;> ring
    rw [h2] at h1
    have h_pos4 : 0 ≤ 4 * r / ξ' := by positivity
    have h3 : (4 * r / ξ') * (nθ : ℝ) ≤ (4 * r / ξ') * (Real.pi / Δ + 1) :=
      mul_le_mul_of_nonneg_left h_nθ_le h_pos4
    have hΔ_eq : Δ = r / 10 := by simp [Δ, delta]
    have h41 : Real.pi / Δ = 10 * Real.pi / r := by
      rw [hΔ_eq]
      have h : Real.pi / (r / 10) = 10 * Real.pi / r := by
        rw [div_div_eq_mul_div] <;> ring
      exact h
    have h43 : 10 * Real.pi / r + 1 = (10 * Real.pi + r) / r := by
      have hne : r ≠ 0 := hr.ne'
      field_simp [hne] <;> ring
    have h4 : (4 * r / ξ') * (Real.pi / Δ + 1) = (40 * Real.pi + 4 * r) / ξ' := by
      rw [h41, h43]
      have hne : r ≠ 0 := hr.ne'
      have hne2 : ξ' ≠ 0 := hξ'_pos.ne'
      field_simp [hne, hne2] <;> ring
    have h5 : (40 * Real.pi + 4 * r) / ξ' ≤ (40 * Real.pi + 4) / ξ' := by
      have h51 : 4 * r ≤ 4 := by linarith [hr1]
      have h52 : 40 * Real.pi + 4 * r ≤ 40 * Real.pi + 4 := by linarith
      exact div_le_div_of_nonneg_right h52 hξ'_pos.le
    have h6 : (2 * α) * (nθ : ℝ) / Real.pi ≤ (40 * Real.pi + 4) / ξ' := by
      calc (2 * α) * (nθ : ℝ) / Real.pi
        ≤ (4 * r / ξ') * (nθ : ℝ) := h1
      _ ≤ (4 * r / ξ') * (Real.pi / Δ + 1) := h3
      _ = (40 * Real.pi + 4 * r) / ξ' := h4
      _ ≤ (40 * Real.pi + 4) / ξ' := h5
    exact Nat.ceil_mono h6

  -- Angle count numeric bound — GENERALIZED: use ξ ≤ 1 instead of ξ' ≤ 2
  have h_angle_count2 : (valid_angles.card : ℝ) ≤ (120 * Real.pi + 18) / ξ := by
    set X : ℝ := (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1 with hX
    have h7 : (valid_angles.card : ℝ) ≤ 3 * X := h_angle_count
    have h8 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) < (40 * Real.pi + 4) / ξ' + 1 := by
      have h9 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) ≤
          (Nat.ceil ((40 * Real.pi + 4) / ξ') : ℝ) := by exact_mod_cast h_ceil
      have h_pos : 0 ≤ (40 * Real.pi + 4) / ξ' := by positivity
      have h10 : (Nat.ceil ((40 * Real.pi + 4) / ξ') : ℝ) < (40 * Real.pi + 4) / ξ' + 1 :=
        Nat.ceil_lt_add_one h_pos
      linarith
    have h9 : (valid_angles.card : ℝ) ≤ 3 * ((40 * Real.pi + 4) / ξ' + 2) := by
      have h10 : 3 * X = 3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) := by
        simp [hX] <;> ring
      rw [h10] at h7
      linarith
    have h10 : 3 * ((40 * Real.pi + 4) / ξ' + 2) = 3 * (40 * Real.pi + 4) / ξ' + 6 := by ring
    rw [h10] at h9
    -- KEY CHANGE: absorb +6 using ξ ≤ 1 instead of ξ' ≤ 2
    have h11 : 6 ≤ 6 / ξ := by
      have h12 : 0 < ξ := hξ
      have h13 : ξ ≤ 1 := hξ_le_one
      have h14 : 6 * ξ ≤ 6 := by linarith
      calc (6 : ℝ)
        = 6 * ξ / ξ := by field_simp [h12.ne'] <;> ring
      _ ≤ 6 / ξ := by gcongr
    have h13 : 3 * (40 * Real.pi + 4) / ξ' + 6 ≤ 3 * (40 * Real.pi + 4) / ξ + 6 / ξ := by
      have h14 : 3 * (40 * Real.pi + 4) / ξ' ≤ 3 * (40 * Real.pi + 4) / ξ := by
        have h15 : ξ ≤ ξ' := hξ'_le
        have h16 : 0 ≤ 3 * (40 * Real.pi + 4) := by positivity
        exact div_le_div_of_nonneg_left h16 hξ h15
      linarith
    have h14 : 3 * (40 * Real.pi + 4) / ξ + 6 / ξ = (120 * Real.pi + 18) / ξ := by ring
    linarith

  -- For each valid angle, at most 41 offsets
  have h_offset_count : ∀ (k : ℕ), k ∈ valid_angles →
      ((offsetSet r).filter (fun j =>
        x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
        y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)))).card ≤ 41 := by
    intro k _
    let a0 := dot x (normalVec (angleVal r k))
    let S_off := (offsetSet r).filter (fun j =>
      x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
      y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)))
    have h1 : ∀ j ∈ S_off, |offsetVal r j - a0| < 2 * r := by
      intro j hj
      have h2 : |a0 - offsetVal r j| < 2 * r :=
        grid_tube_member (angleVal r k) (offsetVal r j) r hr x |>.mp
          (Finset.mem_filter.mp hj).2.1
      have h3 : |offsetVal r j - a0| = |a0 - offsetVal r j| := by
        rw [abs_sub_comm]
      rw [h3]
      exact h2
    have h2 : S_off ⊆ (offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, h1 j hj⟩
    have h3 : S_off.card ≤ ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card :=
      Finset.card_le_card h2
    have h5 : ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card ≤ 41 :=
      offset_packing_bound r hr a0
    linarith

  -- Preimage: pairs (k,j) whose line contains both x,y
  let preimage : Finset (ℕ × ℕ) := (angleSet r ×ˢ offsetSet r).filter (fun ⟨k, j⟩ =>
    x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
    y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)))
  let f : ℕ × ℕ → Line2 := fun ⟨k, j⟩ => lineOfAngleOffset (angleVal r k) (offsetVal r j)

  have h_main_card : (((tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card : ℝ) ≤
      (preimage.card : ℝ) := by
    have h_image : (tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L) ⊆
        preimage.image f := by
      intro L hL
      have hL_in : L ∈ tubeFamily r := (Finset.mem_filter.mp hL).1
      have hL_cond := (Finset.mem_filter.mp hL).2
      rcases Finset.mem_image.mp hL_in with ⟨⟨k, j⟩, hkj, rfl⟩
      have h_in_pre : (k, j) ∈ preimage := Finset.mem_filter.mpr ⟨hkj, hL_cond⟩
      exact Finset.mem_image.mpr ⟨(k, j), h_in_pre, rfl⟩
    have h1 : ((tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card ≤
        (preimage.image f).card := Finset.card_le_card h_image
    have h2 : (preimage.image f).card ≤ preimage.card := Finset.card_image_le
    exact_mod_cast le_trans h1 h2

  -- Key: preimage angles are valid angles (direction closeness)
  let P : ℕ → ℕ → Prop := fun k j =>
    x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
    y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j))

  have h_preimage_valid : ∀ (k j : ℕ), (k, j) ∈ preimage → k ∈ valid_angles := by
    intro k j hkj
    have h_kj_in : (k, j) ∈ angleSet r ×ˢ offsetSet r := (Finset.mem_filter.mp hkj).1
    have h_k_ang : k ∈ angleSet r := (Finset.mem_product.mp h_kj_in).1
    have hP : P k j := (Finset.mem_filter.mp hkj).2
    let L_k := lineOfAngleOffset (angleVal r k) (offsetVal r j)
    have hxL : x ∈ tube (2 * r) L_k := hP.1
    have hyL : y ∈ tube (2 * r) L_k := hP.2
    have hne : y ≠ x := by
      intro h
      have h' : ξ' = 0 := by
        simp [hξ'_def, h, dist_eq_norm]
      exact hξ'_pos.ne' h'
    have hne' : x ≠ y := hne.symm
    have h_dir : submoduleDirDist L_k.toAffine.direction (Submodule.span ℝ {x - y}) < c := by
      have h := direction_closeness_strict r hr L_k y x hne' hyL hxL
      simpa [c, hξ'_def, dist_eq_norm] using h
    have h_Lk_def : L_k = lineOfAngleOffset (angleVal r k) (offsetVal r j) := by rfl
    have h_dir_same : L_k.toAffine.direction = (lineOfAngleOffset (angleVal r k) 0).toAffine.direction := by
      have h1 : L_k.toAffine.direction = Submodule.span ℝ {dirVec (angleVal r k)} := by
        rw [h_Lk_def]
        exact lineOfAngleOffset_aff_direction (angleVal r k) (offsetVal r j)
      have h2 : (lineOfAngleOffset (angleVal r k) 0).toAffine.direction = Submodule.span ℝ {dirVec (angleVal r k)} :=
        lineOfAngleOffset_aff_direction (angleVal r k) 0
      exact Eq.trans h1 h2.symm
    rw [h_dir_same] at h_dir
    have h9 : u = (1 / ξ') • (x - y) := by simp [u] <;> rfl
    have h10 : IsUnit (1 / ξ') := by
      apply IsUnit.mk0
      positivity
    have h_span : Submodule.span ℝ {x - y} = Submodule.span ℝ {u} := by
      have h11 : Submodule.span ℝ {u} = Submodule.span ℝ {(1 / ξ') • (x - y)} := by
        congr 1 <;> simp [u, h9] <;> abel
      rw [h11]
      exact (Submodule.span_singleton_smul_eq h10 (x - y)).symm
    rw [h_span] at h_dir
    have h_eq : submoduleDirDist (lineOfAngleOffset (angleVal r k) 0).toAffine.direction (Submodule.span ℝ {u}) =
        |Real.cos (angleVal r k - φ)| :=
      dirDist_lineOfAngle_span (angleVal r k) φ u hu_norm hcos.symm hsin.symm
    rw [h_eq] at h_dir
    have h_final : |Real.sin (angleVal r k - θ0)| < c := by
      rw [h_sin_eq (angleVal r k)]
      exact h_dir
    exact Finset.mem_filter.mpr ⟨h_k_ang, h_final⟩

  have h_preimage_eq : preimage = (valid_angles ×ˢ offsetSet r).filter (fun ⟨k, j⟩ => P k j) := by
    ext ⟨k, j⟩
    simp only [preimage, P, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      have h1 : (k ∈ angleSet r ∧ j ∈ offsetSet r) ∧ P k j := h
      have h2 : P k j := h1.2
      have h_in_prod : (k, j) ∈ angleSet r ×ˢ offsetSet r := Finset.mem_product.mpr h1.1
      have h3 : k ∈ valid_angles := h_preimage_valid k j (Finset.mem_filter.mpr ⟨h_in_prod, h2⟩)
      have h4 : j ∈ offsetSet r := h1.1.2
      exact ⟨⟨h3, h4⟩, h2⟩
    · intro h
      have h1 : (k ∈ valid_angles ∧ j ∈ offsetSet r) ∧ P k j := h
      have h2 : P k j := h1.2
      have h3 : k ∈ angleSet r := (Finset.mem_filter.mp h1.1.1).1
      have h4 : j ∈ offsetSet r := h1.1.2
      exact ⟨⟨h3, h4⟩, h2⟩

  have h_preimage_bound : (preimage.card : ℝ) ≤ (valid_angles.card : ℝ) * 41 := by
    rw [h_preimage_eq]
    let Q : ℕ → Finset ℕ := fun k => (offsetSet r).filter (fun j => P k j)
    have h21 : (valid_angles ×ˢ offsetSet r).filter (fun ⟨k, j⟩ => P k j) =
        Finset.biUnion valid_angles (fun k => {k} ×ˢ Q k) := by
      ext ⟨k, j⟩
      simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_singleton, Finset.mem_product]
      constructor
      · intro h
        exact ⟨k, h.1.1, rfl, h.1.2, h.2⟩
      · rintro ⟨k', hk', rfl, hj, hP⟩
        exact ⟨⟨hk', hj⟩, hP⟩
    rw [h21]
    have h22 : ∀ k1 k2 : ℕ, k1 ≠ k2 → Disjoint ({k1} ×ˢ Q k1) ({k2} ×ˢ Q k2) := by
      intro k1 k2 hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x.1 ∈ {k1} := (Finset.mem_product.mp hx1).1
      have h1' : x.1 = k1 := Finset.mem_singleton.mp h1
      have h2 : x.1 ∈ {k2} := (Finset.mem_product.mp hx2).1
      have h2' : x.1 = k2 := Finset.mem_singleton.mp h2
      have h3 : k1 = k2 := by rw [←h1', h2']
      exact hne h3
    have h22' : Set.PairwiseDisjoint (valid_angles : Set ℕ) (fun k => {k} ×ˢ Q k) := by
      intro k1 _ k2 _ hne
      exact h22 k1 k2 hne
    rw [Finset.card_biUnion h22']
    have h23 : ∑ k ∈ valid_angles, ({k} ×ˢ Q k).card = ∑ k ∈ valid_angles, (Q k).card := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.card_product]
      <;> simp
    rw [h23]
    have h24 : ∑ k ∈ valid_angles, (Q k).card ≤ ∑ k ∈ valid_angles, (41 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact h_offset_count k hk
    have h25 : ∑ k ∈ valid_angles, (41 : ℕ) = valid_angles.card * 41 := by
      simp [Finset.sum_const, mul_comm] <;> ring
    rw [h25] at h24
    exact_mod_cast h24

  -- Final bound
  have h_final : (preimage.card : ℝ) ≤ ((120 * Real.pi + 18) / ξ) * 41 := by
    calc (preimage.card : ℝ)
      ≤ (valid_angles.card : ℝ) * 41 := h_preimage_bound
    _ ≤ ((120 * Real.pi + 18) / ξ) * 41 := by gcongr

  have h_const : (120 * Real.pi + 18) * 41 < 20000 := by
    have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith [Real.pi_pos]

  have h_final2 : (preimage.card : ℝ) < 20000 / ξ := by
    have h5 : (preimage.card : ℝ) ≤ ((120 * Real.pi + 18) / ξ) * 41 := h_final
    have h6 : ((120 * Real.pi + 18) / ξ) * 41 < 20000 / ξ := by
      have h7 : 0 < ξ := hξ
      have h8 : (120 * Real.pi + 18) * 41 < 20000 := h_const
      have h9 : ((120 * Real.pi + 18) / ξ) * 41 = ((120 * Real.pi + 18) * 41) / ξ := by ring
      rw [h9]
      gcongr
    linarith

  have h_final3 : (preimage.card : ℝ) ≤ 20000 / ξ := by
    exact h_final2.le

  exact h_main_card.trans h_final3

end RadialBootstrapping

end
