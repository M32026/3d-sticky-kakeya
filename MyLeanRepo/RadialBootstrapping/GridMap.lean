module

/-
  GridMap.lean

  Deterministic grid mapping for lines with injectivity and containment.

  Main results:
  - gridMap: deterministic map Line2 → Line2 using angle/offset rounding
  - gridMap_mem: gridMap L ∈ tubeFamily r
  - gridMap_2r: x ∈ tube(2r, gridMap L)
  - gridMap_containment: tube r L ∩ B(0,1) ⊆ tube(2r, gridMap L)
  - gridMap_injective: direction-separated (r/8) lines map injectively
-/

public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.GridLineDirDist

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped Classical ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

/-! ### Deterministic angle/offset representation -/

/-- Deterministic normal angle in [0, π) matching angle_offset_rep. -/
def Line2.gridAngle (L : Line2) : ℝ :=
  if L.normalVector 0 = -1 then 0
  else if L.normalVector 1 ≥ 0 then L.normalAngle
  else Real.pi - L.normalAngle

/-- Deterministic offset matching gridAngle. -/
def Line2.gridOffset (L : Line2) : ℝ :=
  if L.normalVector 0 = -1 then -L.offset
  else if L.normalVector 1 ≥ 0 then L.offset
  else -L.offset

lemma Line2.gridAngle_nonneg (L : Line2) : 0 ≤ L.gridAngle := by
  dsimp only [Line2.gridAngle]
  split_ifs with h1 h2
  · norm_num
  · exact L.normalAngle_nonneg
  · have h : 0 ≤ Real.pi - L.normalAngle := by
      have h' : L.normalAngle < Real.pi := L.normalAngle_lt_pi
      linarith [Real.pi_pos]
    exact h

lemma Line2.gridAngle_lt_pi (L : Line2) : L.gridAngle < Real.pi := by
  dsimp only [Line2.gridAngle]
  split_ifs with h1 h2
  · exact Real.pi_pos
  · exact L.normalAngle_lt_pi
  · have h_n1_neg : L.normalVector 1 < 0 := by linarith
    have h_unit : (L.normalVector 0) ^ 2 + (L.normalVector 1) ^ 2 = 1 := by
      have h2 : ‖L.normalVector‖ ^ 2 = 1 := by rw [L.normalVector_norm] <;> norm_num
      have h3 : ‖L.normalVector‖ ^ 2 = (L.normalVector 0) ^ 2 + (L.normalVector 1) ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
      linarith
    have h_sin_sq : Real.sin L.normalAngle ^ 2 = (L.normalVector 1) ^ 2 := by
      have h_cos : Real.cos L.normalAngle = L.normalVector 0 := by
        dsimp only [Line2.normalAngle]
        have h_arccos_ne : Real.arccos (L.normalVector 0) ≠ Real.pi := by
          intro h; have h' : L.normalVector 0 = -1 := by
            have h3 : Real.cos (Real.arccos (L.normalVector 0)) = L.normalVector 0 := Real.cos_arccos (by nlinarith [h_unit]) (by nlinarith [h_unit])
            rw [h] at h3; norm_num at h3 <;> linarith
          exact h1 h'
        rw [if_neg h_arccos_ne]
        exact Real.cos_arccos (by nlinarith [h_unit]) (by nlinarith [h_unit])
      have h1 : Real.cos L.normalAngle ^ 2 + Real.sin L.normalAngle ^ 2 = 1 := Real.cos_sq_add_sin_sq _
      have h5 : Real.sin L.normalAngle ^ 2 = 1 - Real.cos L.normalAngle ^ 2 := by linarith
      rw [h5, h_cos] <;> linarith
    have h_angle_pos : 0 < L.normalAngle := by
      by_contra h; have h' : L.normalAngle = 0 := by linarith [L.normalAngle_nonneg]
      rw [h'] at h_sin_sq; simp at h_sin_sq <;> nlinarith
    have h : Real.pi - L.normalAngle < Real.pi := by linarith [Real.pi_pos, h_angle_pos]
    exact h

lemma Line2.gridAngle_case (L : Line2) :
    (normalVec L.gridAngle = L.normalVector ∧ L.gridOffset = L.offset) ∨
    (normalVec L.gridAngle = -L.normalVector ∧ L.gridOffset = -L.offset) := by
  dsimp only [Line2.gridAngle, Line2.gridOffset]
  set n : Point := L.normalVector with hn
  set a : ℝ := L.offset with ha
  have h_n0_abs : -1 ≤ n 0 ∧ n 0 ≤ 1 := by
    have h1 : n 0 ^ 2 + n 1 ^ 2 = 1 := by
      have h2 : ‖n‖ ^ 2 = 1 := by rw [L.normalVector_norm] <;> norm_num
      have h3 : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
      linarith
    exact ⟨by nlinarith, by nlinarith⟩
  by_cases h_n0 : n 0 = -1
  · -- Case n 0 = -1
    have h_n1 : n 1 = 0 := by
      have h_unit : n 0 ^ 2 + n 1 ^ 2 = 1 := by
        have h2 : ‖n‖ ^ 2 = 1 := by rw [L.normalVector_norm] <;> norm_num
        have h3 : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
          simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
        linarith
      rw [h_n0] at h_unit; nlinarith
    have h : normalVec 0 = -n := by
      ext i; fin_cases i <;> simp [normalVec_component0, normalVec_component1, h_n0, h_n1] <;> norm_num
    rw [if_pos h_n0, if_pos h_n0]
    exact Or.inr ⟨h, by ring⟩
  · -- Case n 0 ≠ -1
    have h_n0_ne : n 0 ≠ -1 := h_n0
    rw [if_neg h_n0_ne, if_neg h_n0_ne]
    by_cases h_n1 : n 1 ≥ 0
    · -- n 1 ≥ 0
      rw [if_pos h_n1, if_pos h_n1]
      have h_cos : Real.cos L.normalAngle = n 0 := by
        dsimp only [Line2.normalAngle]
        have h_arccos_ne : Real.arccos (n 0) ≠ Real.pi := by
          intro h; have h' : n 0 = -1 := by
            have h3 : Real.cos (Real.arccos (n 0)) = n 0 := Real.cos_arccos h_n0_abs.1 h_n0_abs.2
            rw [h] at h3; norm_num at h3 <;> linarith
          exact h_n0_ne h'
        rw [if_neg h_arccos_ne]
        exact Real.cos_arccos h_n0_abs.1 h_n0_abs.2
      have h_sin_nonneg : 0 ≤ Real.sin L.normalAngle := Real.sin_nonneg_of_mem_Icc ⟨L.normalAngle_nonneg, by linarith [L.normalAngle_lt_pi]⟩
      have h_sin_sq : Real.sin L.normalAngle ^ 2 = n 1 ^ 2 := by
        have h1 : Real.cos L.normalAngle ^ 2 + Real.sin L.normalAngle ^ 2 = 1 := Real.cos_sq_add_sin_sq _
        have h2 : n 0 ^ 2 + n 1 ^ 2 = 1 := by
          have h3 : ‖n‖ ^ 2 = 1 := by rw [L.normalVector_norm] <;> norm_num
          have h4 : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
            simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
          linarith
        have h5 : Real.sin L.normalAngle ^ 2 = 1 - Real.cos L.normalAngle ^ 2 := by linarith
        rw [h5, h_cos]; linarith
      have h_sin_eq : Real.sin L.normalAngle = n 1 := by nlinarith
      have h_nv : normalVec L.normalAngle = n := by
        ext i; fin_cases i
        · simpa [normalVec_component0] using h_cos
        · simpa [normalVec_component1] using h_sin_eq
      exact Or.inl ⟨h_nv, rfl⟩
    · -- n 1 < 0
      have h_n1_neg : n 1 < 0 := by linarith
      rw [if_neg h_n1, if_neg h_n1]
      have h_cos : Real.cos L.normalAngle = n 0 := by
        dsimp only [Line2.normalAngle]
        have h_arccos_ne : Real.arccos (n 0) ≠ Real.pi := by
          intro h; have h' : n 0 = -1 := by
            have h3 : Real.cos (Real.arccos (n 0)) = n 0 := Real.cos_arccos h_n0_abs.1 h_n0_abs.2
            rw [h] at h3; norm_num at h3 <;> linarith
          exact h_n0_ne h'
        rw [if_neg h_arccos_ne]
        exact Real.cos_arccos h_n0_abs.1 h_n0_abs.2
      have h_sin_sq : Real.sin L.normalAngle ^ 2 = n 1 ^ 2 := by
        have h1 : Real.cos L.normalAngle ^ 2 + Real.sin L.normalAngle ^ 2 = 1 := Real.cos_sq_add_sin_sq _
        have h2 : n 0 ^ 2 + n 1 ^ 2 = 1 := by
          have h3 : ‖n‖ ^ 2 = 1 := by rw [L.normalVector_norm] <;> norm_num
          have h4 : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
            simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
          linarith
        have h5 : Real.sin L.normalAngle ^ 2 = 1 - Real.cos L.normalAngle ^ 2 := by linarith
        rw [h5, h_cos]; linarith
      have h_sin_nonneg : 0 ≤ Real.sin L.normalAngle := Real.sin_nonneg_of_mem_Icc ⟨L.normalAngle_nonneg, by linarith [L.normalAngle_lt_pi]⟩
      have h_sin_eq : Real.sin L.normalAngle = -n 1 := by
        have h1 : (Real.sin L.normalAngle)^2 = (-n 1)^2 := by
          have h2 : (-n 1)^2 = (n 1)^2 := by ring
          rw [h2]; exact h_sin_sq
        have h3 : 0 ≤ Real.sin L.normalAngle := h_sin_nonneg
        have h4 : 0 ≤ -n 1 := by linarith
        have h5 : (Real.sin L.normalAngle - (-n 1)) * (Real.sin L.normalAngle + (-n 1)) = 0 := by
          have h6 : (Real.sin L.normalAngle)^2 - (-n 1)^2 = 0 := by
            rw [h1] <;> ring
          linarith
        have h7 : 0 < Real.sin L.normalAngle + (-n 1) := by linarith [h_sin_nonneg, h_n1_neg]
        have h8 : Real.sin L.normalAngle - (-n 1) = 0 := by
          apply (mul_eq_zero.mp h5).resolve_right
          exact h7.ne'
        linarith
      have h_angle_pos : 0 < L.normalAngle := by
        have h_sin_pos : 0 < Real.sin L.normalAngle := by rw [h_sin_eq]; linarith
        by_contra h; have h' : L.normalAngle = 0 := by linarith [L.normalAngle_nonneg]
        rw [h'] at h_sin_pos; simp at h_sin_pos <;> linarith
      let θ_c := Real.pi - L.normalAngle
      have h_nv : normalVec θ_c = -n := by
        ext i; fin_cases i
        · simp [normalVec_component0, θ_c, Real.cos_pi_sub, h_cos] <;> ring
        · simp [normalVec_component1, θ_c, Real.sin_pi_sub, h_sin_eq] <;> ring
      exact Or.inr ⟨h_nv, by ring⟩

/-! ### Grid indices -/

/-- Deterministic angle grid index. -/
def gridAngleIndex (r : ℝ) (θ : ℝ) : ℕ :=
  Nat.floor (θ * (numAngles r : ℝ) / Real.pi)

/-- Deterministic offset grid index. -/
def gridOffsetIndex (r : ℝ) (a : ℝ) : ℕ :=
  Nat.floor ((a + 2) / delta r)

lemma gridAngleIndex_mem (r : ℝ) (hr : 0 < r) (θ : ℝ)
    (hθ1 : 0 ≤ θ) (hθ2 : θ < Real.pi) :
    gridAngleIndex r θ ∈ angleSet r := by
  dsimp only [gridAngleIndex]
  set nθ : ℕ := numAngles r with hnθ
  have h_nθ_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]
    exact Nat.ceil_pos.mpr (div_pos Real.pi_pos (by dsimp only [delta]; positivity))
  have h_nθ_pos' : 0 < (nθ : ℝ) := by exact_mod_cast h_nθ_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  let k : ℕ := Nat.floor (θ * (nθ : ℝ) / Real.pi)
  have hk1 : (k : ℝ) ≤ θ * (nθ : ℝ) / Real.pi := Nat.floor_le (by positivity)
  simp only [angleSet, Finset.mem_range]
  have h9 : θ * (nθ : ℝ) / Real.pi < (nθ : ℝ) := by
    have h10 : θ * (nθ : ℝ) < Real.pi * (nθ : ℝ) := by gcongr
    calc θ * (nθ : ℝ) / Real.pi
      < Real.pi * (nθ : ℝ) / Real.pi := by gcongr
    _ = (nθ : ℝ) := by field_simp [hpi.ne'] <;> ring
  have h : (k : ℝ) < (nθ : ℝ) := by
    calc (k : ℝ) ≤ θ * (nθ : ℝ) / Real.pi := hk1
      _ < (nθ : ℝ) := h9
  exact_mod_cast h

lemma gridAngleIndex_bin (r : ℝ) (hr : 0 < r) (θ : ℝ)
    (hθ1 : 0 ≤ θ) (hθ2 : θ < Real.pi) :
    let k := gridAngleIndex r θ
    angleVal r k ≤ θ ∧ θ < angleVal r k + Real.pi / (numAngles r : ℝ) := by
  dsimp only [gridAngleIndex]
  set nθ : ℕ := numAngles r with hnθ
  have h_nθ_pos' : 0 < (nθ : ℝ) := by
    have h : 0 < nθ := Nat.ceil_pos.mpr (div_pos Real.pi_pos (by dsimp only [delta]; positivity))
    exact_mod_cast h
  have hpi : 0 < Real.pi := Real.pi_pos
  let k : ℕ := Nat.floor (θ * (nθ : ℝ) / Real.pi)
  have hk1 : (k : ℝ) ≤ θ * (nθ : ℝ) / Real.pi := Nat.floor_le (by positivity)
  have hk2 : θ * (nθ : ℝ) / Real.pi < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have h1 : (k : ℝ) * Real.pi / (nθ : ℝ) ≤ θ := by
    have h13 : (k : ℝ) * Real.pi / (nθ : ℝ) ≤
        (θ * (nθ : ℝ) / Real.pi) * Real.pi / (nθ : ℝ) := by gcongr
    have h14 : (θ * (nθ : ℝ) / Real.pi) * Real.pi / (nθ : ℝ) = θ := by
      field_simp [hpi.ne', h_nθ_pos'.ne'] <;> ring
    linarith
  have h2 : θ < (k : ℝ) * Real.pi / (nθ : ℝ) + Real.pi / (nθ : ℝ) := by
    have h15 : θ * (nθ : ℝ) / Real.pi - (k : ℝ) < 1 := by linarith [hk2]
    have h16 : θ - (k : ℝ) * Real.pi / (nθ : ℝ) =
        Real.pi / (nθ : ℝ) * (θ * (nθ : ℝ) / Real.pi - (k : ℝ)) := by
      field_simp [hpi.ne', h_nθ_pos'.ne'] <;> ring
    have h17 : 0 < Real.pi / (nθ : ℝ) := by positivity
    nlinarith
  exact ⟨h1, h2⟩

lemma gridAngleIndex_err (r : ℝ) (hr : 0 < r) (θ : ℝ)
    (hθ1 : 0 ≤ θ) (hθ2 : θ < Real.pi) :
    |θ - angleVal r (gridAngleIndex r θ)| ≤ Real.pi / (numAngles r : ℝ) := by
  let k := gridAngleIndex r θ
  have h_bin : angleVal r k ≤ θ ∧ θ < angleVal r k + Real.pi / (numAngles r : ℝ) :=
    gridAngleIndex_bin r hr θ hθ1 hθ2
  have h1 : 0 ≤ θ - angleVal r k := by linarith [h_bin.1]
  have h2 : θ - angleVal r k < Real.pi / (numAngles r : ℝ) := by linarith [h_bin.2]
  rw [abs_of_nonneg h1]
  linarith

lemma gridOffsetIndex_mem (r : ℝ) (hr : 0 < r) (a : ℝ)
    (ha1 : -2 ≤ a) (ha2 : a ≤ 2) :
    gridOffsetIndex r a ∈ offsetSet r := by
  dsimp only [gridOffsetIndex]
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  have h_nonneg : 0 ≤ (a + 2) / Δ := by apply div_nonneg <;> linarith
  let j : ℕ := Nat.floor ((a + 2) / Δ)
  have hj1 : (j : ℝ) ≤ (a + 2) / Δ := Nat.floor_le h_nonneg
  simp only [offsetSet, Finset.mem_range]
  have h_j_le4 : (j : ℝ) ≤ 4 / Δ := by
    calc (j : ℝ) ≤ (a + 2) / Δ := hj1
      _ ≤ 4 / Δ := by gcongr <;> linarith
  have h_j_le_ceil : (j : ℝ) ≤ (Nat.ceil (4 / Δ) : ℝ) := by
    calc (j : ℝ) ≤ 4 / Δ := h_j_le4
      _ ≤ (Nat.ceil (4 / Δ) : ℝ) := Nat.le_ceil (4 / Δ)
  have h_goal : (j : ℝ) < (Nat.ceil (4 / Δ) + 1 : ℝ) := by linarith
  exact_mod_cast h_goal

lemma gridOffsetIndex_err (r : ℝ) (hr : 0 < r) (a : ℝ)
    (ha1 : -2 ≤ a) (ha2 : a ≤ 2) :
    |a - offsetVal r (gridOffsetIndex r a)| ≤ delta r := by
  dsimp only [gridOffsetIndex]
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  have h_nonneg : 0 ≤ (a + 2) / Δ := by apply div_nonneg <;> linarith
  let j : ℕ := Nat.floor ((a + 2) / Δ)
  have hj1 : (j : ℝ) ≤ (a + 2) / Δ := Nat.floor_le h_nonneg
  have hj2 : (a + 2) / Δ < (j : ℝ) + 1 := Nat.lt_floor_add_one ((a + 2) / Δ)
  have h1 : 0 ≤ (a + 2) / Δ - (j : ℝ) := by linarith
  have h3 : a - offsetVal r j = Δ * ((a + 2) / Δ - (j : ℝ)) := by
    have h4 : offsetVal r j = -2 + (j : ℝ) * Δ := by
      dsimp only [offsetVal, Δ, delta] <;> ring
    rw [h4]
    have h5 : Δ * ((a + 2) / Δ) = a + 2 := by
      field_simp [hΔ_pos.ne'] <;> ring
    have h6 : a - (-2 + (j : ℝ) * Δ) = Δ * ((a + 2) / Δ) - Δ * (j : ℝ) := by
      rw [h5] <;> ring
    rw [h6, mul_sub]
  rw [h3]
  have h4 : 0 ≤ Δ * ((a + 2) / Δ - (j : ℝ)) := by positivity
  rw [abs_of_nonneg h4]
  have h5 : (a + 2) / Δ - (j : ℝ) < 1 := by linarith [hj2]
  have h6 : Δ * ((a + 2) / Δ - (j : ℝ)) < Δ := by
    have h7 : Δ * ((a + 2) / Δ - (j : ℝ)) < Δ * 1 := mul_lt_mul_of_pos_left h5 hΔ_pos
    have h8 : Δ * 1 = Δ := by ring
    rw [h8] at h7
    exact h7
  linarith

/-! ### gridMap definition and basic properties -/

/-- Deterministic grid map of a line using angle/offset rounding. -/
noncomputable def gridMap (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (hxBall : x ∈ closedBall (0 : Point) 1)
    (L : Line2) (hx : x ∈ tube r L) : Line2 :=
  let θ_c : ℝ := L.gridAngle
  let a_c : ℝ := L.gridOffset
  let k : ℕ := gridAngleIndex r θ_c
  let j : ℕ := gridOffsetIndex r a_c
  lineOfAngleOffset (angleVal r k) (offsetVal r j)

/-- gridMap L ∈ tubeFamily r. -/
lemma gridMap_mem (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (hxBall : x ∈ closedBall (0 : Point) 1)
    (L : Line2) (hx : x ∈ tube r L) :
    gridMap r hr hr1 x hxBall L hx ∈ tubeFamily r := by
  dsimp only [gridMap]
  let θ_c : ℝ := L.gridAngle
  let a_c : ℝ := L.gridOffset
  let k : ℕ := gridAngleIndex r θ_c
  let j : ℕ := gridOffsetIndex r a_c
  have hθ1 : 0 ≤ θ_c := L.gridAngle_nonneg
  have hθ2 : θ_c < Real.pi := L.gridAngle_lt_pi
  have h_abs : |a_c| < 2 := by
    have h_off : |L.offset| < 2 := L.offset_bound r hr hr1 x hx hxBall
    dsimp only [a_c, Line2.gridOffset]
    split_ifs <;> simpa [abs_neg] using h_off
  have ha1 : -2 ≤ a_c := by linarith [abs_lt.mp h_abs]
  have ha2 : a_c ≤ 2 := by linarith [abs_lt.mp h_abs]
  have hk_in : k ∈ angleSet r := gridAngleIndex_mem r hr θ_c hθ1 hθ2
  have hj_in : j ∈ offsetSet r := gridOffsetIndex_mem r hr a_c ha1 ha2
  simp only [tubeFamily, Finset.mem_image]
  refine ⟨(k, j), ?_, rfl⟩
  simp only [Finset.mem_product] <;> exact ⟨hk_in, hj_in⟩

/-! ### Geometric containment proof -/

lemma gridMap_geometric_core (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (L : Line2) (x : Point) (hx : x ∈ tube r L) (hxBall : x ∈ closedBall (0 : Point) 1)
    (θ_c a_c : ℝ) (hθ1 : 0 ≤ θ_c) (hθ2 : θ_c < Real.pi)
    (h_case : (normalVec θ_c = L.normalVector ∧ a_c = L.offset) ∨
              (normalVec θ_c = -L.normalVector ∧ a_c = -L.offset))
    (h_abs : |a_c| < 2) (k j : ℕ)
    (hk_err : |θ_c - angleVal r k| ≤ Real.pi / (numAngles r : ℝ))
    (hj_err : |a_c - offsetVal r j| ≤ delta r) :
    let G := lineOfAngleOffset (angleVal r k) (offsetVal r j)
    x ∈ tube (2 * r) G ∧ (tube r L ∩ closedBall (0 : Point) 2 ⊆ tube (2 * r) G) := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta] <;> positivity
  set n : Point := L.normalVector with hn
  set a : ℝ := L.offset with ha
  let nc : Point := normalVec θ_c
  have h_nc_eq : nc = n ∨ nc = -n := by
    rcases h_case with (h | h) <;> [exact Or.inl h.1; exact Or.inr h.1]
  have h_ac_eq : a_c = a ∨ a_c = -a := by
    rcases h_case with (h | h) <;> [exact Or.inl h.2; exact Or.inr h.2]
  have h_line_prop : ∀ (z : Point), z ∈ L.toSet → dot z nc = a_c := by
    intro z hz
    have h_dot : dot z n = a := L.dot_eq_offset hz
    rcases h_case with (h | h)
    · have h_nc : nc = n := h.1
      have h_ac : a_c = a := h.2
      have h_goal : dot z nc = dot z n := by rw [h_nc]
      rw [h_goal, h_ac] <;> exact h_dot
    · have h_nc : nc = -n := h.1
      have h_ac : a_c = -a := h.2
      have h_goal : dot z nc = dot z (-n) := by rw [h_nc]
      rw [h_goal, h_ac]
      have h3 : dot z (-n) = -dot z n := by
        simp [dot_apply, Fin.sum_univ_two] <;> ring
      rw [h3, h_dot] <;> ring
  have h_tube_dot : ∀ (y : Point), y ∈ tube r L → |dot y nc - a_c| < r := by
    intro y hy
    have h_ex : ∃ (z : Point), z ∈ L.toSet ∧ dist y z < r :=
      (Metric.mem_thickening_iff (E := L.toSet) (x := y)).mp hy
    rcases h_ex with ⟨z, hz, hdist⟩
    have h_dot_z : dot z nc = a_c := h_line_prop z hz
    have h1 : |dot y nc - a_c| = |dot y nc - dot z nc| := by rw [h_dot_z]
    rw [h1]
    have h2 : dot y nc - dot z nc = dot (y - z) nc := by
      have h21 : dot (y - z) nc = dot y nc - dot z nc := by
        simp [dot_apply, Fin.sum_univ_two] <;> ring
      exact h21.symm
    rw [h2]
    have h3 : |dot (y - z) nc| ≤ ‖y - z‖ * ‖nc‖ := abs_dot_le_norm (y - z) nc
    have h4 : ‖nc‖ = 1 := normalVec_norm θ_c
    rw [h4] at h3
    have h5 : |dot (y - z) nc| ≤ ‖y - z‖ := by simpa using h3
    have h6 : ‖y - z‖ < r := hdist
    linarith
  set θ' : ℝ := angleVal r k with hθ'
  set a' : ℝ := offsetVal r j with ha'
  set n' : Point := normalVec θ' with hn'
  set G : Line2 := lineOfAngleOffset θ' a' with hG
  have h_pi_le_delta : Real.pi / (numAngles r : ℝ) ≤ Δ := by
    have h1 : Real.pi / Δ ≤ (numAngles r : ℝ) := by
      dsimp only [numAngles]; exact Nat.le_ceil (Real.pi / Δ)
    have h2 : 0 < Δ := hΔ_pos
    have h3 : 0 < (numAngles r : ℝ) := by
      have h4 : 0 < Real.pi / Δ := div_pos Real.pi_pos h2
      have h5 : 0 < numAngles r := Nat.ceil_pos.mpr h4
      exact_mod_cast h5
    calc Real.pi / (numAngles r : ℝ)
      ≤ Real.pi / (Real.pi / Δ) := by gcongr
    _ = Δ := by field_simp [h2.ne'] <;> ring
  have h_diff1 : ∀ (y : Point), |dot y n' - dot y nc| ≤ ‖y‖ * ‖n' - nc‖ := by
    intro y
    have h : dot y n' - dot y nc = dot y (n' - nc) := by
      have h2 : dot y (n' - nc) = dot y n' - dot y nc := dot_sub_right y n' nc
      exact h2.symm
    rw [h]
    exact abs_dot_le_norm y (n' - nc)
  have h_diff2 : ‖n' - nc‖ ≤ |θ_c - θ'| := by
    have h : ‖n' - nc‖ = ‖nc - n'‖ := by rw [norm_sub_rev]
    rw [h]
    exact normalVec_dist_le θ_c θ'
  have h_general_bound : ∀ (y : Point) (B : ℝ), 0 ≤ B → ‖y‖ ≤ B → y ∈ tube r L →
      |dot y n' - a'| ≤ B * (Real.pi / (numAngles r : ℝ)) + r + Δ := by
    intro y B hB_nonneg hB hy_tube
    have h_dot_y : |dot y nc - a_c| < r := h_tube_dot y hy_tube
    have h_ineq : |dot y n' - a'| ≤
        |dot y n' - dot y nc| + |dot y nc - a_c| + |a_c - a'| := by
      have h_eq : dot y n' - a' = (dot y n' - dot y nc) + ((dot y nc - a_c) + (a_c - a')) := by ring
      have h_abs : |dot y n' - a'| = |(dot y n' - dot y nc) + ((dot y nc - a_c) + (a_c - a'))| := by
        rw [h_eq]
      rw [h_abs]
      have h12 : |(dot y n' - dot y nc) + ((dot y nc - a_c) + (a_c - a'))| ≤
          |dot y n' - dot y nc| + |(dot y nc - a_c) + (a_c - a')| := by
        exact abs_add_le _ _
      have h13 : |(dot y nc - a_c) + (a_c - a')| ≤ |dot y nc - a_c| + |a_c - a'| := by
        exact abs_add_le _ _
      have h14 : |(dot y n' - dot y nc) + ((dot y nc - a_c) + (a_c - a'))| ≤
          |dot y n' - dot y nc| + |dot y nc - a_c| + |a_c - a'| := by
        calc |(dot y n' - dot y nc) + ((dot y nc - a_c) + (a_c - a'))|
          ≤ |dot y n' - dot y nc| + |(dot y nc - a_c) + (a_c - a')| := h12
        _ ≤ |dot y n' - dot y nc| + (|dot y nc - a_c| + |a_c - a'|) := by gcongr
        _ = |dot y n' - dot y nc| + |dot y nc - a_c| + |a_c - a'| := by ring
      exact h14
    have h_step1 : |dot y n' - a'| ≤ ‖y‖ * ‖n' - nc‖ + |dot y nc - a_c| + |a_c - a'| := by
      calc |dot y n' - a'|
        ≤ |dot y n' - dot y nc| + |dot y nc - a_c| + |a_c - a'| := h_ineq
      _ ≤ ‖y‖ * ‖n' - nc‖ + |dot y nc - a_c| + |a_c - a'| := by gcongr <;> exact h_diff1 y
    have h_step2 : ‖y‖ * ‖n' - nc‖ ≤ B * |θ_c - θ'| := by
      calc ‖y‖ * ‖n' - nc‖
        ≤ B * ‖n' - nc‖ := by gcongr
      _ ≤ B * |θ_c - θ'| := by exact mul_le_mul_of_nonneg_left h_diff2 hB_nonneg
    have h_step4 : |a_c - a'| ≤ Δ := hj_err
    have h_dot_le : |dot y nc - a_c| ≤ r := by linarith [h_dot_y]
    calc |dot y n' - a'|
      ≤ ‖y‖ * ‖n' - nc‖ + |dot y nc - a_c| + |a_c - a'| := h_step1
    _ ≤ B * |θ_c - θ'| + r + Δ := by
      exact add_le_add (add_le_add h_step2 h_dot_le) h_step4
    _ ≤ B * (Real.pi / (numAngles r : ℝ)) + r + Δ := by
      have h : B * |θ_c - θ'| ≤ B * (Real.pi / (numAngles r : ℝ)) :=
        mul_le_mul_of_nonneg_left hk_err hB_nonneg
      exact add_le_add (add_le_add h (le_refl r)) (le_refl Δ)
  have h_mem_tube : ∀ (y : Point), |dot y n' - a'| < 2 * r → y ∈ tube (2 * r) G := by
    intro y h_bound
    rcases lineOfAngleOffset_projection θ' a' y with ⟨q, hq_mem, hq_norm⟩
    have h3 : ‖y - q‖ < 2 * r := by rw [hq_norm] <;> exact h_bound
    have h_tube : tube (2 * r) G = Metric.thickening (2 * r) G.toSet := by simp only [tube]
    rw [h_tube]
    rw [Metric.mem_thickening_iff (E := G.toSet) (x := y)]
    exact ⟨q, hq_mem, h3⟩
  have h_x_norm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hxBall
  have h_x_bound : |dot x n' - a'| ≤ 1 * (Real.pi / (numAngles r : ℝ)) + r + Δ :=
    h_general_bound x 1 (by norm_num) h_x_norm hx
  have h_x_strict : |dot x n' - a'| < 2 * r := by
    calc |dot x n' - a'|
      ≤ 1 * (Real.pi / (numAngles r : ℝ)) + r + Δ := h_x_bound
    _ ≤ 1 * Δ + r + Δ := by gcongr <;> exact h_pi_le_delta
    _ = r + 2 * Δ := by ring
    _ < 2 * r := by dsimp only [Δ, delta] <;> linarith
  have h4 : x ∈ tube (2 * r) G := h_mem_tube x h_x_strict
  have h_containment : tube r L ∩ closedBall (0 : Point) 2 ⊆ tube (2 * r) G := by
    intro y hy
    have hy_tube : y ∈ tube r L := hy.1
    have hy_ball : y ∈ closedBall (0 : Point) 2 := hy.2
    have h_y_norm : ‖y‖ ≤ 2 := by simpa [Metric.mem_closedBall] using hy_ball
    have h_y_bound : |dot y n' - a'| ≤ 2 * (Real.pi / (numAngles r : ℝ)) + r + Δ :=
      h_general_bound y 2 (by norm_num) h_y_norm hy_tube
    have h_y_strict : |dot y n' - a'| < 2 * r := by
      calc |dot y n' - a'|
        ≤ 2 * (Real.pi / (numAngles r : ℝ)) + r + Δ := h_y_bound
      _ ≤ 2 * Δ + r + Δ := by gcongr <;> exact h_pi_le_delta
      _ = r + 3 * Δ := by ring
      _ < 2 * r := by dsimp only [Δ, delta] <;> linarith
    exact h_mem_tube y h_y_strict
  exact ⟨h4, h_containment⟩

/-- x ∈ tube(2r, gridMap L). -/
lemma gridMap_2r (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (hxBall : x ∈ closedBall (0 : Point) 1)
    (L : Line2) (hx : x ∈ tube r L) :
    x ∈ tube (2 * r) (gridMap r hr hr1 x hxBall L hx) := by
  dsimp only [gridMap]
  let θ_c : ℝ := L.gridAngle
  let a_c : ℝ := L.gridOffset
  let k : ℕ := gridAngleIndex r θ_c
  let j : ℕ := gridOffsetIndex r a_c
  have hθ1 : 0 ≤ θ_c := L.gridAngle_nonneg
  have hθ2 : θ_c < Real.pi := L.gridAngle_lt_pi
  have h_case := L.gridAngle_case
  have h_abs : |a_c| < 2 := by
    have h_off : |L.offset| < 2 := L.offset_bound r hr hr1 x hx hxBall
    dsimp only [a_c, Line2.gridOffset]
    split_ifs <;> simpa [abs_neg] using h_off
  have ha1 : -2 ≤ a_c := by linarith [abs_lt.mp h_abs]
  have ha2 : a_c ≤ 2 := by linarith [abs_lt.mp h_abs]
  have hk_err : |θ_c - angleVal r k| ≤ Real.pi / (numAngles r : ℝ) :=
    gridAngleIndex_err r hr θ_c hθ1 hθ2
  have hj_err : |a_c - offsetVal r j| ≤ delta r :=
    gridOffsetIndex_err r hr a_c ha1 ha2
  exact (gridMap_geometric_core r hr hr1 L x hx hxBall θ_c a_c hθ1 hθ2 h_case h_abs k j hk_err hj_err).1

/-- tube r L ∩ B(0,1) ⊆ tube(2r, gridMap L). -/
lemma gridMap_containment (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (hxBall : x ∈ closedBall (0 : Point) 1)
    (L : Line2) (hx : x ∈ tube r L) :
    tube r L ∩ closedBall (0 : Point) 1 ⊆ tube (2 * r) (gridMap r hr hr1 x hxBall L hx) := by
  dsimp only [gridMap]
  let θ_c : ℝ := L.gridAngle
  let a_c : ℝ := L.gridOffset
  let k : ℕ := gridAngleIndex r θ_c
  let j : ℕ := gridOffsetIndex r a_c
  have hθ1 : 0 ≤ θ_c := L.gridAngle_nonneg
  have hθ2 : θ_c < Real.pi := L.gridAngle_lt_pi
  have h_case := L.gridAngle_case
  have h_abs : |a_c| < 2 := by
    have h_off : |L.offset| < 2 := L.offset_bound r hr hr1 x hx hxBall
    dsimp only [a_c, Line2.gridOffset]
    split_ifs <;> simpa [abs_neg] using h_off
  have ha1 : -2 ≤ a_c := by linarith [abs_lt.mp h_abs]
  have ha2 : a_c ≤ 2 := by linarith [abs_lt.mp h_abs]
  have hk_err : |θ_c - angleVal r k| ≤ Real.pi / (numAngles r : ℝ) :=
    gridAngleIndex_err r hr θ_c hθ1 hθ2
  have hj_err : |a_c - offsetVal r j| ≤ delta r :=
    gridOffsetIndex_err r hr a_c ha1 ha2
  have h_contain := (gridMap_geometric_core r hr hr1 L x hx hxBall θ_c a_c hθ1 hθ2 h_case h_abs k j hk_err hj_err).2
  intro y hy
  have hy1 : y ∈ tube r L := hy.1
  have hy2 : y ∈ closedBall (0 : Point) 1 := hy.2
  have hy3 : y ∈ closedBall (0 : Point) 2 := by
    have h : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy2
    have h' : ‖y‖ ≤ 2 := by linarith
    simpa [Metric.mem_closedBall] using h'
  exact h_contain ⟨hy1, hy3⟩

/-! ### Injectivity -/

/-- The direction subspace of L equals span of dirVec L.gridAngle. -/
lemma Line2.gridAngle_direction (L : Line2) :
    L.toAffine.direction = Submodule.span ℝ {dirVec L.gridAngle} := by
  have h_case := L.gridAngle_case
  rcases h_case with (h | h)
  · -- normalVec gridAngle = L.normalVector
    have h_nv : normalVec L.gridAngle = L.normalVector := h.1
    have h1 : dirVec L.gridAngle = L.unitDirection := by
      ext i
      fin_cases i
      · have h_sin : Real.sin L.gridAngle = (L.normalVector) 1 := by
          have h_eq1 : (normalVec L.gridAngle) 1 = (L.normalVector) 1 := by
            exact congr_arg (fun p : Point => p 1) h_nv
          simpa [normalVec_component1] using h_eq1
        have h_nv1 : (L.normalVector) 1 = -L.unitDirection 0 := by
          exact normalVector_component1 L
        simpa [dirVec_component0, h_sin, h_nv1] using by ring
      · have h_cos : Real.cos L.gridAngle = (L.normalVector) 0 := by
          have h_eq1 : (normalVec L.gridAngle) 0 = (L.normalVector) 0 := by
            exact congr_arg (fun p : Point => p 0) h_nv
          simpa [normalVec_component0] using h_eq1
        have h_nv0 : (L.normalVector) 0 = L.unitDirection 1 := by exact normalVector_component0 L
        simpa [dirVec_component1, h_cos, h_nv0] using rfl
    rw [L.direction_eq_span_unit, h1]
  · -- normalVec gridAngle = -L.normalVector
    have h_nv : normalVec L.gridAngle = -L.normalVector := h.1
    have h1 : dirVec L.gridAngle = -L.unitDirection := by
      ext i
      fin_cases i
      · have h_sin : Real.sin L.gridAngle = (-L.normalVector) 1 := by
          have h_eq1 : (normalVec L.gridAngle) 1 = (-L.normalVector) 1 := by
            exact congr_arg (fun p : Point => p 1) h_nv
          simpa [normalVec_component1] using h_eq1
        have h_nv1 : (L.normalVector) 1 = -L.unitDirection 0 := by exact normalVector_component1 L
        simpa [dirVec_component0, h_sin, h_nv1] using by ring
      · have h_cos : Real.cos L.gridAngle = (-L.normalVector) 0 := by
          have h_eq1 : (normalVec L.gridAngle) 0 = (-L.normalVector) 0 := by
            exact congr_arg (fun p : Point => p 0) h_nv
          simpa [normalVec_component0] using h_eq1
        have h_nv0 : (L.normalVector) 0 = L.unitDirection 1 := by exact normalVector_component0 L
        simpa [dirVec_component1, h_cos, h_nv0] using by ring
    rw [L.direction_eq_span_unit, h1]
    have h_span : Submodule.span ℝ ({L.unitDirection} : Set Point) = Submodule.span ℝ ({-L.unitDirection} : Set Point) := by
      let S1 := Submodule.span ℝ ({L.unitDirection} : Set Point)
      let S2 := Submodule.span ℝ ({-L.unitDirection} : Set Point)
      apply le_antisymm
      · have h_neg_in_S2 : -L.unitDirection ∈ S2 := by
          apply Submodule.subset_span
          simp
        have h_v_in_S2 : L.unitDirection ∈ S2 := by
          have h_eq : L.unitDirection = (-1 : ℝ) • (-L.unitDirection) := by simp
          rw [h_eq]
          exact S2.smul_mem (-1 : ℝ) h_neg_in_S2
        exact Submodule.span_le.mpr (fun x hx => by
          simp only [Set.mem_singleton_iff] at hx
          rw [hx]
          exact h_v_in_S2)
      · have h_v_in_S1 : L.unitDirection ∈ S1 := by
          apply Submodule.subset_span
          simp
        have h_negv_in_S1 : -L.unitDirection ∈ S1 := by
          have h_eq : -L.unitDirection = (-1 : ℝ) • L.unitDirection := by simp
          rw [h_eq]
          exact S1.smul_mem (-1 : ℝ) h_v_in_S1
        exact Submodule.span_le.mpr (fun x hx => by
          simp only [Set.mem_singleton_iff] at hx
          rw [hx]
          exact h_negv_in_S1)
    exact h_span

/-- If two lineOfAngleOffset lines with angles in [0, π) are equal, their angles are equal. -/
lemma lineOfAngleOffset_angle_injective {θ1 θ2 a1 a2 : ℝ}
    (hθ1 : 0 ≤ θ1) (hθ2 : θ1 < Real.pi)
    (hθ3 : 0 ≤ θ2) (hθ4 : θ2 < Real.pi)
    (h : lineOfAngleOffset θ1 a1 = lineOfAngleOffset θ2 a2) : θ1 = θ2 := by
  have h_dir_eq : (lineOfAngleOffset θ1 a1).toAffine.direction =
      (lineOfAngleOffset θ2 a2).toAffine.direction := by
    rw [h]
  have h1 : (lineOfAngleOffset θ1 a1).toAffine.direction = Submodule.span ℝ ({dirVec θ1} : Set Point) :=
    lineOfAngleOffset_aff_direction θ1 a1
  have h2 : (lineOfAngleOffset θ2 a2).toAffine.direction = Submodule.span ℝ ({dirVec θ2} : Set Point) :=
    lineOfAngleOffset_aff_direction θ2 a2
  rw [h1, h2] at h_dir_eq
  have h3 : dirVec θ1 ∈ Submodule.span ℝ ({dirVec θ2} : Set Point) := by
    rw [←h_dir_eq] <;> exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
  rcases Submodule.mem_span_singleton.mp h3 with ⟨c, hc⟩
  have h4 : dirVec θ1 = c • dirVec θ2 := hc.symm
  have h5 : ‖dirVec θ1‖ = 1 := norm_dirVec θ1
  have h6 : ‖dirVec θ2‖ = 1 := norm_dirVec θ2
  have h7 : |c| = 1 := by
    have h8 : ‖dirVec θ1‖ = |c| * ‖dirVec θ2‖ := by
      rw [h4, norm_smul, Real.norm_eq_abs] <;> ring
    rw [h5, h6] at h8 <;> linarith
  have hc1 : c = 1 ∨ c = -1 := by
    by_cases hnonneg : 0 ≤ c
    · have h' : c = 1 := by rw [abs_of_nonneg hnonneg] at h7 <;> linarith
      exact Or.inl h'
    · have hneg : c < 0 := by linarith
      have h' : c = -1 := by rw [abs_of_neg hneg] at h7 <;> linarith
      exact Or.inr h'
  rcases hc1 with (hc1 | hc1)
  · -- c = 1
    have h_eq : dirVec θ1 = dirVec θ2 := by rw [h4, hc1] <;> simp
    have hcos : Real.cos θ1 = Real.cos θ2 := by
      have h11 : (dirVec θ1) 1 = (dirVec θ2) 1 := by rw [h_eq]
      simpa [dirVec_component1] using h11
    have h_inj : θ1 = θ2 := by
      by_contra hne
      have h_lt_or_gt : θ1 < θ2 ∨ θ2 < θ1 := lt_or_gt_of_ne hne
      rcases h_lt_or_gt with (h_lt | h_gt)
      · have h' : Real.cos θ2 < Real.cos θ1 :=
          Real.cos_lt_cos_of_nonneg_of_le_pi hθ1 (by linarith [Real.pi_pos]) h_lt
        linarith [hcos]
      · have h' : Real.cos θ1 < Real.cos θ2 :=
          Real.cos_lt_cos_of_nonneg_of_le_pi hθ3 (by linarith [Real.pi_pos]) h_gt
        linarith [hcos]
    exact h_inj
  · -- c = -1
    have h_eq : dirVec θ1 = -dirVec θ2 := by rw [h4, hc1] <;> simp
    have hsin1 : Real.sin θ1 = -Real.sin θ2 := by
      have h11 : (dirVec θ1) 0 = (-dirVec θ2) 0 := by rw [h_eq]
      have h12 : (dirVec θ1) 0 = -Real.sin θ1 := dirVec_component0 θ1
      have h13 : (-dirVec θ2) 0 = Real.sin θ2 := by
        simp [dirVec_component0] <;> ring
      rw [h12, h13] at h11
      linarith
    have h_sin_nonneg1 : 0 ≤ Real.sin θ1 := Real.sin_nonneg_of_mem_Icc ⟨hθ1, by linarith [Real.pi_pos]⟩
    have h_sin_nonneg2 : 0 ≤ Real.sin θ2 := Real.sin_nonneg_of_mem_Icc ⟨hθ3, by linarith [Real.pi_pos]⟩
    have h_sin_eq : Real.sin θ1 = 0 := by linarith
    have h_sin2_eq : Real.sin θ2 = 0 := by linarith
    have hθ1_0 : θ1 = 0 := by
      by_cases hpos : 0 < θ1
      · have h : 0 < Real.sin θ1 := Real.sin_pos_of_pos_of_lt_pi hpos hθ2
        linarith [h_sin_eq]
      · have h' : θ1 = 0 := by linarith [hθ1]
        exact h'
    have hθ2_0 : θ2 = 0 := by
      by_cases hpos : 0 < θ2
      · have h : 0 < Real.sin θ2 := Real.sin_pos_of_pos_of_lt_pi hpos hθ4
        linarith [h_sin2_eq]
      · have h' : θ2 = 0 := by linarith [hθ3]
        exact h'
    linarith

/-- If two lines have direction distance ≥ r/8, their grid images are distinct. -/
lemma gridMap_injective (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (hxBall : x ∈ closedBall (0 : Point) 1)
    (L1 L2 : Line2) (hx1 : x ∈ tube r L1) (hx2 : x ∈ tube r L2)
    (h_sep : r / 8 ≤ lineDirDist L1 L2) :
    gridMap r hr hr1 x hxBall L1 hx1 ≠ gridMap r hr hr1 x hxBall L2 hx2 := by
  dsimp only [gridMap]
  let θ1 : ℝ := L1.gridAngle
  let a1 : ℝ := L1.gridOffset
  let k1 : ℕ := gridAngleIndex r θ1
  let j1 : ℕ := gridOffsetIndex r a1
  let θ2 : ℝ := L2.gridAngle
  let a2 : ℝ := L2.gridOffset
  let k2 : ℕ := gridAngleIndex r θ2
  let j2 : ℕ := gridOffsetIndex r a2
  have hθ1_1 : 0 ≤ θ1 := L1.gridAngle_nonneg
  have hθ1_2 : θ1 < Real.pi := L1.gridAngle_lt_pi
  have hθ2_1 : 0 ≤ θ2 := L2.gridAngle_nonneg
  have hθ2_2 : θ2 < Real.pi := L2.gridAngle_lt_pi
  intro h_eq
  have h_nat_pos : 0 < (numAngles r : ℝ) := by
    have h : 0 < numAngles r := Nat.ceil_pos.mpr (div_pos Real.pi_pos (by dsimp only [delta]; positivity))
    exact_mod_cast h
  have h_angles_eq : angleVal r k1 = angleVal r k2 := by
    have h : lineOfAngleOffset (angleVal r k1) (offsetVal r j1) =
        lineOfAngleOffset (angleVal r k2) (offsetVal r j2) := h_eq
    have h_k1_in : k1 ∈ angleSet r := gridAngleIndex_mem r hr θ1 hθ1_1 hθ1_2
    have h_k2_in : k2 ∈ angleSet r := gridAngleIndex_mem r hr θ2 hθ2_1 hθ2_2
    have h1 : 0 ≤ angleVal r k1 := by
      dsimp only [angleVal]
      have h_k_nonneg : 0 ≤ (k1 : ℝ) := by exact_mod_cast Nat.zero_le k1
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_nat_nonneg : 0 ≤ (numAngles r : ℝ) := by exact_mod_cast Nat.zero_le (numAngles r)
      positivity
    have h2 : angleVal r k1 < Real.pi := by
      dsimp only [angleVal]
      have h_k_lt : k1 < numAngles r := Finset.mem_range.mp h_k1_in
      have h_k_lt' : (k1 : ℝ) < (numAngles r : ℝ) := by exact_mod_cast h_k_lt
      have h_pos : 0 < (numAngles r : ℝ) := h_nat_pos
      calc (k1 : ℝ) * Real.pi / (numAngles r : ℝ)
        = ((k1 : ℝ) / (numAngles r : ℝ)) * Real.pi := by ring
      _ < 1 * Real.pi := by gcongr <;> exact (div_lt_one h_pos).mpr h_k_lt'
      _ = Real.pi := by ring
    have h3 : 0 ≤ angleVal r k2 := by
      dsimp only [angleVal]
      have h_k_nonneg : 0 ≤ (k2 : ℝ) := by exact_mod_cast Nat.zero_le k2
      have h_pi_pos : 0 < Real.pi := Real.pi_pos
      have h_nat_nonneg : 0 ≤ (numAngles r : ℝ) := by exact_mod_cast Nat.zero_le (numAngles r)
      positivity
    have h4 : angleVal r k2 < Real.pi := by
      dsimp only [angleVal]
      have h_k_lt : k2 < numAngles r := Finset.mem_range.mp h_k2_in
      have h_k_lt' : (k2 : ℝ) < (numAngles r : ℝ) := by exact_mod_cast h_k_lt
      have h_pos : 0 < (numAngles r : ℝ) := h_nat_pos
      calc (k2 : ℝ) * Real.pi / (numAngles r : ℝ)
        = ((k2 : ℝ) / (numAngles r : ℝ)) * Real.pi := by ring
      _ < 1 * Real.pi := by gcongr <;> exact (div_lt_one h_pos).mpr h_k_lt'
      _ = Real.pi := by ring
    exact lineOfAngleOffset_angle_injective h1 h2 h3 h4 h
  have h_k_eq : k1 = k2 := by
    have h5 : (k1 : ℝ) * Real.pi / (numAngles r : ℝ) = (k2 : ℝ) * Real.pi / (numAngles r : ℝ) := h_angles_eq
    have h_pos : 0 < (numAngles r : ℝ) := h_nat_pos
    have h6 : (k1 : ℝ) * Real.pi = (k2 : ℝ) * Real.pi := by
      field_simp [h_pos.ne'] at h5 ⊢ <;> exact h5
    have h7 : (k1 : ℝ) = (k2 : ℝ) := by
      apply (mul_right_inj' Real.pi_pos.ne').mp
      have h8 : Real.pi * (k1 : ℝ) = Real.pi * (k2 : ℝ) := by
        rw [mul_comm Real.pi (k1 : ℝ), mul_comm Real.pi (k2 : ℝ)]
        exact h6
      exact h8
    exact_mod_cast h7
  have h_bin1 : angleVal r k1 ≤ θ1 ∧ θ1 < angleVal r k1 + Real.pi / (numAngles r : ℝ) :=
    gridAngleIndex_bin r hr θ1 hθ1_1 hθ1_2
  have h_bin2 : angleVal r k2 ≤ θ2 ∧ θ2 < angleVal r k2 + Real.pi / (numAngles r : ℝ) :=
    gridAngleIndex_bin r hr θ2 hθ2_1 hθ2_2
  have h_bin2' : angleVal r k1 ≤ θ2 ∧ θ2 < angleVal r k1 + Real.pi / (numAngles r : ℝ) := by
    have h_k2_eq : k2 = k1 := h_k_eq.symm
    rw [h_k2_eq] at h_bin2
    exact h_bin2
  have h_angle_diff : |θ1 - θ2| < Real.pi / (numAngles r : ℝ) := by
    have h1 : θ1 - θ2 < Real.pi / (numAngles r : ℝ) := by linarith [h_bin1.2, h_bin2'.1]
    have h2 : -(Real.pi / (numAngles r : ℝ)) < θ1 - θ2 := by linarith [h_bin1.1, h_bin2'.2]
    have h3 : 0 < Real.pi / (numAngles r : ℝ) := by positivity
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h_pi_le_delta : Real.pi / (numAngles r : ℝ) ≤ delta r := by
    have h1 : Real.pi / delta r ≤ (numAngles r : ℝ) := by
      dsimp only [numAngles]; exact Nat.le_ceil (Real.pi / delta r)
    have h2 : 0 < delta r := by dsimp only [delta]; positivity
    have h3 : 0 < (numAngles r : ℝ) := by
      have h4 : 0 < Real.pi / delta r := div_pos Real.pi_pos h2
      have h5 : 0 < numAngles r := Nat.ceil_pos.mpr h4
      exact_mod_cast h5
    calc Real.pi / (numAngles r : ℝ)
      ≤ Real.pi / (Real.pi / delta r) := by gcongr
    _ = delta r := by field_simp [h2.ne'] <;> ring
  have h_angle_bound : |θ1 - θ2| < r / 10 := by
    calc |θ1 - θ2|
      < Real.pi / (numAngles r : ℝ) := h_angle_diff
    _ ≤ delta r := h_pi_le_delta
    _ = r / 10 := by dsimp only [delta] <;> ring
  have h_case1 := L1.gridAngle_case
  have h_case2 := L2.gridAngle_case
  have h_nc1 : normalVec θ1 = L1.normalVector ∨ normalVec θ1 = -L1.normalVector := by
    rcases h_case1 with (h | h) <;> [exact Or.inl h.1; exact Or.inr h.1]
  have h_dir_eq : L2.toAffine.direction = (lineOfAngleOffset θ2 a2).toAffine.direction := by
    have h_dir3 : (lineOfAngleOffset θ2 a2).toAffine.direction = Submodule.span ℝ {dirVec θ2} :=
      lineOfAngleOffset_aff_direction θ2 a2
    rw [L2.gridAngle_direction, h_dir3]
  have h_dir_dist : lineDirDist L1 L2 ≤ |θ1 - θ2| := by
    have h_eq2 : lineDirDist L1 L2 = lineDirDist L1 (lineOfAngleOffset θ2 a2) := by
      rw [lineDirDist, lineDirDist, h_dir_eq]
    rw [h_eq2]
    exact B1.lineDirDist_to_grid_angle_bound L1 θ1 h_nc1 θ2 a2
  have h_contra : lineDirDist L1 L2 < r / 8 := by
    calc lineDirDist L1 L2
      ≤ |θ1 - θ2| := h_dir_dist
    _ < r / 10 := h_angle_bound
    _ < r / 8 := by linarith [hr]
  linarith [h_sep]

end RadialBootstrapping
