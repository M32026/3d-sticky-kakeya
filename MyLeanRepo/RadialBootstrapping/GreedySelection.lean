module

public import MyLeanRepo.RadialBootstrapping.BoundedOverlap

@[expose] public section

/-!
# Greedy Selection of Direction-Separated Lines Through a Point

Main results:
- `greedy_selection_finite` — maximal δ-separated subset of a finite family
- `direction_separated_card_bound` — cardinality ≤ π/δ + 2 for δ ∈ (0,1]
-/

open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

attribute [local instance] Classical.propDecidable

-- ============================================================================
-- 1. Unit vector from a 1D submodule
-- ============================================================================

lemma submodule_one_dim_exists_nonzero (V : Submodule ℝ Point)
    (hV : Module.finrank ℝ V = 1) : ∃ (v : Point), v ∈ V ∧ v ≠ 0 := by
  have hV_pos : 0 < Module.finrank ℝ V := by rw [hV] <;> norm_num
  have h : (V : Set Point).Nonempty := by exact Submodule.nonempty V
  by_contra h2
  push Not at h2
  have hV_bot : V = (⊥ : Submodule ℝ Point) := by
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · intro hx; exact h2 x hx
    · intro hx; rw [hx]; exact Submodule.zero_mem V
  rw [hV_bot] at hV_pos
  simp at hV_pos

def getUnitVector (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) : Point :=
  let v := Classical.choose (submodule_one_dim_exists_nonzero V hV)
  (1 / ‖v‖) • v

lemma getUnitVector_mem (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    getUnitVector V hV ∈ V := by
  dsimp only [getUnitVector]
  set v := Classical.choose (submodule_one_dim_exists_nonzero V hV) with hv
  have hspec : v ∈ V ∧ v ≠ 0 := Classical.choose_spec (submodule_one_dim_exists_nonzero V hV)
  have hvV : v ∈ V := hspec.1
  exact V.smul_mem (1 / ‖v‖) hvV

lemma getUnitVector_norm (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    ‖getUnitVector V hV‖ = 1 := by
  dsimp only [getUnitVector]
  set v := Classical.choose (submodule_one_dim_exists_nonzero V hV) with hv
  have hspec : v ∈ V ∧ v ≠ 0 := Classical.choose_spec (submodule_one_dim_exists_nonzero V hV)
  have hv0 : v ≠ 0 := hspec.2
  have h_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [norm_smul, Real.norm_eq_abs]
  have h_abs : |(1 : ℝ) / ‖v‖| = 1 / ‖v‖ := by
    rw [abs_of_pos (div_pos zero_lt_one h_pos)]
  rw [h_abs]
  field_simp [h_pos.ne'] <;> ring

-- ============================================================================
-- 2. Greedy selection (finite version)
-- ============================================================================

lemma greedy_selection_finite (x : Point) (S : Finset Line2)
    (hS : ∀ L ∈ S, x ∈ L.toSet) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (T_x : Finset Line2),
      T_x ⊆ S ∧
      (∀ L1 ∈ T_x, ∀ L2 ∈ T_x, L1 ≠ L2 → lineDirDist L1 L2 ≥ δ) ∧
      (∀ L ∈ S, ∃ L' ∈ T_x, lineDirDist L L' < δ) := by
  let separated (T : Finset Line2) : Prop :=
    ∀ L1 ∈ T, ∀ L2 ∈ T, L1 ≠ L2 → lineDirDist L1 L2 ≥ δ
  let candidates : Finset (Finset Line2) := S.powerset.filter separated
  have h_nonempty : candidates.Nonempty := ⟨∅, by simp [candidates, separated]⟩
  rcases candidates.exists_max_image (fun T : Finset Line2 => T.card) h_nonempty
    with ⟨T_x, hTx_mem, hTx_max⟩
  have hTx_sub : T_x ⊆ S := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hTx_mem).1
  have hTx_sep : separated T_x := (Finset.mem_filter.mp hTx_mem).2
  have h_cover : ∀ L ∈ S, ∃ L' ∈ T_x, lineDirDist L L' < δ := by
    intro L hL
    by_contra h
    push Not at h
    have hL_notin : L ∉ T_x := by
      intro hL_in
      have h' : δ ≤ lineDirDist L L := h L hL_in
      have h0 : lineDirDist L L = 0 := submoduleDirDist_self _
      rw [h0] at h'
      have h_false : ¬(0 : ℝ) ≥ δ := by simpa using hδ
      exact h_false h'
    let T_x' := insert L T_x
    have hT_x'_sub : T_x' ⊆ S := by
      intro z hz
      simp only [T_x', Finset.mem_insert] at hz
      rcases hz with (rfl | hz)
      · exact hL
      · exact hTx_sub hz
    have hT_x'_sep : separated T_x' := by
      intro L1 hL1 L2 hL2 hne
      have h1 : L1 = L ∨ L1 ∈ T_x := by simpa [T_x'] using hL1
      have h2 : L2 = L ∨ L2 ∈ T_x := by simpa [T_x'] using hL2
      cases h1 with
      | inl h1eq =>
        cases h2 with
        | inl h2eq =>
          exfalso; exact hne (by rw [h1eq, h2eq])
        | inr h2in =>
          rw [h1eq]; exact h L2 h2in
      | inr h1in =>
        cases h2 with
        | inl h2eq =>
          rw [h2eq]
          have h' : δ ≤ lineDirDist L L1 := h L1 h1in
          have h_sym : lineDirDist L1 L = lineDirDist L L1 := submoduleDirDist_comm _ _
          rw [h_sym]; exact h'
        | inr h2in =>
          exact hTx_sep L1 h1in L2 h2in hne
    have hT_x'_mem : T_x' ∈ candidates := by
      rw [Finset.mem_filter] <;> exact ⟨Finset.mem_powerset.mpr hT_x'_sub, hT_x'_sep⟩
    have h_card : T_x.card < T_x'.card := by
      rw [Finset.card_insert_of_notMem hL_notin] <;> simp
    have h_max : T_x'.card ≤ T_x.card := hTx_max T_x' hT_x'_mem
    linarith
  exact ⟨T_x, hTx_sub, hTx_sep, h_cover⟩

-- ============================================================================
-- 3. Angle parameterization of directions
-- ============================================================================

def canonicalVector (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) : Point :=
  let u := getUnitVector V hV
  if u 1 ≥ 0 then u else -u

lemma canonicalVector_mem (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    canonicalVector V hV ∈ V := by
  dsimp only [canonicalVector]
  have huV : getUnitVector V hV ∈ V := getUnitVector_mem V hV
  split_ifs with h
  · exact huV
  · exact V.neg_mem huV

lemma canonicalVector_norm (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    ‖canonicalVector V hV‖ = 1 := by
  dsimp only [canonicalVector]
  have hnu : ‖getUnitVector V hV‖ = 1 := getUnitVector_norm V hV
  split_ifs with h
  · exact hnu
  · rw [norm_neg]; exact hnu

lemma canonicalVector_y_nonneg (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    (canonicalVector V hV) 1 ≥ 0 := by
  dsimp only [canonicalVector]
  split_ifs with h
  · exact h
  · have h' : ¬(getUnitVector V hV) 1 ≥ 0 := h
    have h'' : (getUnitVector V hV) 1 < 0 := by linarith
    simp [h''] <;> linarith

def directionAngle (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) : ℝ :=
  Real.arccos ((canonicalVector V hV) 0)

lemma directionAngle_range (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    0 ≤ directionAngle V hV ∧ directionAngle V hV ≤ Real.pi := by
  dsimp only [directionAngle]
  have h2 : (canonicalVector V hV) 0 ^ 2 ≤ ‖canonicalVector V hV‖ ^ 2 := by
    rw [norm_sq_fin2] <;> nlinarith
  rw [canonicalVector_norm] at h2
  have h1 : -1 ≤ (canonicalVector V hV) 0 := by nlinarith
  have h3 : (canonicalVector V hV) 0 ≤ 1 := by nlinarith
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

lemma canonicalVector_cos (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    (canonicalVector V hV) 0 = Real.cos (directionAngle V hV) := by
  dsimp only [directionAngle]
  have h2 : (canonicalVector V hV) 0 ^ 2 ≤ ‖canonicalVector V hV‖ ^ 2 := by
    rw [norm_sq_fin2] <;> nlinarith
  rw [canonicalVector_norm] at h2
  have h1 : -1 ≤ (canonicalVector V hV) 0 := by nlinarith
  have h3 : (canonicalVector V hV) 0 ≤ 1 := by nlinarith
  rw [Real.cos_arccos h1 h3]

lemma canonicalVector_sin (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) :
    (canonicalVector V hV) 1 = Real.sin (directionAngle V hV) := by
  dsimp only [directionAngle]
  let u := canonicalVector V hV
  have hnu : ‖u‖ = 1 := canonicalVector_norm V hV
  have h_coord : (u 0) ^ 2 + (u 1) ^ 2 = 1 := coords_norm_one u hnu
  have h4 : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - (u 0) ^ 2) := by
    rw [Real.sin_arccos] <;> nlinarith
  rw [h4]
  have h5 : 1 - (u 0) ^ 2 = (u 1) ^ 2 := by linarith
  rw [h5, Real.sqrt_sq_eq_abs, abs_of_nonneg (canonicalVector_y_nonneg V hV)] <;> rfl

-- ============================================================================
-- 4. Direction distance in terms of angles
-- ============================================================================

lemma dirDist_eq_abs_sin (V1 V2 : Submodule ℝ Point)
    (hV1 : Module.finrank ℝ V1 = 1) (hV2 : Module.finrank ℝ V2 = 1) :
    submoduleDirDist V1 V2 = |Real.sin (directionAngle V1 hV1 - directionAngle V2 hV2)| := by
  let u1 := canonicalVector V1 hV1
  let u2 := canonicalVector V2 hV2
  have h11 : u1 ∈ V1 := canonicalVector_mem V1 hV1
  have h12 : ‖u1‖ = 1 := canonicalVector_norm V1 hV1
  have h_id : submoduleDirDist V1 V2 = ‖u2 - V1.orthogonalProjectionFn u2‖ :=
    submoduleDirDist_eq_perp V1 V2 hV1 hV2 u2 (canonicalVector_mem V2 hV2)
      (canonicalVector_norm V2 hV2)
  have hproj : V1.orthogonalProjectionFn u2 = inner ℝ u2 u1 • u1 :=
    projection_one_dim V1 u1 u2 h11 h12 hV1
  set y : ℝ := directionAngle V2 hV2 - directionAngle V1 hV1 with hy
  have h_inner : inner ℝ u2 u1 = Real.cos y := by
    have hc2 : u2 0 = Real.cos (directionAngle V2 hV2) := canonicalVector_cos V2 hV2
    have hs2 : u2 1 = Real.sin (directionAngle V2 hV2) := canonicalVector_sin V2 hV2
    have hc1 : u1 0 = Real.cos (directionAngle V1 hV1) := canonicalVector_cos V1 hV1
    have hs1 : u1 1 = Real.sin (directionAngle V1 hV1) := canonicalVector_sin V1 hV1
    have h : inner ℝ u2 u1 = u2 0 * u1 0 + u2 1 * u1 1 := by
      rw [inner_fin2] <;> ring
    rw [h, hc2, hs2, hc1, hs1, hy, Real.cos_sub] <;> ring
  have h_main : ‖u2 - inner ℝ u2 u1 • u1‖ = Real.sqrt (1 - (inner ℝ u2 u1) ^ 2) := by
    have h_norm : ‖u2 - inner ℝ u2 u1 • u1‖ ^ 2 = 1 - (inner ℝ u2 u1) ^ 2 := by
      have h5 : ‖u2 - inner ℝ u2 u1 • u1‖ ^ 2 =
          ‖u2‖ ^ 2 + ‖inner ℝ u2 u1 • u1‖ ^ 2 - 2 * inner ℝ u2 (inner ℝ u2 u1 • u1) := by
        have h51 := norm_sub_sq_real u2 (inner ℝ u2 u1 • u1); linarith
      rw [h5]
      have h7 : ‖inner ℝ u2 u1 • u1‖ ^ 2 = (inner ℝ u2 u1) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, h12] <;> simp [sq_abs]
      have h8 : inner ℝ u2 (inner ℝ u2 u1 • u1) = (inner ℝ u2 u1) ^ 2 := by
        rw [inner_smul_right] <;> ring
      rw [h7, h8, canonicalVector_norm V2 hV2] <;> ring
    have h_nonneg : 0 ≤ ‖u2 - inner ℝ u2 u1 • u1‖ := by positivity
    rw [← Real.sqrt_sq h_nonneg, h_norm]
  calc
    submoduleDirDist V1 V2
      = ‖u2 - V1.orthogonalProjectionFn u2‖ := h_id
    _ = ‖u2 - inner ℝ u2 u1 • u1‖ := by rw [hproj]
    _ = Real.sqrt (1 - (inner ℝ u2 u1) ^ 2) := h_main
    _ = Real.sqrt (1 - Real.cos y ^ 2) := by rw [h_inner]
    _ = Real.sqrt (Real.sin y ^ 2) := by
      have h12 : Real.cos y ^ 2 + Real.sin y ^ 2 = 1 := Real.cos_sq_add_sin_sq y
      have h13 : 1 - Real.cos y ^ 2 = Real.sin y ^ 2 := by linarith
      rw [h13]
    _ = |Real.sin y| := by rw [Real.sqrt_sq_eq_abs]
    _ = |Real.sin (directionAngle V1 hV1 - directionAngle V2 hV2)| := by
      have h14 : Real.sin y = Real.sin (directionAngle V2 hV2 - directionAngle V1 hV1) := by rfl
      rw [h14]
      have h15 : |Real.sin (directionAngle V2 hV2 - directionAngle V1 hV1)| =
          |Real.sin (directionAngle V1 hV1 - directionAngle V2 hV2)| := by
        have h16 : Real.sin (directionAngle V2 hV2 - directionAngle V1 hV1) =
            -Real.sin (directionAngle V1 hV1 - directionAngle V2 hV2) := by
          rw [show directionAngle V2 hV2 - directionAngle V1 hV1 =
              -(directionAngle V1 hV1 - directionAngle V2 hV2) by ring]
          rw [Real.sin_neg] <;> ring
        rw [h16, abs_neg]
      exact h15

-- ============================================================================
-- 5. Cardinality bound for δ-separated directions
-- ============================================================================

lemma direction_separated_card_bound {T : Finset Line2} {x : Point} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : ∀ L ∈ T, x ∈ L.toSet)
    (h_sep : ∀ L1 ∈ T, ∀ L2 ∈ T, L1 ≠ L2 → lineDirDist L1 L2 ≥ δ) :
    (T.card : ℝ) ≤ Real.pi / δ + 2 := by
  let θ : Line2 → ℝ := fun L => directionAngle L.toAffine.direction L.2
  let ψ : Line2 → ℝ := fun L => θ L - Real.pi / 2
  let T1 : Finset Line2 := T.filter (fun L => θ L ≤ Real.pi / 2)
  let T2 : Finset Line2 := T.filter (fun L => θ L ≥ Real.pi / 2)
  have h1_sub : T1 ⊆ T := Finset.filter_subset _ _
  have h2_sub : T2 ⊆ T := Finset.filter_subset _ _

  have h_abs_sin : ∀ (y : ℝ), |y| ≤ Real.pi / 2 → |Real.sin y| = Real.sin |y| := by
    intro y hy
    by_cases hy' : 0 ≤ y
    · have h3 : 0 ≤ Real.sin y := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [abs_le.mp hy]⟩
      rw [abs_of_nonneg h3, abs_of_nonneg hy']
    · have h1 : y < 0 := by exact lt_of_not_ge hy'
      have h4 : 0 ≤ -y := by linarith
      have h5 : -y ≤ Real.pi / 2 := by linarith [abs_le.mp hy]
      have h7 : 0 ≤ Real.sin (-y) := Real.sin_nonneg_of_mem_Icc ⟨h4, by linarith⟩
      have h8 : Real.sin y ≤ 0 := by
        have h9 : Real.sin (-y) = -Real.sin y := Real.sin_neg y
        rw [h9] at h7; linarith
      rw [abs_of_nonpos h8, abs_of_neg h1]
      have h10 : Real.sin (-y) = -Real.sin y := Real.sin_neg y
      rw [h10] <;> ring

  have h_sep_from_angle : ∀ (L1 L2 : Line2), L1 ∈ T → L2 ∈ T → L1 ≠ L2 →
      (θ L1 ≤ Real.pi / 2 → θ L2 ≤ Real.pi / 2 → |θ L1 - θ L2| ≥ δ) ∧
      (θ L1 ≥ Real.pi / 2 → θ L2 ≥ Real.pi / 2 → |θ L1 - θ L2| ≥ δ) := by
    intro L1 L2 hL1' hL2' hne
    have h_dist : lineDirDist L1 L2 ≥ δ := h_sep L1 hL1' L2 hL2' hne
    have h_eq : lineDirDist L1 L2 = |Real.sin (θ L1 - θ L2)| :=
      dirDist_eq_abs_sin L1.toAffine.direction L2.toAffine.direction L1.2 L2.2
    rw [h_eq] at h_dist
    constructor
    · intro h1 h2
      have h_θ1_nonneg : 0 ≤ θ L1 := (directionAngle_range _ _).1
      have h_θ2_nonneg : 0 ≤ θ L2 := (directionAngle_range _ _).1
      have h_diff_range : |θ L1 - θ L2| ≤ Real.pi / 2 := by
        rw [abs_le] <;> constructor <;> linarith
      rw [h_abs_sin (θ L1 - θ L2) h_diff_range] at h_dist
      have h_sin_le : Real.sin |θ L1 - θ L2| ≤ |θ L1 - θ L2| := Real.sin_le (abs_nonneg _)
      linarith
    · intro h1 h2
      have h_θ1_le : θ L1 ≤ Real.pi := (directionAngle_range _ _).2
      have h_θ2_le : θ L2 ≤ Real.pi := (directionAngle_range _ _).2
      have h_diff_range : |θ L1 - θ L2| ≤ Real.pi / 2 := by
        rw [abs_le] <;> constructor <;> linarith
      rw [h_abs_sin (θ L1 - θ L2) h_diff_range] at h_dist
      have h_sin_le : Real.sin |θ L1 - θ L2| ≤ |θ L1 - θ L2| := Real.sin_le (abs_nonneg _)
      linarith

  let s1 : Finset ℝ := T1.image θ
  let s2 : Finset ℝ := T2.image ψ
  have hlo1 : ∀ x ∈ s1, 0 ≤ x := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨L, _, rfl⟩; exact (directionAngle_range _ _).1
  have hhi1 : ∀ x ∈ s1, x ≤ Real.pi / 2 := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨L, hL, rfl⟩; exact (Finset.mem_filter.mp hL).2
  have hlo2 : ∀ x ∈ s2, 0 ≤ x := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨L, hL, rfl⟩
    have h : θ L ≥ Real.pi / 2 := (Finset.mem_filter.mp hL).2
    simp only [ψ, sub_nonneg] <;> linarith
  have hhi2 : ∀ x ∈ s2, x ≤ Real.pi / 2 := by
    intro x hx; rcases Finset.mem_image.mp hx with ⟨L, hL, rfl⟩
    have h : θ L ≤ Real.pi := (directionAngle_range _ _).2
    simp only [ψ] <;> linarith

  have hT1_sep : ∀ (a : ℝ), a ∈ s1 → ∀ (b : ℝ), b ∈ s1 → a ≠ b → |a - b| ≥ δ := by
    intro a ha b hb hne
    rcases Finset.mem_image.mp ha with ⟨L1, hL1, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨L2, hL2, rfl⟩
    have hL1' : L1 ∈ T := h1_sub hL1
    have hL2' : L2 ∈ T := h1_sub hL2
    have hne' : L1 ≠ L2 := by intro h; rw [h] at hne; simpa using hne
    exact (h_sep_from_angle L1 L2 hL1' hL2' hne').1
      ((Finset.mem_filter.mp hL1).2) ((Finset.mem_filter.mp hL2).2)

  have hT2_sep : ∀ (a : ℝ), a ∈ s2 → ∀ (b : ℝ), b ∈ s2 → a ≠ b → |a - b| ≥ δ := by
    intro a ha b hb hne
    rcases Finset.mem_image.mp ha with ⟨L1, hL1, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨L2, hL2, rfl⟩
    have hL1' : L1 ∈ T := h2_sub hL1
    have hL2' : L2 ∈ T := h2_sub hL2
    have hne' : L1 ≠ L2 := by intro h; rw [h] at hne; simpa using hne
    have h_eq : |ψ L1 - ψ L2| = |θ L1 - θ L2| := by simp only [ψ] <;> abel_nf
    rw [h_eq]
    exact (h_sep_from_angle L1 L2 hL1' hL2' hne').2
      ((Finset.mem_filter.mp hL1).2) ((Finset.mem_filter.mp hL2).2)

  have h_inj1 : Set.InjOn θ (T1 : Set Line2) := by
    intro L1 hL1 L2 hL2 h
    by_contra hne
    have h_dist : lineDirDist L1 L2 ≥ δ := h_sep L1 (h1_sub hL1) L2 (h1_sub hL2) hne
    have h9 : directionAngle L1.toAffine.direction L1.2 = directionAngle L2.toAffine.direction L2.2 := by
      simpa [θ] using h
    have h_eq0 : lineDirDist L1 L2 = 0 := by
      simp only [lineDirDist]
      rw [dirDist_eq_abs_sin L1.toAffine.direction L2.toAffine.direction L1.2 L2.2, h9] <;> simp
    rw [h_eq0] at h_dist
    have h_contra : (0 : ℝ) ≥ δ := h_dist
    have h_false : ¬(0 : ℝ) ≥ δ := by
      simpa using hδ
    exact h_false h_contra

  have h_inj2 : Set.InjOn ψ (T2 : Set Line2) := by
    intro L1 hL1 L2 hL2 h
    by_contra hne
    have h_eqθ : θ L1 = θ L2 := by simp only [ψ] at h <;> linarith
    have h_dist : lineDirDist L1 L2 ≥ δ := h_sep L1 (h2_sub hL1) L2 (h2_sub hL2) hne
    have h9 : directionAngle L1.toAffine.direction L1.2 = directionAngle L2.toAffine.direction L2.2 := by
      simpa [θ] using h_eqθ
    have h_eq0 : lineDirDist L1 L2 = 0 := by
      simp only [lineDirDist]
      rw [dirDist_eq_abs_sin L1.toAffine.direction L2.toAffine.direction L1.2 L2.2, h9] <;> simp
    rw [h_eq0] at h_dist
    have h_contra : (0 : ℝ) ≥ δ := h_dist
    have h_false : ¬(0 : ℝ) ≥ δ := by simpa using hδ
    exact h_false h_contra

  have h_card1 : s1.card = T1.card := Finset.card_image_of_injOn h_inj1
  have h_card2 : s2.card = T2.card := Finset.card_image_of_injOn h_inj2
  have hW : 0 ≤ Real.pi / 2 := by positivity
  have h_pack1 : s1.card ≤ Nat.floor ((Real.pi / 2) / δ) + 1 :=
    real_packing_simple hδ hW hlo1 hhi1 hT1_sep
  have h_pack2 : s2.card ≤ Nat.floor ((Real.pi / 2) / δ) + 1 :=
    real_packing_simple hδ hW hlo2 hhi2 hT2_sep
  have h_union : T ⊆ T1 ∪ T2 := by
    intro L hL
    by_cases h' : θ L ≤ Real.pi / 2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hL, h'⟩)
    · have h'' : θ L ≥ Real.pi / 2 := by linarith
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hL, h''⟩)
  have h_card_le : T.card ≤ (T1 ∪ T2).card := Finset.card_le_card h_union
  have h_card_union : (T1 ∪ T2).card ≤ T1.card + T2.card := Finset.card_union_le _ _
  rw [h_card1] at h_pack1
  rw [h_card2] at h_pack2
  have h_final : T.card ≤ 2 * (Nat.floor ((Real.pi / 2) / δ) + 1) := by
    calc T.card ≤ (T1 ∪ T2).card := h_card_le
         _ ≤ T1.card + T2.card := h_card_union
         _ ≤ (Nat.floor ((Real.pi / 2) / δ) + 1) + (Nat.floor ((Real.pi / 2) / δ) + 1) := by gcongr
         _ = 2 * (Nat.floor ((Real.pi / 2) / δ) + 1) := by ring
  have h_main : (T.card : ℝ) ≤ Real.pi / δ + 2 := by
    calc (T.card : ℝ)
      ≤ (2 * (Nat.floor ((Real.pi / 2) / δ) + 1) : ℕ) := by exact_mod_cast h_final
    _ = 2 * ((Nat.floor ((Real.pi / 2) / δ) : ℝ) + 1) := by simp
    _ ≤ 2 * (((Real.pi / 2) / δ) + 1) := by
      have h_nonneg : 0 ≤ (Real.pi / 2) / δ := by positivity
      have h_floor : (Nat.floor ((Real.pi / 2) / δ) : ℝ) ≤ (Real.pi / 2) / δ :=
        Nat.floor_le h_nonneg
      have h : (Nat.floor ((Real.pi / 2) / δ) : ℝ) + 1 ≤ ((Real.pi / 2) / δ) + 1 := by
        linarith
      exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ = Real.pi / δ + 2 := by field_simp [hδ.ne']
  exact h_main

-- ============================================================================
-- 6. Greedy selection + counting lower bound
-- ============================================================================

/-- Given a δ-separated, δ-covering subfamily `S_y ⊆ T`, and a bound `K` on the
measure of each direction cluster's tube union, derive a lower bound on
`|S_y|`:

    |S_y| ≥ M / K

where `M` is a lower bound on the measure of `⋃_{L ∈ T} tube r L`.

This is the key counting step in the concentrated case (Step 6):
- T_y is a family of tubes through y
- S_y is a maximal δ-separated subfamily (from `greedy_selection_finite`)
- Each direction cluster has measure ≤ K (reverse thin tube bound)
- Total measure ≥ M
- Therefore |S_y| ≥ M / K
-/
lemma greedy_card_lower_bound {T S_y : Finset Line2} {r δ M K : ℝ}
    (hδ : 0 < δ)
    (hS_y_sub : S_y ⊆ T)
    (hS_y_cover : ∀ L ∈ T, ∃ L' ∈ S_y, lineDirDist L L' < δ)
    {ν : Measure Point} (hM : 0 ≤ M) (hK_pos : 0 < K)
    (h_total : ν (⋃ L ∈ T, tube r L) ≥ ENNReal.ofReal M)
    (h_cluster : ∀ L' ∈ S_y,
      ν (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L) ≤ ENNReal.ofReal K) :
    (S_y.card : ℝ) ≥ M / K := by
  have h_cover1 : (⋃ L ∈ T, tube r L) ⊆
      ⋃ L' ∈ S_y, (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L) := by
    intro x hx
    have hx' : ∃ (L : Line2), L ∈ T ∧ x ∈ tube r L := by
      simpa [Finset.mem_coe] using hx
    rcases hx' with ⟨L, hL, hxL⟩
    rcases hS_y_cover L hL with ⟨L', hL', h_close⟩
    have hL_in_filter : L ∈ T.filter (fun L => lineDirDist L L' < δ) := by
      rw [Finset.mem_filter] <;> exact ⟨hL, h_close⟩
    have h_inner : x ∈ (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L) := by
      have h_goal : ∃ (L0 : Line2), L0 ∈ (T.filter (fun L => lineDirDist L L' < δ)) ∧ x ∈ tube r L0 :=
        ⟨L, hL_in_filter, hxL⟩
      exact Set.mem_biUnion hL_in_filter hxL
    have h_outer : x ∈ (⋃ L' ∈ S_y, (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L)) := by
      have h_goal2 : ∃ (L0 : Line2), L0 ∈ S_y ∧ x ∈ (⋃ L ∈ (T.filter (fun L => lineDirDist L L0 < δ)), tube r L) :=
        ⟨L', hL', h_inner⟩
      exact Set.mem_biUnion hL' h_inner
    exact h_outer
  have h1 : ν (⋃ L ∈ T, tube r L) ≤
      ν (⋃ L' ∈ S_y, (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L)) :=
    measure_mono h_cover1
  have h2 : ν (⋃ L' ∈ S_y, (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L)) ≤
      ∑ L' ∈ S_y, ν (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L) :=
    measure_biUnion_finset_le _ _
  have h3 : ∑ L' ∈ S_y, ν (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L) ≤
      ∑ L' ∈ S_y, ENNReal.ofReal K := by
    apply Finset.sum_le_sum
    intro L' hL'
    exact h_cluster L' hL'
  have h4 : ∑ L' ∈ S_y, ENNReal.ofReal K = ENNReal.ofReal (K * (S_y.card : ℝ)) := by
    have h_sum : ∑ L' ∈ S_y, ENNReal.ofReal K = ENNReal.ofReal K * (S_y.card : ENNReal) := by
      rw [Finset.sum_const] <;> ring
    rw [h_sum]
    have h_cast : (S_y.card : ENNReal) = ENNReal.ofReal (S_y.card : ℝ) := by
      simp
    rw [h_cast]
    rw [ENNReal.ofReal_mul (by positivity)] <;> ring
  have h5 : ENNReal.ofReal M ≤ ENNReal.ofReal (K * (S_y.card : ℝ)) := by
    calc ENNReal.ofReal M
      ≤ ν (⋃ L ∈ T, tube r L) := h_total
    _ ≤ ν (⋃ L' ∈ S_y, (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L)) := h1
    _ ≤ ∑ L' ∈ S_y, ν (⋃ L ∈ (T.filter (fun L => lineDirDist L L' < δ)), tube r L) := h2
    _ ≤ ∑ L' ∈ S_y, ENNReal.ofReal K := h3
    _ = ENNReal.ofReal (K * (S_y.card : ℝ)) := h4
  have h6 : M ≤ K * (S_y.card : ℝ) := by
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h5
  have h7 : (S_y.card : ℝ) ≥ M / K := by
    calc (S_y.card : ℝ)
      = (K * (S_y.card : ℝ)) / K := by field_simp [hK_pos.ne'] <;> ring
    _ ≥ M / K := by gcongr
  exact h7

-- ============================================================================
-- 7. Geometric cluster containment
-- ============================================================================

/-- If two lines `L, L'` both pass through `y`, and their direction distance is
at most `δ`, then any point in the `r`-tube of `L` within distance `R` of `y`
is in the `(r + R*δ)`-tube of `L'`.

This is the key geometric fact for direction clustering: a direction ball of
radius `δ` corresponds to a tube of width `r + R*δ` at distance `R` from the
common point. -/
lemma tube_cluster_containment (y : Point) (L L' : Line2) (r R δ : ℝ)
    (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hyL : y ∈ L.toSet) (hyL' : y ∈ L'.toSet)
    (h_dir : lineDirDist L L' ≤ δ) :
    tube r L ∩ Metric.closedBall y R ⊆ tube (r + R * δ) L' := by
  intro z hz
  have hz1 : z ∈ tube r L := hz.1
  have hz2 : z ∈ Metric.closedBall y R := hz.2
  have hnorm : ‖z - y‖ ≤ R := by
    have h : dist z y ≤ R := by simpa [Metric.mem_closedBall] using hz2
    simpa [dist_eq_norm] using h
  let w := z - y
  let V := L.toAffine.direction
  let V' := L'.toAffine.direction
  -- Step 1: infDist z L.toSet < r from tube membership
  have h_infDist_L : Metric.infDist z (L.toSet : Set Point) < r := by
    have htube : z ∈ Metric.thickening r (L.toSet : Set Point) := hz1
    rcases Metric.mem_thickening_iff.mp htube with ⟨z', hz'L, hdist⟩
    have h2 : Metric.infDist z (L.toSet : Set Point) ≤ dist z z' :=
      infDist_le_dist_of_mem hz'L
    exact lt_of_le_of_lt h2 hdist
  -- Step 2: orthogonal projection q of z onto L, and formula q = y + submoduleProj V w
  let q : Point := (EuclideanGeometry.orthogonalProjection L.toAffine z : Point)
  have hq_mem : q ∈ L.toSet := (EuclideanGeometry.orthogonalProjection L.toAffine z).property
  have h_dist_q : dist z q = Metric.infDist z (L.toSet : Set Point) :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist L.toAffine z
  have hV : submoduleProj V = V.starProjection := submoduleProj_eq_starProjection V
  have h_proj_formula : q = y + submoduleProj V w := by
    have h' := EuclideanGeometry.orthogonalProjection_apply_mem
      (s := L.toAffine) (p := z) (x := y) hyL
    have h_lin : V.starProjection (z - y) = V.starProjection z - V.starProjection y :=
      V.starProjection.map_sub z y
    have h_goal : q = V.starProjection z - V.starProjection y + y := by
      simpa [q] using h'
    rw [h_goal]
    have h9 : V.starProjection z - V.starProjection y + y = y + submoduleProj V w := by
      rw [←h_lin, ←hV] <;> simp [w] <;> abel
    exact h9
  have h1 : ‖w - submoduleProj V w‖ < r := by
    have h_eq : z - q = w - submoduleProj V w := by
      rw [h_proj_formula] <;> simp [w] <;> abel
    have h : ‖z - q‖ = Metric.infDist z (L.toSet : Set Point) := by
      simpa [dist_eq_norm] using h_dist_q
    rw [h_eq] at h
    rw [h]
    exact h_infDist_L
  -- Step 3: operator norm bound for projection difference
  have h2 : ‖(submoduleProj V - submoduleProj V') w‖ ≤ submoduleDirDist V V' * ‖w‖ := by
    exact ContinuousLinearMap.le_opNorm (submoduleProj V - submoduleProj V') w
  have h3 : submoduleDirDist V V' ≤ δ := h_dir
  have h4 : ‖(submoduleProj V - submoduleProj V') w‖ ≤ δ * ‖w‖ := by
    calc _ ≤ submoduleDirDist V V' * ‖w‖ := h2
       _ ≤ δ * ‖w‖ := by gcongr
  -- Step 4: triangle inequality
  have h_triangle : ‖w - submoduleProj V' w‖ ≤
      ‖w - submoduleProj V w‖ + ‖(submoduleProj V - submoduleProj V') w‖ := by
    have h_eq : w - submoduleProj V' w =
        (w - submoduleProj V w) + (submoduleProj V w - submoduleProj V' w) := by
      simp [w] <;> abel
    rw [h_eq]
    exact norm_add_le _ _
  have h5 : ‖w - submoduleProj V' w‖ < r + R * δ := by
    calc ‖w - submoduleProj V' w‖
      ≤ ‖w - submoduleProj V w‖ + ‖(submoduleProj V - submoduleProj V') w‖ := h_triangle
    _ < r + δ * ‖w‖ := by linarith
    _ ≤ r + δ * R := by gcongr <;> linarith
    _ = r + R * δ := by ring
  -- Step 5: exhibit point q' = y + submoduleProj V' w on L' and bound distance
  let q' : Point := y + submoduleProj V' w
  have hq'_mem : q' ∈ L'.toSet := by
    have hV'_mem : submoduleProj V' w ∈ V' := by
      have h_eq1 : submoduleProj V' w = V'.orthogonalProjectionFn w := by
        have h_fn : V'.orthogonalProjectionFn w = (V'.orthogonalProjectionOnto w : Point) :=
          Submodule.orthogonalProjectionFn_eq w
        have h_clm : submoduleProj V' w = (V'.orthogonalProjectionOnto w : Point) := by rfl
        rw [h_fn, h_clm]
      rw [h_eq1]
      exact (V'.orthogonalProjectionOnto w).property
    have h : q' - y ∈ L'.toAffine.direction := by
      simpa [q', w] using hV'_mem
    have h2 : (q' - y) +ᵥ y ∈ L'.toAffine := L'.toAffine.vadd_mem_of_mem_direction h hyL'
    have h3 : (q' - y) +ᵥ y = q' := by
      simp [vadd_eq_add, q', w] <;> abel
    rw [h3] at h2
    exact h2
  have h_dist_q' : dist z q' = ‖w - submoduleProj V' w‖ := by
    have h : z - q' = w - submoduleProj V' w := by
      simp [q', w] <;> abel
    rw [dist_eq_norm, h]
  have h6 : dist z q' < r + R * δ := by
    rw [h_dist_q']
    exact h5
  exact Metric.mem_thickening_iff.mpr ⟨q', hq'_mem, h6⟩

/-- AffineSubspace version of `tube_cluster_containment`.

If two lines ℓ, ℓ' pass through y and their direction distance is ≤ δ,
then the intersection of tube_r(ℓ) with closedBall_R(y) is contained in
tube_{r+Rδ}(ℓ'). -/
lemma tube_cluster_containment_affine (y : Point)
    (ℓ ℓ' : AffineSubspace ℝ Point)
    (hℓ : Module.finrank ℝ ℓ.direction = 1)
    (hℓ' : Module.finrank ℝ ℓ'.direction = 1)
    (r R δ : ℝ) (hr : 0 < r) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hyℓ : y ∈ (ℓ : Set Point)) (hyℓ' : y ∈ (ℓ' : Set Point))
    (h_dir : submoduleDirDist ℓ.direction ℓ'.direction ≤ δ) :
    Metric.thickening r (ℓ : Set Point) ∩ Metric.closedBall y R ⊆
      Metric.thickening (r + R * δ) (ℓ' : Set Point) := by
  let L : Line2 := ⟨ℓ, hℓ⟩
  let L' : Line2 := ⟨ℓ', hℓ'⟩
  have h1 : y ∈ L.toSet := hyℓ
  have h2 : y ∈ L'.toSet := hyℓ'
  have h3 : lineDirDist L L' ≤ δ := by
    have h_eq1 : L.toAffine.direction = ℓ.direction := by rfl
    have h_eq2 : L'.toAffine.direction = ℓ'.direction := by rfl
    simpa [lineDirDist, h_eq1, h_eq2] using h_dir
  have h4 : tube r L ∩ Metric.closedBall y R ⊆ tube (r + R * δ) L' :=
    tube_cluster_containment y L L' r R δ hr hR hδ h1 h2 h3
  have h5 : tube r L = Metric.thickening r (ℓ : Set Point) := by rfl
  have h6 : tube (r + R * δ) L' = Metric.thickening (r + R * δ) (ℓ' : Set Point) := by rfl
  rw [h5, h6] at h4
  exact h4

-- ============================================================================
-- 8. Direction bound from tube membership
-- ============================================================================

/-- If `x ∈ L` and `y ∈ tube(r, L)`, then the direction of `L` is within
`submoduleDirDist ≤ r / ‖y - x‖` of the direction of `y - x`.

This is the geometric fact that a tube of width `r` around a line through `x`
subtends an angle `~arcsin(r/d)` at distance `d = ‖y-x‖`. -/
lemma direction_bound_from_tube (x y : Point) (L : Line2) (r : ℝ)
    (hr : 0 < r) (hne : y ≠ x)
    (hxL : x ∈ L.toSet) (hy_tube : y ∈ tube r L) :
    submoduleDirDist L.toAffine.direction (Submodule.span ℝ {y - x}) ≤
      r / ‖y - x‖ := by
  let V := L.toAffine.direction
  let w := y - x
  have hw0 : w ≠ 0 := by
    intro h; exact hne (sub_eq_zero.mp h)
  have hnorm_w : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let u : Point := (1 / ‖w‖) • w
  have hnu : ‖u‖ = 1 := by
    simp [u, norm_smul, hnorm_w.ne'] <;> field_simp [hnorm_w.ne'] <;> ring_nf <;> norm_num
  have huW : u ∈ Submodule.span ℝ {w} := by
    rw [Submodule.mem_span_singleton]; refine' ⟨1 / ‖w‖, _⟩ <;> simp [u] <;> ring
  have hW : Module.finrank ℝ (Submodule.span ℝ {w}) = 1 := by
    rw [finrank_span_singleton hw0] <;> norm_num
  have h1 : submoduleDirDist V (Submodule.span ℝ {w}) =
      ‖u - V.orthogonalProjectionFn u‖ :=
    submoduleDirDist_eq_perp V (Submodule.span ℝ {w}) L.2 hW u huW hnu
  have h_proj_scale : V.orthogonalProjectionFn u = (1 / ‖w‖) • V.orthogonalProjectionFn w := by
    have h : V.orthogonalProjectionFn u = V.orthogonalProjectionFn ((1 / ‖w‖) • w) := by rfl
    rw [h]
    have h2 : V.orthogonalProjectionFn ((1 / ‖w‖) • w) = (1 / ‖w‖) • V.orthogonalProjectionFn w := by
      have h3 : V.orthogonalProjectionFn ((1 / ‖w‖) • w) = ↑(V.orthogonalProjectionOnto ((1 / ‖w‖) • w)) := by rfl
      rw [h3]
      have h4 : V.orthogonalProjectionOnto ((1 / ‖w‖) • w) = (1 / ‖w‖) • V.orthogonalProjectionOnto w := by
        exact V.orthogonalProjectionOnto.map_smul (1 / ‖w‖) w
      rw [h4]
      <;> rfl
    exact h2
  have h3 : u - V.orthogonalProjectionFn u = (1 / ‖w‖) • (w - V.orthogonalProjectionFn w) := by
    rw [h_proj_scale]
    <;> simp [u, smul_sub] <;> ring
  have h4 : ‖u - V.orthogonalProjectionFn u‖ = ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ := by
    rw [h3, norm_smul]
    have h5 : ‖(1 / ‖w‖)‖ = 1 / ‖w‖ := by
      simp [hnorm_w.ne'] <;> field_simp [hnorm_w.ne'] <;> linarith
    rw [h5] <;> ring
  -- Distance from y to L equals ‖w - V.orthogonalProjectionFn w‖
  let q : Point := (EuclideanGeometry.orthogonalProjection L.toAffine y : Point)
  have hq_mem : q ∈ L.toSet := (EuclideanGeometry.orthogonalProjection L.toAffine y).property
  have h_dist_q : dist y q = Metric.infDist y (L.toSet : Set Point) :=
    EuclideanGeometry.dist_orthogonalProjection_eq_infDist L.toAffine y
  have h_proj_formula : q = x + V.orthogonalProjectionFn w := by
    have h' := EuclideanGeometry.orthogonalProjection_apply_mem
      (s := L.toAffine) (p := y) (x := x) hxL
    have hV : submoduleProj V = V.starProjection := submoduleProj_eq_starProjection V
    have h_lin : V.starProjection (y - x) = V.starProjection y - V.starProjection x :=
      V.starProjection.map_sub y x
    have h_goal : q = V.starProjection y - V.starProjection x + x := by
      simpa [q] using h'
    rw [h_goal]
    have h9 : V.starProjection y - V.starProjection x + x = x + submoduleProj V w := by
      rw [←h_lin, ←hV] <;> simp [w] <;> abel
    exact h9
  have h_perp_norm : ‖w - V.orthogonalProjectionFn w‖ = dist y q := by
    have h_eq : y - q = w - V.orthogonalProjectionFn w := by
      rw [h_proj_formula] <;> simp [w] <;> abel
    rw [dist_eq_norm, h_eq]
  have h_infDist_lt : Metric.infDist y (L.toSet : Set Point) < r := by
    rcases Metric.mem_thickening_iff.mp hy_tube with ⟨z', hz'L, hdist⟩
    have h2 : Metric.infDist y (L.toSet : Set Point) ≤ dist y z' :=
      infDist_le_dist_of_mem hz'L
    exact lt_of_le_of_lt h2 hdist
  have h5 : ‖w - V.orthogonalProjectionFn w‖ < r := by
    rw [h_perp_norm, h_dist_q]
    exact h_infDist_lt
  rw [h1, h4]
  have h6 : ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ ≤ r / ‖w‖ := by
    gcongr
    <;> linarith
  exact h6

end RadialBootstrapping
