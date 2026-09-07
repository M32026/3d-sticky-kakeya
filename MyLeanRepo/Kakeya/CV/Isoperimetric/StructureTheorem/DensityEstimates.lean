import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.SequenceCompactness
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import Mathlib.Tactic

/-!
# Density Estimates at Frontier and Reduced Boundary Points

## Main results

1. `frontier_volume_interior_pos`: at every frontier point of an open set `U`,
   `volume(U ∩ ball x r) > 0` for all `r > 0`.
2. `frontier_volume_exterior_pos`: at every frontier point of a **regular open**
   set `U = interior(closure U)`, `volume(ball x r \\ U) > 0` for all `r > 0`.
3. `reduced_boundary_two_sided_density`: at a reduced boundary point, both
   `volume(E ∩ ball x r)` and `volume(ball x r \\ E)` are bounded below by
   `c · r^n` for small `r`.

## Proof route for (3)

Compactness + half-space limit:
- Blow-ups at a reduced boundary point converge to a half-space
  (`reduced_boundary_blowup_data`, conditional on `halfspace_characterization`).
- Half-space has density 1/2 in every ball.
- Failure of the lower bound would give a sequence of blow-ups with density → 0,
  contradicting the half-space limit.
- Both interior and exterior bounds follow by the same argument.

## References

- Maggi, *Sets of Finite Perimeter*, Theorem 15.5, Steps 1-2
- Maggi, Remark 15.16 (density estimates at reduced boundary)
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.StructureTheorem

variable {n : ℕ}

-- ============================================================================
-- Task 2: Positive two-sided volume at frontier points
-- ============================================================================

/-- **Positive interior volume at frontier points.**

For any open set `U`, `x ∈ frontier U`, and `r > 0`,
`volume (U ∩ ball x r) > 0`. -/
theorem frontier_volume_interior_pos
    {U : Set (E n)} (hU : IsOpen U)
    {x : E n} (hx : x ∈ frontier U) {r : ℝ} (hr : 0 < r) :
    0 < volume (U ∩ ball x r) := by
  have hx_closure : x ∈ closure U := frontier_subset_closure hx
  have h_nonempty : (U ∩ ball x r).Nonempty := by
    have h1 : (ball x r ∩ U).Nonempty :=
      (_root_.mem_closure_iff.mp hx_closure) (ball x r) isOpen_ball (mem_ball_self hr)
    simpa [inter_comm] using h1
  have h_open : IsOpen (U ∩ ball x r) := hU.inter isOpen_ball
  exact h_open.measure_pos volume h_nonempty

/-- **Positive exterior volume at frontier points of a regular open set.**

For a regular open set `U = interior(closure U)`, `x ∈ frontier U`, and `r > 0`,
`volume ((ball x r) \ U) > 0`. -/
theorem frontier_volume_exterior_pos
    {U : Set (E n)} (hU : IsOpen U)
    (hU_reg : U = interior (closure U))
    {x : E n} (hx : x ∈ frontier U) {r : ℝ} (hr : 0 < r) :
    0 < volume ((ball x r) \ U) := by
  have h1 : ((ball x r) \ closure U).Nonempty := by
    by_contra h
    have h21 : ball x r \ closure U = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    have h2 : ball x r ⊆ closure U := by
      intro y hy
      by_contra h22
      have h23 : y ∈ ball x r \ closure U := ⟨hy, h22⟩
      rw [h21] at h23
      exact h23
    have h3 : ball x r ⊆ interior (closure U) := by
      exact isOpen_ball.subset_interior_iff.mpr h2
    have h4 : interior (closure U) = U := hU_reg.symm
    rw [h4] at h3
    have h5 : x ∈ U := h3 (mem_ball_self hr)
    have h6 : x ∉ U := by
      have h_frontier_eq : frontier U = closure U \ interior U :=
        Eq.symm (closure_sdiff_interior U)
      rw [h_frontier_eq] at hx
      have h7 : x ∉ interior U := hx.2
      have h8 : interior U = U := interior_eq_iff_isOpen.mpr hU
      rw [h8] at h7
      exact h7
    exact h6 h5
  have h_open : IsOpen ((ball x r) \ closure U) :=
    isOpen_ball.sdiff isClosed_closure
  have h_pos : 0 < volume ((ball x r) \ closure U) :=
    h_open.measure_pos volume h1
  have h_sub : (ball x r) \ closure U ⊆ (ball x r) \ U := by
    intro y hy
    exact ⟨hy.1, fun h => hy.2 (subset_closure h)⟩
  have h_le : volume ((ball x r) \ closure U) ≤ volume ((ball x r) \ U) :=
    measure_mono h_sub
  exact lt_of_lt_of_le h_pos h_le

/-- **Two-sided positive volume at frontier points of a regular open set.** -/
theorem frontier_two_sided_positive_volume
    {U : Set (E n)} (hU : IsOpen U)
    (hU_reg : U = interior (closure U))
    {x : E n} (hx : x ∈ frontier U) {r : ℝ} (hr : 0 < r) :
    0 < volume (U ∩ ball x r) ∧ 0 < volume ((ball x r) \ U) :=
  ⟨frontier_volume_interior_pos hU hx hr,
   frontier_volume_exterior_pos hU hU_reg hx hr⟩

-- ============================================================================
-- Helper lemmas for reduced boundary density
-- ============================================================================

/-- **L¹ convergence on a compact set implies convergence of intersection volumes.** -/
lemma tendsto_volume_inter_of_symmDiff {E_seq : ℕ → Set (E n)} {F : Set (E n)}
    {K : Set (E n)} (hK : IsCompact K)
    (h_conv : Tendsto (fun k => volume (symmDiff (E_seq k) F ∩ K)) atTop (nhds 0)) :
    Tendsto (fun k => volume (E_seq k ∩ K)) atTop (nhds (volume (F ∩ K))) := by
  let d := fun k => volume (symmDiff (E_seq k) F ∩ K)
  let a := fun k => volume (E_seq k ∩ K)
  let b := volume (F ∩ K)
  have hK_fin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have ha_fin : ∀ k, a k ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hK_fin (measure_mono (by simp))
  have hb_fin : b ≠ ⊤ :=
    ne_top_of_le_ne_top hK_fin (measure_mono (by simp))
  have hd_fin : ∀ k, d k ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top hK_fin (measure_mono (by simp))
  have h1 : ∀ k, a k ≤ b + d k := by
    intro k
    have h_sub : E_seq k ∩ K ⊆ (F ∩ K) ∪ (symmDiff (E_seq k) F ∩ K) := by
      intro x hx
      have hxK : x ∈ K := hx.2
      by_cases h : x ∈ F
      · exact Or.inl ⟨h, hxK⟩
      · exact Or.inr ⟨Or.inl ⟨hx.1, h⟩, hxK⟩
    calc a k
      ≤ volume ((F ∩ K) ∪ (symmDiff (E_seq k) F ∩ K)) := measure_mono h_sub
    _ ≤ b + d k := measure_union_le _ _
  have h2 : ∀ k, b ≤ a k + d k := by
    intro k
    have h_sub : F ∩ K ⊆ (E_seq k ∩ K) ∪ (symmDiff (E_seq k) F ∩ K) := by
      intro x hx
      have hxK : x ∈ K := hx.2
      by_cases h : x ∈ E_seq k
      · exact Or.inl ⟨h, hxK⟩
      · exact Or.inr ⟨Or.inr ⟨hx.1, h⟩, hxK⟩
    calc b
      ≤ volume ((E_seq k ∩ K) ∪ (symmDiff (E_seq k) F ∩ K)) := measure_mono h_sub
    _ ≤ a k + d k := measure_union_le _ _
  have h3 : ∀ k, |(a k).toReal - b.toReal| ≤ (d k).toReal := by
    intro k
    have h4 : (a k).toReal ≤ b.toReal + (d k).toReal := by
      have h5 : b + d k ≠ ⊤ := add_ne_top.mpr ⟨hb_fin, hd_fin k⟩
      have h6 : (a k).toReal ≤ (b + d k).toReal :=
        (ENNReal.toReal_le_toReal (ha_fin k) h5).mpr (h1 k)
      have h7 : (b + d k).toReal = b.toReal + (d k).toReal :=
        ENNReal.toReal_add hb_fin (hd_fin k)
      rw [h7] at h6
      exact h6
    have h5 : b.toReal ≤ (a k).toReal + (d k).toReal := by
      have h6 : a k + d k ≠ ⊤ := add_ne_top.mpr ⟨ha_fin k, hd_fin k⟩
      have h7 : b.toReal ≤ (a k + d k).toReal :=
        (ENNReal.toReal_le_toReal hb_fin h6).mpr (h2 k)
      have h8 : (a k + d k).toReal = (a k).toReal + (d k).toReal :=
        ENNReal.toReal_add (ha_fin k) (hd_fin k)
      rw [h8] at h7
      exact h7
    rw [abs_le] <;> constructor <;> linarith
  have h4 : Tendsto (fun k => (d k).toReal) atTop (nhds 0) :=
    (ENNReal.tendsto_toReal (show (0 : ENNReal) ≠ ⊤ from by simp)).comp h_conv
  have h7 : Tendsto (fun k => |(a k).toReal - b.toReal|) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) h3 h4
  have h5 : Tendsto (fun k => (a k).toReal) atTop (nhds b.toReal) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using h7
  have h6 : Tendsto (fun k => ENNReal.ofReal ((a k).toReal)) atTop
      (nhds (ENNReal.ofReal b.toReal)) :=
    continuous_ofReal.tendsto b.toReal |>.comp h5
  have h7eq : (fun k => ENNReal.ofReal ((a k).toReal)) = a := by
    funext k; rw [ENNReal.ofReal_toReal (ha_fin k)]
  have h8 : ENNReal.ofReal b.toReal = b := ENNReal.ofReal_toReal hb_fin
  rw [h7eq, h8] at h6
  exact h6

/-- **L¹ convergence implies convergence of complement volumes on compact.** -/
lemma tendsto_volume_compl_of_symmDiff {E_seq : ℕ → Set (E n)} {F : Set (E n)}
    {K : Set (E n)} (hK : IsCompact K)
    (h_conv : Tendsto (fun k => volume (symmDiff (E_seq k) F ∩ K)) atTop (nhds 0)) :
    Tendsto (fun k => volume (K \ E_seq k)) atTop (nhds (volume (K \ F))) := by
  let E'_seq := fun k => (E_seq k)ᶜ
  let F' := Fᶜ
  have h_symm : ∀ k, symmDiff (E'_seq k) F' = symmDiff (E_seq k) F := by
    intro k
    ext x
    simp [symmDiff, E'_seq, F'] <;> tauto
  have h_conv' : Tendsto (fun k => volume (symmDiff (E'_seq k) F' ∩ K)) atTop (nhds 0) := by
    have h_eq : (fun k => volume (symmDiff (E'_seq k) F' ∩ K)) =
        (fun k => volume (symmDiff (E_seq k) F ∩ K)) := by
      funext k; rw [h_symm k]
    rw [h_eq]; exact h_conv
  have h_main := tendsto_volume_inter_of_symmDiff hK h_conv'
  have h_eq1 : ∀ k, E'_seq k ∩ K = K \ E_seq k := by
    intro k; ext x; simp [E'_seq]; tauto
  have h_eq2 : F' ∩ K = K \ F := by
    ext x; simp [F']; tauto
  have h_eq3 : (fun k => volume (E'_seq k ∩ K)) = fun k => volume (K \ E_seq k) := by
    funext k; rw [h_eq1 k]
  have h_eq4 : volume (F' ∩ K) = volume (K \ F) := by rw [h_eq2]
  have h_main2 := h_main
  rw [h_eq3] at h_main2
  rw [h_eq4] at h_main2
  exact h_main2

/-- **Half-space intersected with ball has positive volume.** -/
lemma halfSpace_inter_ball_positive {ν : E n} (hν_unit : ‖ν‖ = 1) {R : ℝ} (hR : 0 < R) :
    0 < volume ({y : E n | inner ℝ y ν < 0} ∩ ball (0 : E n) R) := by
  let y0 : E n := (-(R / 2)) • ν
  have h_cont : Continuous (fun y : E n => inner ℝ y ν) :=
    continuous_id.inner continuous_const
  have h1 : inner ℝ y0 ν < 0 := by
    have h_i1 : inner ℝ y0 ν = -(R / 2) * inner ℝ ν ν := by
      simp [y0, inner_smul_left] <;> ring
    rw [h_i1]
    have h_i2 : inner ℝ ν ν = (‖ν‖ : ℝ) ^ 2 := inner_self_eq_norm_sq_to_K ν
    rw [h_i2, hν_unit] <;> norm_num <;> linarith
  have h2 : y0 ∈ ball (0 : E n) R := by
    have h_abs : |-(R / 2)| = R / 2 := by
      rw [abs_neg, abs_of_pos] <;> linarith
    have h_norm : ‖y0‖ = R / 2 := by
      calc ‖y0‖
        = |-(R / 2)| * ‖ν‖ := norm_smul _ _
      _ = (R / 2) * ‖ν‖ := by rw [h_abs]
      _ = R / 2 := by rw [hν_unit] <;> ring
    simpa [ball, dist_zero_right, h_norm] using by linarith
  have h_open : IsOpen ({y : E n | inner ℝ y ν < 0} ∩ ball (0 : E n) R) :=
    (isOpen_lt h_cont continuous_const).inter isOpen_ball
  have h_nonempty : ({y : E n | inner ℝ y ν < 0} ∩ ball (0 : E n) R).Nonempty :=
    ⟨y0, h1, h2⟩
  exact h_open.measure_pos volume h_nonempty

/-- **Complement of half-space intersected with ball has positive volume.** -/
lemma halfSpace_compl_inter_ball_positive {ν : E n} (hν_unit : ‖ν‖ = 1) {R : ℝ} (hR : 0 < R) :
    0 < volume ({y : E n | inner ℝ y ν < 0}ᶜ ∩ ball (0 : E n) R) := by
  let G : Set (E n) := {y | inner ℝ y ν > 0}
  have h_cont : Continuous (fun y : E n => inner ℝ y ν) :=
    continuous_id.inner continuous_const
  have hG_open : IsOpen G := isOpen_lt continuous_const h_cont
  let y0 : E n := (R / 2) • ν
  have h1 : inner ℝ y0 ν > 0 := by
    have h_i1 : inner ℝ y0 ν = (R / 2) * inner ℝ ν ν := by
      simp [y0, inner_smul_left] <;> ring
    rw [h_i1]
    have h_i2 : inner ℝ ν ν = (‖ν‖ : ℝ) ^ 2 := inner_self_eq_norm_sq_to_K ν
    rw [h_i2, hν_unit] <;> linarith
  have h2 : y0 ∈ ball (0 : E n) R := by
    have h_norm : ‖y0‖ = R / 2 := by
      calc ‖y0‖
        = |R / 2| * ‖ν‖ := norm_smul _ _
      _ = (R / 2) * ‖ν‖ := by rw [abs_of_pos (show (0 : ℝ) < R / 2 by linarith)]
      _ = R / 2 := by rw [hν_unit] <;> ring
    simpa [ball, dist_zero_right, h_norm] using by linarith
  have hG_nonempty : (G ∩ ball (0 : E n) R).Nonempty := ⟨y0, h1, h2⟩
  have hG_pos : 0 < volume (G ∩ ball (0 : E n) R) :=
    (hG_open.inter isOpen_ball).measure_pos volume hG_nonempty
  have h_sub : G ∩ ball (0 : E n) R ⊆ {y : E n | inner ℝ y ν < 0}ᶜ ∩ ball (0 : E n) R := by
    intro y hy
    have h3 : inner ℝ y ν > 0 := hy.1
    have h4 : ¬(inner ℝ y ν < 0) := by linarith
    exact ⟨h4, hy.2⟩
  exact lt_of_lt_of_le hG_pos (measure_mono h_sub)

/-- **Blow-up of complement equals complement of blow-up.** -/
lemma blowUp_compl {S : Set (E n)} {x : E n} {r : ℝ} (hr : r ≠ 0) :
    blowUp Sᶜ x r = (blowUp S x r)ᶜ := by
  let Φ : E n ≃ₜ E n :=
    { toFun := blowUpMap x r
      invFun := fun z => x + r • z
      left_inv := fun y => by
        simp [blowUpMap, smul_smul, hr] <;> ring
      right_inv := fun z => by
        simp [blowUpMap, smul_smul, hr] <;> ring
      continuous_toFun := by
        unfold blowUpMap
        fun_prop
      continuous_invFun := by
        fun_prop }
  ext z
  simp only [Set.mem_compl_iff, Set.mem_image, blowUp]
  constructor
  · rintro ⟨y, hy, rfl⟩ hz
    rcases hz with ⟨y', hy', h_eq⟩
    have h_eq' : Φ y = Φ y' := by
      simpa [Φ] using h_eq.symm
    have h_inj : y = y' := Φ.injective h_eq'
    have h_contra : y' ∉ S := by
      rw [← h_inj]; exact hy
    exact h_contra hy'
  · intro hz
    rcases Φ.surjective z with ⟨y, rfl⟩
    have h_y_notin_S : y ∉ S := by
      intro h
      exact hz ⟨y, h, rfl⟩
    exact ⟨y, h_y_notin_S, rfl⟩

-- ============================================================================
-- Task 3: Two-sided density lower bound at reduced boundary points
-- ============================================================================

/-- **Two-sided density lower bound at a reduced boundary point**.

At a reduced boundary point `x` with normal `ν`, there exist constants `c > 0`
and `R > 0` such that for all `0 < r < R`:

  `volume (S ∩ ball x r) ≥ c · r^n`
  `volume ((ball x r) \\ S) ≥ c · r^n`

**Proof route (compactness + half-space limit):**

Suppose the interior density bound fails. Then there is a sequence `r_k → 0`
with `volume(S ∩ B(x,r_k)) / r_k^n → 0`. The blow-ups `S_k = (S-x)/r_k`
satisfy `volume(S_k ∩ B(0,1)) → 0`. By BV compactness, a subsequence
converges in L¹_loc to some `F`. By `reduced_boundary_blowup_data`,
`F =ᵐ {y | inner y ν < 0}`, so `volume(F ∩ B(0,1)) > 0`.
L¹ convergence implies `volume(S_k ∩ K) → volume(F ∩ K)`,
contradicting `volume(S_k ∩ K) → 0`.

The exterior bound follows by the same argument applied to the complement.

This proof uses `halfspace_characterization` through
`reduced_boundary_blowup_data`. -/
theorem reduced_boundary_two_sided_density
    {S : Set (E n)} (hS : MeasurableSet S)
    {x : E n} {ν : E n} (hν_unit : ‖ν‖ = 1)
    (h_reduced : ReducedBoundaryData S x ν)
    (hn : 2 ≤ n) :
    ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
      ∀ r ∈ Set.Ioo 0 R,
        volume (S ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
        volume ((ball x r) \ S) ≥ ENNReal.ofReal (c * r ^ n) := by
  have h_data := reduced_boundary_blowup_data hS x ν hν_unit h_reduced
  rcases h_data with ⟨h_vol_bound, h_trans_bound, h_halfspace⟩

  let H : Set (E n) := {y | inner ℝ y ν < 0}
  let K : Set (E n) := closedBall (0 : E n) (1 / 2)

  have hK_compact : IsCompact K := isCompact_closedBall _ _
  have hK_sub_ball : K ⊆ ball (0 : E n) 1 := by
    intro y hy
    have h : ‖y‖ ≤ 1 / 2 := by simpa [K, mem_closedBall, dist_zero_right] using hy
    simpa [ball, dist_zero_right] using by linarith

  have h_add_tendsto : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    refine ⟨Nat.ceil b, fun k hk => ?_⟩
    have h2 : (k : ℝ) ≥ (Nat.ceil b : ℝ) := by exact_mod_cast hk
    linarith [Nat.le_ceil b]
  have h_inv_tendsto : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) := by
    have h : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h_add_tendsto
    have h_eq : (fun k : ℕ => 1 / ((k : ℝ) + 1)) = fun k : ℕ => ((k : ℝ) + 1)⁻¹ := by
      funext k; ring
    rw [h_eq]; exact h

  let blowUpEquiv : (r : ℝ) → r ≠ 0 → (E n ≃ₜ E n) := fun r hr =>
    { toFun := blowUpMap x r
      invFun := fun z => x + r • z
      left_inv := fun y => by simp [blowUpMap, smul_smul, hr] <;> ring
      right_inv := fun z => by simp [blowUpMap, smul_smul, hr] <;> ring
      continuous_toFun := by
        unfold blowUpMap
        fun_prop
      continuous_invFun := by
        fun_prop }

  have h_ofReal_tendsto : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (nhds 0) := by
    have h9 : Continuous ENNReal.ofReal := continuous_ofReal
    have h10 : Tendsto (ENNReal.ofReal ∘ (fun k : ℕ => 1 / ((k : ℝ) + 1))) atTop
        (nhds (ENNReal.ofReal (0 : ℝ))) :=
      h9.tendsto (0 : ℝ) |>.comp h_inv_tendsto
    have h11 : ENNReal.ofReal (0 : ℝ) = (0 : ENNReal) := by simp
    rw [h11] at h10
    exact h10

  have h_le_id : ∀ (subseq : ℕ → ℕ), StrictMono subseq → ∀ n, n ≤ subseq n := by
    intro subseq hsub_strict n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h : subseq n < subseq (n + 1) := hsub_strict (by linarith)
      linarith

  -- ===== Claim 1: Interior density lower bound =====
  have h_claim1 : ∃ (c1 : ℝ) (R1 : ℝ), 0 < c1 ∧ 0 < R1 ∧
      ∀ r ∈ Set.Ioo 0 R1, volume (S ∩ ball x r) ≥ ENNReal.ofReal (c1 * r ^ n) := by
    by_contra h
    have h_neg : ∀ (c : ℝ), 0 < c → ∀ (R : ℝ), 0 < R →
        ∃ r ∈ Set.Ioo 0 R, volume (S ∩ ball x r) < ENNReal.ofReal (c * r ^ n) := by
      intro c hc R hR
      by_contra h2
      push Not at h2
      exact h (Exists.intro c (Exists.intro R ⟨hc, hR, h2⟩))
    have h_main : ∀ k : ℕ, ∃ (r : ℝ), r ∈ Set.Ioo 0 (min 1 (1 / ((k : ℝ) + 1))) ∧
        volume (S ∩ ball x r) < ENNReal.ofReal ((1 / ((k : ℝ) + 1)) * r ^ n) := by
      intro k
      exact h_neg (1 / ((k : ℝ) + 1)) (by positivity) (min 1 (1 / ((k : ℝ) + 1))) (by positivity)
    choose r hr_in hr_lt using h_main
    have hr_pos : ∀ k, 0 < r k := fun k => (hr_in k).1
    have hr_lt_one : ∀ k, r k < 1 := fun k => (hr_in k).2.trans_le (min_le_left _ _)
    have hr_lt_inv : ∀ k, r k < 1 / ((k : ℝ) + 1) := fun k =>
      (hr_in k).2.trans_le (min_le_right _ _)
    have h_abs : ∀ k, |r k| ≤ 1 / ((k : ℝ) + 1) := by
      intro k; rw [abs_of_pos (hr_pos k)]; exact (hr_lt_inv k).le
    have hr_tendsto : Tendsto r atTop (nhds 0) := squeeze_zero_norm h_abs h_inv_tendsto

    let E_seq := fun k => blowUp S x (r k)
    have hE_meas : ∀ k, MeasurableSet (E_seq k) := by
      intro k
      have hr_ne : r k ≠ 0 := (hr_pos k).ne'
      let Φ := blowUpEquiv (r k) hr_ne
      have hΦ : (Φ : E n → E n) = blowUpMap x (r k) := by
        funext y; simp [Φ, blowUpEquiv, blowUpMap] <;> rfl
      have h_eq : Φ '' S = E_seq k := by
        rw [hΦ] <;> rfl
      rw [← h_eq]
      exact Φ.measurableEmbedding.measurableSet_image.mpr hS

    have h_vol : ∀ (K' : Set (E n)), IsCompact K' →
        ∃ (C : ENNReal), ∀ k, volume (E_seq k ∩ K') ≤ C := by
      intro K' hK'
      rcases h_vol_bound K' hK' with ⟨C, hC⟩
      refine ⟨C, fun k => hC (r k) (hr_pos k) (hr_lt_one k)⟩
    have h_trans : ∀ (K' : Set (E n)), IsCompact K' →
        ∃ (C : ℝ), ∀ k, ∀ (h : E n),
          volume (symmDiff (E_seq k) ((fun y => y + h) '' (E_seq k)) ∩ K') ≤
          ENNReal.ofReal (C * ‖h‖) := by
      intro K' hK'
      rcases h_trans_bound K' hK' with ⟨C, hC⟩
      refine ⟨C, fun k => hC (r k) (hr_pos k) (hr_lt_one k)⟩

    rcases bv_compactness_sequence_of_translation hE_meas h_vol h_trans with
      ⟨F, subseq, hsub_strict, hF_meas, h_conv⟩

    let r' : ℕ → ℝ := fun k => r (subseq k)
    have hr'_pos : ∀ k, 0 < r' k := fun k => hr_pos (subseq k)
    have hr'_tendsto : Tendsto r' atTop (nhds 0) :=
      hr_tendsto.comp hsub_strict.tendsto_atTop
    have h_symmDiff_eq : ∀ (A B : Set (E n)), Geometry.symmDiff A B = symmDiff A B := by
      intro A B; rfl
    have h_conv' : ∀ (K' : Set (E n)), IsCompact K' →
        Tendsto (fun k => volume (symmDiff (blowUp S x (r' k)) F ∩ K')) atTop (nhds 0) := by
      intro K' hK'
      have h_eq : ∀ (k : ℕ), volume (Geometry.symmDiff (blowUp S x (r (subseq k))) F ∩ K') =
          volume (symmDiff (blowUp S x (r' k)) F ∩ K') := by
        intro k
        have h1 : r (subseq k) = r' k := by simp [r']
        rw [h1]
        rfl
      exact (h_conv K' hK').congr h_eq

    have hF_halfspace : F =ᵐ[volume] H :=
      h_halfspace F hF_meas r' hr'_pos hr'_tendsto h_conv'

    have h_inter_ae : (Set.inter F K) =ᵐ[volume] (Set.inter H K) := by
      filter_upwards [hF_halfspace] with y hy
      have h_yF : y ∈ F ↔ y ∈ H := by
        constructor
        · intro h; exact hy.mp h
        · intro h; exact hy.mpr h
      have h_iff : y ∈ Set.inter F K ↔ y ∈ Set.inter H K := by
        constructor
        · intro h; exact ⟨h_yF.mp h.1, h.2⟩
        · intro h; exact ⟨h_yF.mpr h.1, h.2⟩
      exact propext h_iff
    have h_pos_vol : 0 < volume (F ∩ K) := by
      have h_eq_vol : volume (F ∩ K) = volume (H ∩ K) := measure_congr h_inter_ae
      rw [h_eq_vol]
      have h_sub : H ∩ ball (0 : E n) (1 / 2) ⊆ H ∩ K := by
        intro y hy
        have h_yK : y ∈ K := by
          have h_norm : ‖y‖ < 1 / 2 := by simpa [ball, dist_zero_right] using hy.2
          simpa [K, mem_closedBall, dist_zero_right] using by linarith
        exact ⟨hy.1, h_yK⟩
      have h_pos : 0 < volume (H ∩ ball (0 : E n) (1 / 2)) :=
        halfSpace_inter_ball_positive hν_unit (by norm_num)
      exact lt_of_lt_of_le h_pos (measure_mono h_sub)

    have h_vol_conv : Tendsto (fun k => volume (E_seq (subseq k) ∩ K)) atTop
        (nhds (volume (F ∩ K))) :=
      tendsto_volume_inter_of_symmDiff hK_compact (h_conv K hK_compact)

    have h_bound : ∀ k, volume (E_seq (subseq k) ∩ ball (0 : E n) 1) ≤
        ENNReal.ofReal (1 / ((subseq k : ℝ) + 1)) := by
      intro k
      set rk := r (subseq k) with hrk_def
      have hrk_pos : 0 < rk := hr_pos (subseq k)
      have h_pos : 0 < rk ^ n := pow_pos hrk_pos n
      have hE_eq : E_seq (subseq k) = blowUp S x rk := by
        simp [E_seq, hrk_def]
      have h_ball_eq : ball x (rk * (1 : ℝ)) = ball x rk := by rw [mul_one]
      set scale : ENNReal := ENNReal.ofReal ((rk ^ n)⁻¹) with hscale
      have h1 : volume (E_seq (subseq k) ∩ ball (0 : E n) 1) = scale * volume (S ∩ ball x rk) := by
        rw [hE_eq]
        have h_tmp := blow_up_volume (S := S) (x := x) (r := rk) (R := (1 : ℝ)) hS hrk_pos (by norm_num)
        rw [h_tmp, h_ball_eq, ←hscale]
      have h2 : volume (S ∩ ball x rk) ≤
          ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) := (hr_lt (subseq k)).le
      have h_pos_a : 0 ≤ (rk ^ n)⁻¹ := by positivity
      have h_mul_eq : scale * ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) =
          ENNReal.ofReal (1 / ((subseq k : ℝ) + 1)) := by
        rw [hscale]
        have h5 : ENNReal.ofReal ((rk ^ n)⁻¹) * ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) =
            ENNReal.ofReal (((rk ^ n)⁻¹) * ((1 / ((subseq k : ℝ) + 1)) * rk ^ n)) := by
          rw [← ENNReal.ofReal_mul (hp := h_pos_a)]
        rw [h5]
        have h6 : ((rk ^ n)⁻¹) * ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) =
            1 / ((subseq k : ℝ) + 1) := by field_simp [h_pos.ne'] <;> ring
        rw [h6]
      rw [h1]
      calc
        scale * volume (S ∩ ball x rk)
          ≤ scale * ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) := mul_le_mul_left' h2 _
        _ = ENNReal.ofReal (1 / ((subseq k : ℝ) + 1)) := h_mul_eq

    have h_bound_K : ∀ k, volume (E_seq (subseq k) ∩ K) ≤
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have h5 : volume (E_seq (subseq k) ∩ K) ≤
          volume (E_seq (subseq k) ∩ ball (0 : E n) 1) :=
        measure_mono (inter_subset_inter_right _ hK_sub_ball)
      have h6 := h_bound k
      have h7 : k ≤ subseq k := h_le_id subseq hsub_strict k
      have h7' : (subseq k : ℝ) ≥ (k : ℝ) := by exact_mod_cast h7
      have h8 : 1 / ((subseq k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by gcongr <;> linarith
      exact h5.trans (h6.trans (ENNReal.ofReal_le_ofReal h8))

    have hK_fin2 : volume (F ∩ K) ≠ ⊤ :=
      ne_top_of_le_ne_top hK_compact.measure_lt_top.ne (measure_mono (by simp))
    have h_ek_fin : ∀ k, volume (E_seq (subseq k) ∩ K) ≠ ⊤ := fun k =>
      ne_top_of_le_ne_top hK_compact.measure_lt_top.ne (measure_mono (by simp))
    have h_vol_conv_real : Tendsto (fun k => (volume (E_seq (subseq k) ∩ K)).toReal) atTop
        (nhds (volume (F ∩ K)).toReal) :=
      (ENNReal.tendsto_toReal hK_fin2).comp h_vol_conv
    have h_bound_real : ∀ k, (volume (E_seq (subseq k) ∩ K)).toReal ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      have h9 : (volume (E_seq (subseq k) ∩ K)).toReal ≤ (ENNReal.ofReal (1 / ((k : ℝ) + 1))).toReal :=
        ENNReal.toReal_le_toReal (h_ek_fin k) (by simp) |>.mpr (h_bound_K k)
      have h10 : (ENNReal.ofReal (1 / ((k : ℝ) + 1))).toReal = 1 / ((k : ℝ) + 1) := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      rw [h10] at h9
      exact h9
    have h_tendsto_real : Tendsto (fun k => (volume (E_seq (subseq k) ∩ K)).toReal) atTop (nhds 0) :=
      squeeze_zero (fun _ => by positivity) h_bound_real h_inv_tendsto
    have h_eq_real : (volume (F ∩ K)).toReal = 0 := tendsto_nhds_unique h_vol_conv_real h_tendsto_real
    have h_eq : volume (F ∩ K) = 0 := by
      rw [← ENNReal.ofReal_toReal hK_fin2, h_eq_real] <;> simp
    exact h_pos_vol.ne' h_eq

  -- ===== Claim 2: Exterior density lower bound =====
  have h_claim2 : ∃ (c2 : ℝ) (R2 : ℝ), 0 < c2 ∧ 0 < R2 ∧
      ∀ r ∈ Set.Ioo 0 R2, volume ((ball x r) \ S) ≥ ENNReal.ofReal (c2 * r ^ n) := by
    by_contra h
    have h_neg : ∀ (c : ℝ), 0 < c → ∀ (R : ℝ), 0 < R →
        ∃ r ∈ Set.Ioo 0 R, volume ((ball x r) \ S) < ENNReal.ofReal (c * r ^ n) := by
      intro c hc R hR
      by_contra h2
      push Not at h2
      exact h (Exists.intro c (Exists.intro R ⟨hc, hR, h2⟩))
    have h_main : ∀ k : ℕ, ∃ (r : ℝ), r ∈ Set.Ioo 0 (min 1 (1 / ((k : ℝ) + 1))) ∧
        volume ((ball x r) \ S) < ENNReal.ofReal ((1 / ((k : ℝ) + 1)) * r ^ n) := by
      intro k
      exact h_neg (1 / ((k : ℝ) + 1)) (by positivity) (min 1 (1 / ((k : ℝ) + 1))) (by positivity)
    choose r hr_in hr_lt using h_main
    have hr_pos : ∀ k, 0 < r k := fun k => (hr_in k).1
    have hr_lt_one : ∀ k, r k < 1 := fun k => (hr_in k).2.trans_le (min_le_left _ _)
    have hr_lt_inv : ∀ k, r k < 1 / ((k : ℝ) + 1) := fun k =>
      (hr_in k).2.trans_le (min_le_right _ _)
    have h_abs : ∀ k, |r k| ≤ 1 / ((k : ℝ) + 1) := by
      intro k; rw [abs_of_pos (hr_pos k)]; exact (hr_lt_inv k).le
    have hr_tendsto : Tendsto r atTop (nhds 0) := squeeze_zero_norm h_abs h_inv_tendsto

    let E_seq := fun k => blowUp S x (r k)
    have hE_meas : ∀ k, MeasurableSet (E_seq k) := by
      intro k
      have hr_ne : r k ≠ 0 := (hr_pos k).ne'
      let Φ := blowUpEquiv (r k) hr_ne
      have hΦ : (Φ : E n → E n) = blowUpMap x (r k) := by
        funext y; simp [Φ, blowUpEquiv, blowUpMap] <;> rfl
      have h_eq : Φ '' S = E_seq k := by
        rw [hΦ] <;> rfl
      rw [← h_eq]
      exact Φ.measurableEmbedding.measurableSet_image.mpr hS

    have h_vol : ∀ (K' : Set (E n)), IsCompact K' →
        ∃ (C : ENNReal), ∀ k, volume (E_seq k ∩ K') ≤ C := by
      intro K' hK'
      rcases h_vol_bound K' hK' with ⟨C, hC⟩
      refine ⟨C, fun k => hC (r k) (hr_pos k) (hr_lt_one k)⟩
    have h_trans : ∀ (K' : Set (E n)), IsCompact K' →
        ∃ (C : ℝ), ∀ k, ∀ (h : E n),
          volume (symmDiff (E_seq k) ((fun y => y + h) '' (E_seq k)) ∩ K') ≤
          ENNReal.ofReal (C * ‖h‖) := by
      intro K' hK'
      rcases h_trans_bound K' hK' with ⟨C, hC⟩
      refine ⟨C, fun k => hC (r k) (hr_pos k) (hr_lt_one k)⟩

    rcases bv_compactness_sequence_of_translation hE_meas h_vol h_trans with
      ⟨F, subseq, hsub_strict, hF_meas, h_conv⟩

    let r' : ℕ → ℝ := fun k => r (subseq k)
    have hr'_pos : ∀ k, 0 < r' k := fun k => hr_pos (subseq k)
    have hr'_tendsto : Tendsto r' atTop (nhds 0) :=
      hr_tendsto.comp hsub_strict.tendsto_atTop
    have h_symmDiff_eq : ∀ (A B : Set (E n)), Geometry.symmDiff A B = symmDiff A B := by
      intro A B; rfl
    have h_conv' : ∀ (K' : Set (E n)), IsCompact K' →
        Tendsto (fun k => volume (symmDiff (blowUp S x (r' k)) F ∩ K')) atTop (nhds 0) := by
      intro K' hK'
      have h_eq : ∀ (k : ℕ), volume (Geometry.symmDiff (blowUp S x (r (subseq k))) F ∩ K') =
          volume (symmDiff (blowUp S x (r' k)) F ∩ K') := by
        intro k
        have h1 : r (subseq k) = r' k := by simp [r']
        rw [h1]
        rfl
      exact (h_conv K' hK').congr h_eq

    have hF_halfspace : F =ᵐ[volume] H :=
      h_halfspace F hF_meas r' hr'_pos hr'_tendsto h_conv'

    have h_compl_ae : Set.diff K F =ᵐ[volume] Set.diff K H := by
      filter_upwards [hF_halfspace] with y hy
      have h_yF : y ∈ F ↔ y ∈ H := by
        constructor
        · intro h; exact hy.mp h
        · intro h; exact hy.mpr h
      have h_iff : y ∈ Set.diff K F ↔ y ∈ Set.diff K H := by
        constructor
        · intro ⟨hK, hnF⟩; exact ⟨hK, fun hH => hnF (h_yF.mpr hH)⟩
        · intro ⟨hK, hnH⟩; exact ⟨hK, fun hF => hnH (h_yF.mp hF)⟩
      exact propext h_iff
    have h_pos_vol : 0 < volume (K \ F) := by
      have h_eq_vol : volume (K \ F) = volume (K \ H) := measure_congr h_compl_ae
      rw [h_eq_vol]
      have h_sub : Hᶜ ∩ ball (0 : E n) (1 / 2) ⊆ K \ H := by
        intro y hy
        have h_yK : y ∈ K := by
          have h_norm : ‖y‖ < 1 / 2 := by simpa [ball, dist_zero_right] using hy.2
          simpa [K, mem_closedBall, dist_zero_right] using by linarith
        exact ⟨h_yK, hy.1⟩
      have h_pos : 0 < volume (Hᶜ ∩ ball (0 : E n) (1 / 2)) :=
        halfSpace_compl_inter_ball_positive hν_unit (by norm_num)
      exact lt_of_lt_of_le h_pos (measure_mono h_sub)

    have h_vol_conv : Tendsto (fun k => volume (K \ E_seq (subseq k))) atTop
        (nhds (volume (K \ F))) :=
      tendsto_volume_compl_of_symmDiff hK_compact (h_conv' K hK_compact)

    have h_bound : ∀ k, volume ((ball (0 : E n) 1) \ E_seq (subseq k)) ≤
        ENNReal.ofReal (1 / ((subseq k : ℝ) + 1)) := by
      intro k
      set rk := r (subseq k) with hrk_def
      have hrk_pos : 0 < rk := hr_pos (subseq k)
      have hrk_ne : rk ≠ 0 := hrk_pos.ne'
      have h_pos : 0 < rk ^ n := pow_pos hrk_pos n
      have hS_compl : MeasurableSet Sᶜ := hS.compl
      have hE_eq : E_seq (subseq k) = blowUp S x rk := by
        simp [E_seq, hrk_def]
      have h_ball_eq : ball x (rk * (1 : ℝ)) = ball x rk := by rw [mul_one]
      set scale : ENNReal := ENNReal.ofReal ((rk ^ n)⁻¹) with hscale
      have hbc : blowUp Sᶜ x rk = (E_seq (subseq k))ᶜ := by
        rw [blowUp_compl hrk_ne] <;> rfl
      have h_eq1 : blowUp Sᶜ x rk ∩ ball (0 : E n) 1 =
          (ball (0 : E n) 1) \ E_seq (subseq k) := by
        rw [hbc]
        ext y
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
        <;> exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      have h2 : volume ((ball (0 : E n) 1) \ E_seq (subseq k)) =
          scale * volume (Sᶜ ∩ ball x rk) := by
        rw [← h_eq1]
        have h_tmp := blow_up_volume (S := Sᶜ) (x := x) (r := rk) (R := (1 : ℝ)) hS_compl hrk_pos (by norm_num)
        rw [h_tmp, h_ball_eq, ←hscale]
      have h3 : Sᶜ ∩ ball x rk = (ball x rk) \ S := by
        ext y; simp; tauto
      have h4 : volume ((ball x rk) \ S) ≤
          ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) := (hr_lt (subseq k)).le
      have h_pos_a : 0 ≤ (rk ^ n)⁻¹ := by positivity
      have h_mul_eq : scale * ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) =
          ENNReal.ofReal (1 / ((subseq k : ℝ) + 1)) := by
        rw [hscale]
        have h6 : ENNReal.ofReal ((rk ^ n)⁻¹) * ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) =
            ENNReal.ofReal (((rk ^ n)⁻¹) * ((1 / ((subseq k : ℝ) + 1)) * rk ^ n)) := by
          rw [← ENNReal.ofReal_mul (hp := h_pos_a)]
        rw [h6]
        have h7 : ((rk ^ n)⁻¹) * ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) =
            1 / ((subseq k : ℝ) + 1) := by field_simp [h_pos.ne'] <;> ring
        rw [h7]
      rw [h2, h3]
      calc
        scale * volume ((ball x rk) \ S)
          ≤ scale * ENNReal.ofReal ((1 / ((subseq k : ℝ) + 1)) * rk ^ n) := mul_le_mul_left' h4 _
        _ = ENNReal.ofReal (1 / ((subseq k : ℝ) + 1)) := h_mul_eq

    have h_bound_K : ∀ k, volume (K \ E_seq (subseq k)) ≤
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have h5 : volume (K \ E_seq (subseq k)) ≤
          volume ((ball (0 : E n) 1) \ E_seq (subseq k)) :=
        measure_mono (Set.sdiff_subset_sdiff hK_sub_ball (Subset.refl _))
      have h6 := h_bound k
      have h7 : k ≤ subseq k := h_le_id subseq hsub_strict k
      have h7' : (subseq k : ℝ) ≥ (k : ℝ) := by exact_mod_cast h7
      have h8 : 1 / ((subseq k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by gcongr <;> linarith
      exact h5.trans (h6.trans (ENNReal.ofReal_le_ofReal h8))

    have hK_fin2 : volume (K \ F) ≠ ⊤ :=
      ne_top_of_le_ne_top hK_compact.measure_lt_top.ne (measure_mono (by simp))
    have h_ek_fin : ∀ k, volume (K \ E_seq (subseq k)) ≠ ⊤ := fun k =>
      ne_top_of_le_ne_top hK_compact.measure_lt_top.ne (measure_mono (by simp))
    have h_vol_conv_real : Tendsto (fun k => (volume (K \ E_seq (subseq k))).toReal) atTop
        (nhds (volume (K \ F)).toReal) :=
      (ENNReal.tendsto_toReal hK_fin2).comp h_vol_conv
    have h_bound_real : ∀ k, (volume (K \ E_seq (subseq k))).toReal ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      have h9 : (volume (K \ E_seq (subseq k))).toReal ≤ (ENNReal.ofReal (1 / ((k : ℝ) + 1))).toReal :=
        ENNReal.toReal_le_toReal (h_ek_fin k) (by simp) |>.mpr (h_bound_K k)
      have h10 : (ENNReal.ofReal (1 / ((k : ℝ) + 1))).toReal = 1 / ((k : ℝ) + 1) := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      rw [h10] at h9
      exact h9
    have h_tendsto_real : Tendsto (fun k => (volume (K \ E_seq (subseq k))).toReal) atTop (nhds 0) :=
      squeeze_zero (fun _ => by positivity) h_bound_real h_inv_tendsto
    have h_eq_real : (volume (K \ F)).toReal = 0 := tendsto_nhds_unique h_vol_conv_real h_tendsto_real
    have h_eq : volume (K \ F) = 0 := by
      rw [← ENNReal.ofReal_toReal hK_fin2, h_eq_real] <;> simp
    exact h_pos_vol.ne' h_eq

  -- ===== Combine the two claims =====
  rcases h_claim1 with ⟨c1, R1, hc1_pos, hR1_pos, h1⟩
  rcases h_claim2 with ⟨c2, R2, hc2_pos, hR2_pos, h2⟩
  refine ⟨min c1 c2, min R1 R2, by positivity, by positivity, fun r hr => ?_⟩
  have hr1 : r ∈ Set.Ioo 0 R1 := ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩
  have hr2 : r ∈ Set.Ioo 0 R2 := ⟨hr.1, hr.2.trans_le (min_le_right _ _)⟩
  have h_i1 : volume (S ∩ ball x r) ≥ ENNReal.ofReal (c1 * r ^ n) := h1 r hr1
  have h_i2 : volume ((ball x r) \ S) ≥ ENNReal.ofReal (c2 * r ^ n) := h2 r hr2
  have h_c1 : (min c1 c2 : ℝ) ≤ c1 := min_le_left _ _
  have h_c2 : (min c1 c2 : ℝ) ≤ c2 := min_le_right _ _
  have h_rn_pos : 0 < r ^ n := pow_pos hr.1 n
  have h4 : ENNReal.ofReal ((min c1 c2) * r ^ n) ≤ ENNReal.ofReal (c1 * r ^ n) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr <;> linarith
  have h5 : ENNReal.ofReal ((min c1 c2) * r ^ n) ≤ ENNReal.ofReal (c2 * r ^ n) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr <;> linarith
  exact ⟨le_trans h4 h_i1, le_trans h5 h_i2⟩

end Geometry.StructureTheorem
