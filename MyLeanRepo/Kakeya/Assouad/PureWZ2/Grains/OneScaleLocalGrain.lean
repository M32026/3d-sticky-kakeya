import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubeCountingCover
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Pure WZ2 one-scale local grain helpers

Helper lemmas for proving `PureWZ2OneScaleLocalGrainConclusion`.

## Easy case (outputLoss > 1/3)

The scalar projection of a set inside `ball(p, √rho)` has diameter at most `2√rho`.
The trivial diameter-based covering bound suffices to establish `IsADSet1` when
`outputLoss > 1/3`, since `rho ≥ δ^(1-outputLoss)` makes `δ^(-outputLoss)` dominate
`1/√rho`.

## Main results

- `diameter_covering_bound`: covering number of a diameter-bounded set
- `projection_diameter_bound`: diameter of scalar projection of a ball-bounded set
- `easy_case_is_ad_set1`: `IsADSet1` via diameter bound when `outputLoss > 1/3`
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Metric ENNReal

attribute [local instance] Classical.propDecidable

/-- Covering number of a set with diameter ≤ D at scale t is ≤ 2*D/t + 2.

The set is contained in a ball of radius D around any of its points, hence in an
interval of length 2D. An interval of length 2D is covered by at most `2D/t + 2`
balls of radius t. -/
lemma diameter_covering_bound
    {E : Set ℝ} {t D : ℝ} (ht_pos : 0 < t) (hD_nonneg : 0 ≤ D)
    (h_diam : ∀ y z, y ∈ E → z ∈ E → dist y z ≤ D) :
    (Metric.externalCoveringNumber ⟨t, ht_pos.le⟩ E : ENNReal) ≤
      ENNReal.ofReal (2 * D / t + 2) := by
  by_cases hE : E = ∅
  · rw [hE]; simp
  · have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE
    rcases hE_nonempty with ⟨y, hy⟩
    have hE_sub : E ⊆ Metric.closedBall y D := by
      intro z hz
      exact h_diam z y hz hy
    have h_interval : ∃ (left : ℝ), E ⊆ Set.Icc left (left + 2 * D) := by
      refine ⟨y - D, ?_⟩
      intro z hz
      have h : dist z y ≤ D := hE_sub hz
      have h' : |z - y| ≤ D := by simpa [Real.dist_eq] using h
      have h1 : y - D ≤ z := by linarith [abs_le.mp h']
      have h2 : z ≤ y + D := by linarith [abs_le.mp h']
      exact ⟨h1, by linarith⟩
    rcases h_interval with ⟨left, hleft⟩
    let s : Finset Unit := {()}
    let A : Unit → Set ℝ := fun _ => E
    have hA : ∀ (i : Unit), i ∈ s → ∃ (l : ℝ), A i ⊆ Set.Icc l (l + 2 * D) := by
      intro i _
      exact ⟨left, hleft⟩
    have h_main : (Metric.externalCoveringNumber ⟨t, ht_pos.le⟩ (⋃ i ∈ s, A i) : ENNReal) ≤
        (s.card : ENNReal) * (ENNReal.ofReal ((2 * D) / t) + 2) :=
      covering_number_union_intervals ht_pos (by positivity) s hA
    have h_union : (⋃ i ∈ s, A i) = E := by
      simp [s, A] <;> ext x <;> simp
    rw [h_union] at h_main
    have h_card : (s.card : ENNReal) = 1 := by simp [s]
    rw [h_card] at h_main
    have h_main2 : (Metric.externalCoveringNumber ⟨t, ht_pos.le⟩ E : ENNReal) ≤
        ENNReal.ofReal (2 * D / t) + (2 : ENNReal) := by
      simpa [one_mul] using h_main
    have h_pos : 0 ≤ 2 * D / t := by positivity
    have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
    have h_final : (ENNReal.ofReal (2 * D / t) + (2 : ENNReal)) = ENNReal.ofReal (2 * D / t + 2) := by
      rw [h2]
      have h3 : ENNReal.ofReal (2 * D / t) + ENNReal.ofReal (2 : ℝ) =
          ENNReal.ofReal ((2 * D / t) + (2 : ℝ)) := by
        rw [← ENNReal.ofReal_add h_pos (by norm_num)]
      exact h3
    rw [h_final] at h_main2
    exact h_main2

/-- The scalar projection of a set inside `ball(p, √rho)` has diameter ≤ 2√rho. -/
lemma projection_diameter_bound
    {rho : ℝ} (hrho_pos : 0 < rho)
    {v : Point3} (hv_unit : ‖v‖ = 1)
    {p : Point3} {E : Set Point3}
    (hE : E ⊆ Metric.closedBall p (Real.sqrt rho)) :
    ∀ y z, y ∈ scalarProjection v E → z ∈ scalarProjection v E → dist y z ≤ 2 * Real.sqrt rho := by
  rintro y z ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩
  have h1 : dist y' p ≤ Real.sqrt rho := hE hy'
  have h2 : dist z' p ≤ Real.sqrt rho := hE hz'
  have h3 : dist y' z' ≤ dist y' p + dist p z' := dist_triangle y' p z'
  have h4 : dist p z' = dist z' p := dist_comm p z'
  rw [h4] at h3
  have h5 : dist y' z' ≤ 2 * Real.sqrt rho := by linarith
  have h6 : dist (inner ℝ y' v) (inner ℝ z' v) ≤ dist y' z' := by
    have h7 : dist (inner ℝ y' v) (inner ℝ z' v) = |inner ℝ (y' - z') v| := by
      simp [Real.dist_eq, inner_sub_left] <;> ring
    rw [h7]
    have h8 : |inner ℝ (y' - z') v| ≤ ‖y' - z'‖ * ‖v‖ := abs_real_inner_le_norm (y' - z') v
    have h9 : ‖y' - z'‖ = dist y' z' := by simp [dist_eq_norm]
    rw [h9, hv_unit] at h8 <;> linarith
  exact h6.trans h5

/-- Easy case: diameter bound gives `IsADSet1` when `outputLoss > 1/3`.

For `t ≥ rho`, the covering number is at most `4√rho/t + 2`.
The worst case is `t = rho`, giving `4/√rho + 2`.
Since `rho ≥ δ^(1-outputLoss)`, we have `4/√rho ≤ 4·δ^(-(1-outputLoss)/2)`.
The exponent `-(1-outputLoss)/2` is more negative than `-outputLoss` precisely
when `outputLoss > 1/3`, so `δ^(-outputLoss)` dominates for sufficiently small `δ`.

The hypothesis `h_absorb` packages the required small-`δ` inequality. -/
lemma easy_case_is_ad_set1
    {delta sigma outputLoss rho : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (houtput_loss_pos : 0 < outputLoss)
    (h_easy : 1 / 3 < outputLoss)
    (hrho_pos : 0 < rho) (hrho_one : rho ≤ 1)
    (hrho_lower : delta ≤ rho)
    (v : Point3) (hv_unit : ‖v‖ = 1)
    (p : Point3)
    (E : Set Point3)
    (hE : E ⊆ Metric.closedBall p (Real.sqrt rho))
    (hE_proj_bdd : scalarProjection v E ⊆ Set.Icc (-4 : ℝ) 4)
    (h_absorb : (4 / Real.sqrt rho + 2 : ℝ) ≤ Real.rpow delta (-outputLoss)) :
    IsADSet1 (scalarProjection v E) rho (1 - sigma)
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  let alpha : ℝ := 1 - sigma
  have halpha_pos : 0 < alpha := by linarith
  have halpha_le_one : alpha ≤ 1 := by linarith
  let C : ENNReal := Kakeya.realRpowENN delta (-outputLoss)
  have hC_one : (1 : ENNReal) ≤ C := by
    simp only [C, Kakeya.realRpowENN]
    have h1 : (1 : ℝ) ≤ Real.rpow delta (-outputLoss) := by
      have h2 : -outputLoss ≤ 0 := by linarith
      have h3 : Real.rpow delta 0 ≤ Real.rpow delta (-outputLoss) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one h2
      have h4 : Real.rpow delta 0 = 1 := by simp
      rw [h4] at h3
      exact h3
    have h5 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow delta (-outputLoss)) := by
      exact_mod_cast ENNReal.ofReal_le_ofReal h1
    exact h5
  have h_diam : ∀ y z, y ∈ scalarProjection v E → z ∈ scalarProjection v E → dist y z ≤ 2 * Real.sqrt rho :=
    projection_diameter_bound hrho_pos hv_unit hE
  refine ⟨hrho_pos, halpha_pos, halpha_le_one, hC_one, hE_proj_bdd, ?_⟩
  intro t ht_nonneg hrho_le_t ht_one x r ht_le_r hr_le_one
  set A_set : Set ℝ := scalarProjection v E ∩ Metric.closedBall x r with hA_def
  have ht_pos : 0 < t := by linarith
  have h_diam_A : ∀ y z, y ∈ A_set → z ∈ A_set → dist y z ≤ 2 * Real.sqrt rho := by
    intro y z hy hz
    exact h_diam y z hy.1 hz.1
  have h_cover : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
      ENNReal.ofReal (4 * Real.sqrt rho / t + 2) := by
    have h := diameter_covering_bound ht_pos (by positivity) h_diam_A
    have h_eq : (2 * (2 * Real.sqrt rho) / t + 2 : ℝ) = 4 * Real.sqrt rho / t + 2 := by ring
    rw [h_eq] at h
    exact h
  have h1 : 4 * Real.sqrt rho / t ≤ 4 / Real.sqrt rho := by
    have h2 : t ≥ rho := hrho_le_t
    have h3 : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
    have h4 : 4 * Real.sqrt rho / t ≤ 4 * Real.sqrt rho / rho := by gcongr
    have h_sq : (Real.sqrt rho)^2 = rho := Real.sq_sqrt (by linarith)
    have h5 : 4 * Real.sqrt rho / rho = 4 / Real.sqrt rho := by
      calc
        4 * Real.sqrt rho / rho
          = 4 * Real.sqrt rho / (Real.sqrt rho)^2 := by rw [h_sq]
        _ = 4 / Real.sqrt rho := by
          field_simp [h3.ne'] <;> ring
    rw [h5] at h4
    exact h4
  have h2 : (4 * Real.sqrt rho / t + 2 : ℝ) ≤ 4 / Real.sqrt rho + 2 := by linarith
  have h3 : (4 * Real.sqrt rho / t + 2 : ℝ) ≤ Real.rpow delta (-outputLoss) := h2.trans h_absorb
  have h_rt_nonneg : 0 ≤ r / t := by
    have h_r_nonneg : 0 ≤ r := by linarith
    exact div_nonneg h_r_nonneg (by linarith)
  have h4 : (1 : ℝ) ≤ Real.rpow (r / t) alpha := by
    have h5 : 1 ≤ r / t := by
      calc (1 : ℝ) = t / t := by field_simp [ht_pos.ne'] <;> ring
        _ ≤ r / t := by gcongr
    exact Real.one_le_rpow h5 (by linarith)
  have h_pos_a : 0 ≤ Real.rpow delta (-outputLoss) := Real.rpow_nonneg hdelta_pos.le _
  have h5 : (4 * Real.sqrt rho / t + 2 : ℝ) ≤ Real.rpow delta (-outputLoss) * Real.rpow (r / t) alpha := by
    calc (4 * Real.sqrt rho / t + 2 : ℝ)
        ≤ Real.rpow delta (-outputLoss) := h3
      _ ≤ Real.rpow delta (-outputLoss) * Real.rpow (r / t) alpha := by
        have h : Real.rpow delta (-outputLoss) * 1 ≤ Real.rpow delta (-outputLoss) * Real.rpow (r / t) alpha :=
          mul_le_mul_of_nonneg_left h4 h_pos_a
        simpa using h
  have h_pos1 : 0 ≤ Real.rpow delta (-outputLoss) := h_pos_a
  have h_pos2 : 0 ≤ Real.rpow (r / t) alpha := Real.rpow_nonneg h_rt_nonneg alpha
  have h6 : ENNReal.ofReal (4 * Real.sqrt rho / t + 2) ≤ C * Kakeya.realRpowENN (r / t) alpha := by
    simp only [C, Kakeya.realRpowENN]
    have h_eq : ENNReal.ofReal (Real.rpow delta (-outputLoss) * Real.rpow (r / t) alpha) =
        ENNReal.ofReal (Real.rpow delta (-outputLoss)) * ENNReal.ofReal (Real.rpow (r / t) alpha) := by
      rw [ENNReal.ofReal_mul h_pos1]
    rw [← h_eq]
    exact ENNReal.ofReal_le_ofReal h5
  exact h_cover.trans h6

/-- Convert a custom covering-number bound at scale `rho` into `PureWZ2PaperADSet1`.

Given that the full projection `scalarProjection v S` has covering number
at most `C` at scale `rho`, deduce the paper AD condition for all
subintervals at all scales `rho' ≥ rho`, using anti-monotonicity and
`1 ≤ (length/rho')^alpha`. -/
lemma slab_to_ad_wz1
    {sigma rho : ℝ}
    {C : ENNReal}
    {S : Set Point3}
    {v : Point3}
    (_hv_unit : ‖v‖ = 1)
    (hrho_pos : 0 < rho)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤)
    (h_cover_bound :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (scalarProjection v S)) : ENNReal) ≤ C) :
    PureWZ2PaperADSet1 (scalarProjection v S) rho (1 - sigma) C := by
  let alpha : ℝ := 1 - sigma
  have halpha_pos : 0 < alpha := by linarith
  have halpha_le_one : alpha ≤ 1 := by linarith
  refine' ⟨by linarith, halpha_pos, halpha_le_one, hC_one, hC_top, _⟩
  intro rho' hrho' hrho_ge left length hlength
  let E : Set ℝ := scalarProjection v S ∩ Set.Icc left (left + length)
  have hE_sub : E ⊆ scalarProjection v S := by intro x hx; exact hx.1
  have hrho'_pos : 0 < rho' := lt_of_lt_of_le hrho_pos hrho_ge
  have hlength_pos : 0 < length := lt_of_lt_of_le hrho'_pos hlength
  let ε : NNReal := ⟨rho, by linarith⟩
  let ε' : NNReal := ⟨rho', hrho'⟩
  have hε_le : ε ≤ ε' := by
    exact NNReal.coe_le_coe.mpr hrho_ge
  have h1 : (Metric.externalCoveringNumber ε' E : ENNReal) ≤
      Metric.externalCoveringNumber ε' (scalarProjection v S) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hE_sub
  have h2 : (Metric.externalCoveringNumber ε' (scalarProjection v S) : ENNReal) ≤
      Metric.externalCoveringNumber ε (scalarProjection v S) := by
    exact_mod_cast Metric.externalCoveringNumber_anti hε_le
  have hε_eq : ε = Real.toNNReal rho := by
    apply NNReal.coe_injective
    have h1 : (ε : ℝ) = rho := by
      simp [ε] <;> rfl
    have h2 : ((Real.toNNReal rho : ℝ)) = rho := by
      rw [Real.coe_toNNReal']
      rw [max_eq_left hrho_pos.le]
    rw [h1, h2]
  have h3 : (Metric.externalCoveringNumber ε' E : ENNReal) ≤ C := by
    rw [hε_eq] at h2
    exact le_trans h1 (le_trans h2 h_cover_bound)
  have h_ratio_pos : 0 < length / rho' := by
    apply div_pos hlength_pos hrho'_pos
  have h_ratio_one : 1 ≤ length / rho' := by
    calc 1 = rho' / rho' := by field_simp [hrho'_pos.ne']
      _ ≤ length / rho' := by gcongr
  have h4 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho') alpha := by
    have h5 : 1 ≤ length / rho' := h_ratio_one
    have h6 : 0 ≤ alpha := by linarith
    have h7 : (1 : ℝ) ≤ Real.rpow (length / rho') alpha := Real.one_le_rpow h5 h6
    simp only [Kakeya.realRpowENN]
    exact ENNReal.one_le_ofReal.mpr h7
  have h5 : C ≤ C * Kakeya.realRpowENN (length / rho') alpha := by
    have h6 : C * (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / rho') alpha := by gcongr
    simpa using h6
  exact le_trans h3 h5

end Kakeya.Assouad.PureWZ2
