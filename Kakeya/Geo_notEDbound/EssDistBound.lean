/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Kakeya.Tube.CylinderApprox
public import Kakeya.Geo_notEDbound.NearlyParallel
public import Kakeya.Mathlib.Analysis.EuclideanFrame
public import Kakeya.Mathlib.Analysis.Segment
public import Kakeya.ConvexBody
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Tube.Param

/-!
# Essential distinctness bounds

Bounds on the number of essentially distinct tubes that are all not essentially distinct
from a given tube.  Includes `finite_label_of_bounded` (a finite ε-labeling of a closed
ball), `sliding_T0_relative` (near-simultaneous closing of perpendicular and parallel
features), and the main `packing_card_le_of_features` / `essDist_notED_bound_*` theorems
that yield dimension-only cardinality bounds.
-/

@[expose] public section

open MeasureTheory
open Topology
open Tube

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- Rescaled packaging of `notED_implies_all_close`: for any δ-tube `T` that
is not essentially distinct from `T₀`, there exist constants `C_dir, C_perp,
C_long > 0` (depending only on dimension) and a sign `ε ∈ {1, -1}` such that
the direction, perpendicular midpoint, and parallel midpoint each satisfy
explicit bounds (the perpendicular and parallel components are independent of
`ε`). -/
private lemma notED_rescaled_bounds (hn : 1 < Module.finrank ℝ E) :
    ∃ (C_dir C_perp C_long : ℝ), 0 < C_dir ∧ 0 < C_perp ∧ 0 < C_long ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ 1)
        (T T₀ : Tube δ E),
        ¬ IsEssentiallyDistinct T.carrier T₀.carrier →
        ∃ (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
          ‖ε • T.direction - T₀.direction‖ ≤ C_dir * (δ : ℝ) ∧
          ‖(T.midpoint - T₀.midpoint) -
              (inner ℝ (T.midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖
            ≤ C_perp * (δ : ℝ) ∧
          |inner ℝ (T.midpoint - T₀.midpoint) T₀.direction| ≤ C_long := by
  obtain ⟨C_dir, C_perp, C_long, hCd, hCp, hCl, hall⟩ := notED_implies_all_close hn
  refine ⟨C_dir, C_perp, C_long, hCd, hCp, hCl, ?_⟩
  intro δ hδ hδ1 T T₀ h_notED
  have hδ1' : δ ≤ 1 := by exact_mod_cast hδ1
  obtain ⟨hmin, ε₀, hε₀, hperp_eps, hpar_eps⟩ := hall hδ hδ1' T T₀ h_notED
  have hperp : ‖(T.midpoint - T₀.midpoint) -
        (inner ℝ (T.midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖
        ≤ C_perp * (δ : ℝ) := by
    rcases hε₀ with rfl | rfl
    · simpa [one_smul] using hperp_eps
    · have heq : (T.midpoint - T₀.midpoint) -
              (inner ℝ (T.midpoint - T₀.midpoint) T₀.direction) • T₀.direction =
            (T.midpoint - T₀.midpoint) -
              (inner ℝ (T.midpoint - T₀.midpoint) ((-1 : ℝ) • T₀.direction)) •
                ((-1 : ℝ) • T₀.direction) := by
        rw [neg_smul, one_smul, inner_neg_right, neg_smul, smul_neg, neg_neg]
      rw [heq]; exact hperp_eps
  have hpar : |inner ℝ (T.midpoint - T₀.midpoint) T₀.direction| ≤ C_long := by
    rcases hε₀ with rfl | rfl
    · simpa [one_smul] using hpar_eps
    · rw [show inner ℝ (T.midpoint - T₀.midpoint) T₀.direction
              = -(inner ℝ (T.midpoint - T₀.midpoint) ((-1 : ℝ) • T₀.direction)) by
              rw [neg_smul, one_smul, inner_neg_right, neg_neg], abs_neg]
      exact hpar_eps
  -- Choose ε based on which of ‖d - d₀‖, ‖d + d₀‖ realizes the min.
  by_cases hcase : ‖T.direction - T₀.direction‖ ≤ ‖T.direction + T₀.direction‖
  · refine ⟨1, Or.inl rfl, ?_, hperp, hpar⟩
    rw [one_smul]
    rw [min_eq_left hcase] at hmin
    exact hmin
  · push Not at hcase
    refine ⟨-1, Or.inr rfl, ?_, hperp, hpar⟩
    rw [show ((-1 : ℝ) • T.direction - T₀.direction)
          = -(T.direction + T₀.direction) by
          rw [neg_smul, one_smul]; abel, norm_neg]
    rw [min_eq_right hcase.le] at hmin
    exact hmin

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every closed ball `B(0, R)` in a finite-dimensional inner-product space
admits a finite ε-labeling: there exists `N : ℕ` and `label : E → Fin N` such
that any two points of `B(0, R)` with the same label lie within `ε` of each
other. -/
lemma finite_label_of_bounded
    (R ε : ℝ) (_ : 0 ≤ R) (hε : 0 < ε) :
    ∃ (N : ℕ), 0 < N ∧ ∃ (label : E → Fin N),
      ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ R → label x = label y → ‖x - y‖ ≤ ε := by
  classical
  -- The closed ball is compact (proper space), hence totally bounded.
  have hcpt : IsCompact (Metric.closedBall (0 : E) R) :=
    ProperSpace.isCompact_closedBall 0 R
  have htb : TotallyBounded (Metric.closedBall (0 : E) R) := hcpt.totallyBounded
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨t, ht_fin, ht_cov⟩ :=
    (Metric.totallyBounded_iff.mp htb) (ε / 2) hε2
  let F : Finset E := ht_fin.toFinset
  -- The cover condition rewritten for norm.
  have ht_cov' : ∀ x : E, ‖x‖ ≤ R → ∃ c ∈ t, dist x c < ε / 2 := by
    intro x hx
    have hxB : x ∈ Metric.closedBall (0 : E) R := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hx
    have hxc := ht_cov hxB
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hxc
    exact hxc
  -- We will use N := F.card + 1 (always positive).
  refine ⟨F.card + 1, Nat.succ_pos _, ?_⟩
  -- For each x ∈ E, choose a center, conditioned on the norm bound.
  let pick : E → E := fun x =>
    if hx : ‖x‖ ≤ R then (ht_cov' x hx).choose else (0 : E)
  -- Specs for pick.
  have pick_spec : ∀ x : E, ‖x‖ ≤ R →
      pick x ∈ t ∧ dist x (pick x) < ε / 2 := by
    intro x hx
    have hpick_eq : pick x = (ht_cov' x hx).choose := by
      simp only [pick, hx, dif_pos]
    rw [hpick_eq]
    exact ⟨(ht_cov' x hx).choose_spec.1, (ht_cov' x hx).choose_spec.2⟩
  -- Encode the center as a Fin F.card via a noncomputable equivalence.
  let φ : F → Fin F.card := (Finset.equivFin F)
  -- Define the label function.
  let label : E → Fin (F.card + 1) := fun x =>
    if hxF : pick x ∈ F then (φ ⟨pick x, hxF⟩).castSucc
    else Fin.last _
  refine ⟨label, ?_⟩
  intro x y hx hy hxy
  have hpx := pick_spec x hx
  have hpy := pick_spec y hy
  set cx := pick x with hcx_def
  set cy := pick y with hcy_def
  have hcx_mem : cx ∈ t := hpx.1
  have hcy_mem : cy ∈ t := hpy.1
  have hxdist : dist x cx < ε / 2 := hpx.2
  have hydist : dist y cy < ε / 2 := hpy.2
  have hcxF : cx ∈ F := by simpa [F, Set.Finite.mem_toFinset] using hcx_mem
  have hcyF : cy ∈ F := by simpa [F, Set.Finite.mem_toFinset] using hcy_mem
  -- Compute label x and label y.
  have hlx : label x = (φ ⟨cx, hcxF⟩).castSucc := by
    change (if hxF : pick x ∈ F then (φ ⟨pick x, hxF⟩).castSucc else Fin.last _)
        = (φ ⟨cx, hcxF⟩).castSucc
    rw [dif_pos hcxF]
  have hly : label y = (φ ⟨cy, hcyF⟩).castSucc := by
    change (if hyF : pick y ∈ F then (φ ⟨pick y, hyF⟩).castSucc else Fin.last _)
        = (φ ⟨cy, hcyF⟩).castSucc
    rw [dif_pos hcyF]
  rw [hlx, hly] at hxy
  -- castSucc is injective, then φ is injective.
  have h1 : φ ⟨cx, hcxF⟩ = φ ⟨cy, hcyF⟩ := Fin.castSucc_inj.mp hxy
  have h2 : (⟨cx, hcxF⟩ : F) = ⟨cy, hcyF⟩ := (Finset.equivFin F).injective h1
  have hcc : cx = cy := by
    have := Subtype.ext_iff.mp h2
    exact this
  -- Triangle inequality.
  have hxy_dist : dist x y ≤ dist x cx + dist cy y := by
    calc dist x y ≤ dist x cx + dist cx y := dist_triangle _ _ _
      _ = dist x cx + dist cy y := by rw [hcc]
  have hsum : dist x cx + dist cy y < ε / 2 + ε / 2 := by
    have hd2 : dist cy y = dist y cy := dist_comm _ _
    rw [hd2]
    linarith
  have hxy_lt : dist x y < ε := by
    have : ε / 2 + ε / 2 = ε := by ring
    linarith
  have : ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
  rw [this]
  exact le_of_lt hxy_lt

lemma sliding_T0_relative (hn : 1 < Module.finrank ℝ E) :
    ∃ (c_pair_dir c_pair_perp c_pair_par δ₀ : ℝ),
      0 < c_pair_dir ∧ 0 < c_pair_perp ∧ 0 < c_pair_par ∧
      0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ δ₀)
        (T₁ T₂ T₀ : Tube δ E),
        ‖T₁.direction - T₀.direction‖ ≤ c_pair_dir * (δ : ℝ) →
        ‖T₂.direction - T₀.direction‖ ≤ c_pair_dir * (δ : ℝ) →
        ‖(T₁.midpoint - T₂.midpoint) -
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖
          ≤ c_pair_perp * (δ : ℝ) →
        |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| ≤ c_pair_par →
        ¬ IsEssentiallyDistinct T₁.carrier T₂.carrier := by
  obtain ⟨c_slide, κ, δ₀, hcs_pos, hκ_pos, hκ_half, hδ0_pos, hδ0_le1, hslide⟩ :=
    Tube.nearly_parallel_sliding hn
  -- Choose constants.
  set c_pair_par : ℝ := (1/2 - κ) / 2 with hcpp_def
  set c_pair_perp : ℝ := c_slide / 2 with hcperp_def
  set A : ℝ := c_pair_perp + 2 * c_pair_par + 1 with hA_def
  have hcpp_pos : 0 < c_pair_par := by
    have h1 : (0 : ℝ) < 1/2 - κ := by linarith
    have h2 : (0 : ℝ) < (1/2 - κ) / 2 := by linarith
    exact h2
  have hcperp_pos : 0 < c_pair_perp := by
    have : (0 : ℝ) < c_slide / 2 := by linarith
    exact this
  have hA_pos : 0 < A := by
    have : (0 : ℝ) < c_pair_perp + 2 * c_pair_par + 1 := by linarith
    exact this
  set c_pair_dir : ℝ := min ((1/2 - κ) / (4 * A)) (c_slide / (4 * A)) with hcpd_def
  have h4A_pos : 0 < 4 * A := by linarith
  have hcpd_pos : 0 < c_pair_dir := by
    have h1 : 0 < (1/2 - κ) / (4 * A) := div_pos (by linarith) h4A_pos
    have h2 : 0 < c_slide / (4 * A) := div_pos hcs_pos h4A_pos
    exact lt_min h1 h2
  -- Key arithmetic relations the constants satisfy.
  have hcpd_le1 : c_pair_dir ≤ (1/2 - κ) / (4 * A) := min_le_left _ _
  have hcpd_le2 : c_pair_dir ≤ c_slide / (4 * A) := min_le_right _ _
  have hbound_slide : c_pair_dir * (4 * A) ≤ c_slide := by
    rw [← le_div_iff₀ h4A_pos]; exact hcpd_le2
  have hbound_par : c_pair_dir * (4 * A) ≤ 1/2 - κ := by
    rw [← le_div_iff₀ h4A_pos]; exact hcpd_le1
  -- (a) 2 * c_pair_dir ≤ c_slide
  have ha : 2 * c_pair_dir ≤ c_slide := by
    nlinarith [hA_pos, hcs_pos, hcperp_pos, hcpp_pos, hcpd_pos, hbound_slide]
  -- (b) c_pair_perp + (c_pair_perp + 2 * c_pair_par) * c_pair_dir ≤ c_slide
  have hb : c_pair_perp + (c_pair_perp + 2 * c_pair_par) * c_pair_dir ≤ c_slide := by
    have hpA : c_pair_perp + 2 * c_pair_par ≤ A := by
      change c_pair_perp + 2 * c_pair_par ≤ c_pair_perp + 2 * c_pair_par + 1
      linarith
    have hstep : (c_pair_perp + 2 * c_pair_par) * c_pair_dir ≤ A * c_pair_dir := by
      exact mul_le_mul_of_nonneg_right hpA hcpd_pos.le
    have hstep2 : A * c_pair_dir ≤ c_slide / 4 := by
      nlinarith [hA_pos, hcpd_pos, hbound_slide]
    have hcperp_val : c_pair_perp = c_slide / 2 := hcperp_def
    linarith
  -- (c) c_pair_par + (c_pair_perp + c_pair_par) * c_pair_dir ≤ 1/2 - κ
  have hc : c_pair_par + (c_pair_perp + c_pair_par) * c_pair_dir ≤ 1/2 - κ := by
    have hpA : c_pair_perp + c_pair_par ≤ A := by
      change c_pair_perp + c_pair_par ≤ c_pair_perp + 2 * c_pair_par + 1
      linarith
    have hstep : (c_pair_perp + c_pair_par) * c_pair_dir ≤ A * c_pair_dir := by
      exact mul_le_mul_of_nonneg_right hpA hcpd_pos.le
    have hstep2 : A * c_pair_dir ≤ (1/2 - κ) / 4 := by
      nlinarith [hA_pos, hcpd_pos, hbound_par]
    have hcpp_val : c_pair_par = (1/2 - κ) / 2 := hcpp_def
    linarith
  refine ⟨c_pair_dir, c_pair_perp, c_pair_par, δ₀, hcpd_pos, hcperp_pos, hcpp_pos,
    hδ0_pos, hδ0_le1, ?_⟩
  intro δ hδ hδ_le T₁ T₂ T₀ h_d1 h_d2 h_perp h_par
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδ1 : (δ : ℝ) ≤ 1 := hδ_le.trans hδ0_le1
  -- Unit-norm of directions.
  have hd0_norm : ‖T₀.direction‖ = 1 := by
    have := T₀.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have hd1_norm : ‖T₁.direction‖ = 1 := by
    have := T₁.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have hd2_norm : ‖T₂.direction‖ = 1 := by
    have := T₂.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  -- Apply hslide with T₁ and T₂. We need the three bounds w.r.t. T₂.direction.
  apply hslide hδ hδ_le T₁ T₂
  · -- (i) min ‖d₁ - d₂‖ ‖d₁ + d₂‖ ≤ c_slide * δ
    have hd0_sub : ‖T₀.direction - T₂.direction‖ ≤ c_pair_dir * δ := by
      have heq : T₀.direction - T₂.direction = -(T₂.direction - T₀.direction) := by
        rw [neg_sub]
      rw [heq, norm_neg]; exact h_d2
    have htri : ‖T₁.direction - T₂.direction‖ ≤ 2 * c_pair_dir * δ := by
      have hdec : T₁.direction - T₂.direction =
          (T₁.direction - T₀.direction) + (T₀.direction - T₂.direction) := by
        abel
      calc ‖T₁.direction - T₂.direction‖
          = ‖(T₁.direction - T₀.direction) + (T₀.direction - T₂.direction)‖ := by
            rw [hdec]
        _ ≤ ‖T₁.direction - T₀.direction‖ + ‖T₀.direction - T₂.direction‖ :=
            norm_add_le _ _
        _ ≤ c_pair_dir * δ + c_pair_dir * δ := by linarith
        _ = 2 * c_pair_dir * δ := by ring
    have hle : ‖T₁.direction - T₂.direction‖ ≤ c_slide * (δ : ℝ) := by
      have hkey : 2 * c_pair_dir * (δ : ℝ) ≤ c_slide * (δ : ℝ) := by
        have := mul_le_mul_of_nonneg_right ha hδr.le
        linarith
      linarith
    exact le_trans (min_le_left _ _) hle
  · -- (ii) Perpendicular bound w.r.t. T₂.direction
    have h_par_v : |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| ≤ c_pair_par :=
      h_par
    have hv_norm_bound : ‖T₁.midpoint - T₂.midpoint‖ ≤ c_pair_perp * δ + c_pair_par := by
      have hvdec : T₁.midpoint - T₂.midpoint =
          (T₁.midpoint - T₂.midpoint -
            (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction) +
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction := by
        abel
      calc ‖T₁.midpoint - T₂.midpoint‖
          = ‖(T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction) +
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ := by
            rw [← hvdec]
        _ ≤ ‖T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
              ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ :=
            norm_add_le _ _
        _ = ‖T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
              |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| * ‖T₀.direction‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ = ‖T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
              |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| := by
            rw [hd0_norm]; ring
        _ ≤ c_pair_perp * δ + c_pair_par := by linarith
    have hv_norm_le1 :
        ‖T₁.midpoint - T₂.midpoint‖ ≤ c_pair_perp + c_pair_par := by
      have h1 : c_pair_perp * δ ≤ c_pair_perp := by
        have := mul_le_mul_of_nonneg_left hδ1 hcperp_pos.le
        linarith
      linarith
    have hd0_d2 : ‖T₀.direction - T₂.direction‖ ≤ c_pair_dir * δ := by
      have heq : T₀.direction - T₂.direction = -(T₂.direction - T₀.direction) := by
        rw [neg_sub]
      rw [heq, norm_neg]; exact h_d2
    have hdecomp :
        (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction -
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction =
        (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) •
            (T₀.direction - T₂.direction) +
          (inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)) •
            T₂.direction := by
      have hir :
          inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction) =
            inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction -
              inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction := by
        exact inner_sub_right _ _ _
      rw [hir, smul_sub, sub_smul]
      module
    have hcorr_bound :
        ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction -
            (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
          ≤ (c_pair_perp + 2 * c_pair_par) * c_pair_dir * δ := by
      rw [hdecomp]
      have h_t1 :
          ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) •
              (T₀.direction - T₂.direction)‖
            ≤ c_pair_par * (c_pair_dir * δ) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul h_par_v hd0_d2 (norm_nonneg _) hcpp_pos.le
      have hvd0d2 :
          |inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)|
            ≤ ‖T₁.midpoint - T₂.midpoint‖ * (c_pair_dir * δ) := by
        calc |inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)|
            ≤ ‖T₁.midpoint - T₂.midpoint‖ * ‖T₀.direction - T₂.direction‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ ‖T₁.midpoint - T₂.midpoint‖ * (c_pair_dir * δ) :=
              mul_le_mul_of_nonneg_left hd0_d2 (norm_nonneg _)
      have h_t2 :
          ‖(inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)) •
              T₂.direction‖
            ≤ (c_pair_perp + c_pair_par) * (c_pair_dir * δ) := by
        rw [norm_smul, Real.norm_eq_abs, hd2_norm, mul_one]
        calc |inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)|
            ≤ ‖T₁.midpoint - T₂.midpoint‖ * (c_pair_dir * δ) := hvd0d2
          _ ≤ (c_pair_perp + c_pair_par) * (c_pair_dir * δ) := by
              apply mul_le_mul_of_nonneg_right hv_norm_le1
              positivity
      calc ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) •
              (T₀.direction - T₂.direction) +
              (inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)) •
                T₂.direction‖
          ≤ ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) •
                (T₀.direction - T₂.direction)‖ +
              ‖(inner ℝ (T₁.midpoint - T₂.midpoint) (T₀.direction - T₂.direction)) •
                T₂.direction‖ := norm_add_le _ _
        _ ≤ c_pair_par * (c_pair_dir * δ)
            + (c_pair_perp + c_pair_par) * (c_pair_dir * δ) := by linarith
        _ = (c_pair_perp + 2 * c_pair_par) * c_pair_dir * δ := by ring
    have hkey_eq :
        T₁.midpoint - T₂.midpoint -
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction =
        (T₁.midpoint - T₂.midpoint -
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction) +
        ((inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction -
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction) := by
      abel
    calc ‖T₁.midpoint - T₂.midpoint -
            (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
        = ‖(T₁.midpoint - T₂.midpoint -
            (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction) +
            ((inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction)‖ := by
          rw [hkey_eq]
      _ ≤ ‖T₁.midpoint - T₂.midpoint -
            (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
            ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖ :=
            norm_add_le _ _
      _ ≤ c_pair_perp * δ + (c_pair_perp + 2 * c_pair_par) * c_pair_dir * δ := by
          linarith
      _ = (c_pair_perp + (c_pair_perp + 2 * c_pair_par) * c_pair_dir) * (δ : ℝ) := by ring
      _ ≤ c_slide * (δ : ℝ) :=
          mul_le_mul_of_nonneg_right hb hδr.le
  · -- (iii) Parallel bound w.r.t. T₂.direction
    have h_par_v : |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| ≤ c_pair_par :=
      h_par
    have hv_norm_bound : ‖T₁.midpoint - T₂.midpoint‖ ≤ c_pair_perp * δ + c_pair_par := by
      have hvdec : T₁.midpoint - T₂.midpoint =
          (T₁.midpoint - T₂.midpoint -
            (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction) +
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction := by
        abel
      calc ‖T₁.midpoint - T₂.midpoint‖
          = ‖(T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction) +
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ := by
            rw [← hvdec]
        _ ≤ ‖T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
              ‖(inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ :=
            norm_add_le _ _
        _ = ‖T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
              |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| * ‖T₀.direction‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ = ‖T₁.midpoint - T₂.midpoint -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction) • T₀.direction‖ +
              |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| := by
            rw [hd0_norm]; ring
        _ ≤ c_pair_perp * δ + c_pair_par := by linarith
    have hv_norm_le1 :
        ‖T₁.midpoint - T₂.midpoint‖ ≤ c_pair_perp + c_pair_par := by
      have h1 : c_pair_perp * δ ≤ c_pair_perp := by
        have := mul_le_mul_of_nonneg_left hδ1 hcperp_pos.le
        linarith
      linarith
    have hd2_d0 : ‖T₂.direction - T₀.direction‖ ≤ c_pair_dir * δ := h_d2
    have heq_inner :
        inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction =
          inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction +
            inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction) := by
      have h : inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction) =
          inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction -
            inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction :=
        inner_sub_right _ _ _
      linarith
    have habs :
        |inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction|
          ≤ |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| +
              |inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction)| := by
      rw [heq_inner]
      exact abs_add_le _ _
    have h_abs_d2d0 :
        |inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction)|
          ≤ ‖T₁.midpoint - T₂.midpoint‖ * (c_pair_dir * δ) := by
      calc |inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction)|
          ≤ ‖T₁.midpoint - T₂.midpoint‖ * ‖T₂.direction - T₀.direction‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖T₁.midpoint - T₂.midpoint‖ * (c_pair_dir * δ) :=
            mul_le_mul_of_nonneg_left hd2_d0 (norm_nonneg _)
    have h_abs_d2d0' :
        |inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction)|
          ≤ (c_pair_perp + c_pair_par) * (c_pair_dir * δ) := by
      calc |inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction)|
          ≤ ‖T₁.midpoint - T₂.midpoint‖ * (c_pair_dir * δ) := h_abs_d2d0
        _ ≤ (c_pair_perp + c_pair_par) * (c_pair_dir * δ) := by
            apply mul_le_mul_of_nonneg_right hv_norm_le1
            positivity
    have h_d2d0_le_const :
        (c_pair_perp + c_pair_par) * (c_pair_dir * δ) ≤
          (c_pair_perp + c_pair_par) * c_pair_dir := by
      have hcdδ : c_pair_dir * δ ≤ c_pair_dir := by
        have := mul_le_mul_of_nonneg_left hδ1 hcpd_pos.le
        linarith
      have := mul_le_mul_of_nonneg_left hcdδ
        (show 0 ≤ c_pair_perp + c_pair_par by linarith)
      linarith
    calc |inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction|
        ≤ |inner ℝ (T₁.midpoint - T₂.midpoint) T₀.direction| +
            |inner ℝ (T₁.midpoint - T₂.midpoint) (T₂.direction - T₀.direction)| := habs
      _ ≤ c_pair_par + (c_pair_perp + c_pair_par) * (c_pair_dir * δ) := by linarith
      _ ≤ c_pair_par + (c_pair_perp + c_pair_par) * c_pair_dir := by linarith
      _ ≤ 1/2 - κ := hc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- **Geometric feature lemma from containment.**  Given two *unit* segments
`[a,b]` and `[c,d]` such that every point of `[a,b]` is within `ρ` of `[c,d]`
(the one-sided closeness coming from `T_in ⊆ (T_out.rescale ρ)`), the direction,
perpendicular midpoint offset and parallel midpoint offset of the second segment
relative to the first are controlled by `ρ` with dimension-free constants. This
plays the role of `notED_rescaled_bounds` but the "all close" data comes from
*containment* instead of *non-essential-distinctness*. -/
lemma containment_features {a b c d : E}
    (hab : ‖b - a‖ = 1) (hcd : ‖d - c‖ = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hclose : ∀ p ∈ segment ℝ a b, ∃ q ∈ segment ℝ c d, dist p q ≤ ρ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ‖ε • (d - c) - (b - a)‖ ≤ 4 * ρ ∧
      ‖(midpoint ℝ c d - midpoint ℝ a b) -
          (inner ℝ (midpoint ℝ c d - midpoint ℝ a b) (b - a)) • (b - a)‖ ≤ 3 * ρ ∧
      |inner ℝ (midpoint ℝ c d - midpoint ℝ a b) (b - a)| ≤ 4 := by
  set u : E := b - a with hu_def
  set e : E := d - c with he_def
  set m₁ : E := midpoint ℝ a b with hm1_def
  set m₂ : E := midpoint ℝ c d with hm2_def
  have hu_norm : ‖u‖ = 1 := hab
  have he_norm : ‖e‖ = 1 := hcd
  have h_uu : inner ℝ u u = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu_norm]; ring
  -- two-sided Hausdorff closeness
  have hclose2 : ∀ z ∈ segment ℝ c d, ∃ w ∈ segment ℝ a b, dist z w ≤ 3 * ρ :=
    Tube.symm_hausdorff_segment hab hcd hρ hclose
  -- DIRECTION: endpoints a, b are within ρ of [c,d].
  obtain ⟨pa, hpa_mem, hpa_le⟩ := hclose a (left_mem_segment ℝ a b)
  obtain ⟨pb, hpb_mem, hpb_le⟩ := hclose b (right_mem_segment ℝ a b)
  rw [segment_eq_image] at hpa_mem hpb_mem
  obtain ⟨s, hs_mem, hs_eq⟩ := hpa_mem
  obtain ⟨t, ht_mem, ht_eq⟩ := hpb_mem
  obtain ⟨hs0, hs1⟩ := hs_mem
  obtain ⟨ht0, ht1⟩ := ht_mem
  have hpa_eq : pa = c + s • e := by rw [← hs_eq, he_def]; match_scalars <;> ring
  have hpb_eq : pb = c + t • e := by rw [← ht_eq, he_def]; match_scalars <;> ring
  set τ : ℝ := t - s with hτ_def
  have hτ_le : |τ| ≤ 1 := by rw [hτ_def, abs_le]; constructor <;> linarith
  have hpapb : pb - pa = τ • e := by rw [hpa_eq, hpb_eq, hτ_def]; module
  have ha_pa : ‖a - pa‖ ≤ ρ := by rw [← dist_eq_norm]; exact hpa_le
  have hb_pb : ‖b - pb‖ ≤ ρ := by rw [← dist_eq_norm]; exact hpb_le
  have hu_τe : ‖u - τ • e‖ ≤ 2 * ρ := by
    have hdec : u - τ • e = (b - pb) - (a - pa) := by
      rw [hu_def, ← hpapb]; abel
    rw [hdec]
    calc ‖(b - pb) - (a - pa)‖ ≤ ‖b - pb‖ + ‖a - pa‖ := norm_sub_le _ _
      _ ≤ 2 * ρ := by linarith
  -- |τ| ≥ 1 - 2ρ
  have hτ_ge : 1 - 2 * ρ ≤ |τ| := by
    have h1 : ‖τ • e‖ = |τ| := by rw [norm_smul, Real.norm_eq_abs, he_norm, mul_one]
    have h2 : ‖u‖ ≤ ‖u - τ • e‖ + ‖τ • e‖ := by
      calc ‖u‖ = ‖(u - τ • e) + τ • e‖ := by congr 1; abel
        _ ≤ ‖u - τ • e‖ + ‖τ • e‖ := norm_add_le _ _
    rw [hu_norm, h1] at h2
    linarith
  -- min ‖e - u‖ ‖e + u‖ ≤ 4ρ
  have hmin : min ‖e - u‖ ‖e + u‖ ≤ 4 * ρ := by
    rcases le_or_gt 0 τ with hτ_nn | hτ_neg
    · -- τ ≥ 0 ⇒ ‖e - u‖ ≤ 4ρ
      have hτ_abs : |τ| = τ := abs_of_nonneg hτ_nn
      have hτ_lb : 1 - 2 * ρ ≤ τ := by rw [hτ_abs] at hτ_ge; exact hτ_ge
      have he_τe : ‖e - τ • e‖ ≤ 2 * ρ := by
        have : e - τ • e = (1 - τ) • e := by module
        rw [this, norm_smul, Real.norm_eq_abs, he_norm, mul_one]
        rw [abs_le]; constructor <;> linarith
      have : ‖e - u‖ ≤ 4 * ρ := by
        calc ‖e - u‖ = ‖(e - τ • e) + (τ • e - u)‖ := by congr 1; abel
          _ ≤ ‖e - τ • e‖ + ‖τ • e - u‖ := norm_add_le _ _
          _ ≤ 2 * ρ + 2 * ρ := by
              have : ‖τ • e - u‖ = ‖u - τ • e‖ := norm_sub_rev _ _
              rw [this]; linarith
          _ = 4 * ρ := by ring
      exact (min_le_left _ _).trans this
    · -- τ < 0 ⇒ ‖e + u‖ ≤ 4ρ
      have hτ_abs : |τ| = -τ := abs_of_neg hτ_neg
      have hτ_lb : 1 - 2 * ρ ≤ -τ := by rw [hτ_abs] at hτ_ge; exact hτ_ge
      have he_τe : ‖e + τ • e‖ ≤ 2 * ρ := by
        have : e + τ • e = (1 + τ) • e := by module
        rw [this, norm_smul, Real.norm_eq_abs, he_norm, mul_one]
        rw [abs_le]; constructor <;> linarith
      have : ‖e + u‖ ≤ 4 * ρ := by
        calc ‖e + u‖ = ‖(e + τ • e) + (u - τ • e)‖ := by congr 1; abel
          _ ≤ ‖e + τ • e‖ + ‖u - τ • e‖ := norm_add_le _ _
          _ ≤ 2 * ρ + 2 * ρ := by linarith
          _ = 4 * ρ := by ring
      exact (min_le_right _ _).trans this
  -- PERP / PAR: use m₂ ∈ [c,d], find w ∈ [a,b] with ‖m₂ - w‖ ≤ 3ρ.
  have hm2_mem : m₂ ∈ segment ℝ c d := by
    rw [hm2_def]; exact midpoint_mem_segment _ _
  obtain ⟨w, hw_mem, hw_le⟩ := hclose2 m₂ hm2_mem
  obtain ⟨σ, hσ_abs, hw_eq⟩ := mem_unit_segment_param hw_mem
  rw [← hm1_def, ← hu_def] at hw_eq
  have hm2w : ‖m₂ - w‖ ≤ 3 * ρ := by rw [← dist_eq_norm]; exact hw_le
  -- m₂ - m₁ = (m₂ - w) + σ • u
  have hsplit : m₂ - m₁ = (m₂ - w) + σ • u := by rw [hw_eq]; abel
  set wm : E := m₂ - w with hwm_def
  -- inner (m₂ - m₁) u = inner wm u + σ
  have h_inner_split : inner ℝ (m₂ - m₁) u = inner ℝ wm u + σ := by
    rw [hsplit, inner_add_left, real_inner_smul_left, h_uu]; ring
  have h_inner_wm_le : |inner ℝ wm u| ≤ 3 * ρ := by
    calc |inner ℝ wm u| ≤ ‖wm‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (3 * ρ) * 1 := by rw [hu_norm]; gcongr
      _ = 3 * ρ := by ring
  -- PAR bound
  have hpar : |inner ℝ (m₂ - m₁) u| ≤ 4 := by
    rw [h_inner_split]
    calc |inner ℝ wm u + σ| ≤ |inner ℝ wm u| + |σ| := abs_add_le _ _
      _ ≤ 3 * ρ + 1/2 := by linarith
      _ ≤ 4 := by linarith
  -- PERP bound: perp_u (m₂ - m₁) = perp_u wm
  have hperp_eq : (m₂ - m₁) - (inner ℝ (m₂ - m₁) u) • u
      = wm - (inner ℝ wm u) • u := by
    rw [h_inner_split, hsplit, add_smul]
    module
  have hperp : ‖(m₂ - m₁) - (inner ℝ (m₂ - m₁) u) • u‖ ≤ 3 * ρ := by
    rw [hperp_eq]
    -- ‖wm - ⟨wm,u⟩ u‖ ≤ ‖wm‖
    have hle : ‖wm - (inner ℝ wm u) • u‖ ≤ ‖wm‖ := by
      have hpyth : ‖wm‖^2 = ‖wm - (inner ℝ wm u) • u‖^2 + ‖(inner ℝ wm u) • u‖^2 := by
        have horth : inner ℝ (wm - (inner ℝ wm u) • u) ((inner ℝ wm u) • u) = (0 : ℝ) := by
          rw [inner_sub_left, real_inner_smul_right, real_inner_smul_right,
            real_inner_smul_left, h_uu]
          ring
        have := norm_add_sq_real (wm - (inner ℝ wm u) • u) ((inner ℝ wm u) • u)
        rw [horth] at this
        rw [show wm - (inner ℝ wm u) • u + (inner ℝ wm u) • u = wm by abel] at this
        linarith
      nlinarith [norm_nonneg (wm - (inner ℝ wm u) • u), norm_nonneg ((inner ℝ wm u) • u),
        norm_nonneg wm, sq_nonneg ‖(inner ℝ wm u) • u‖]
    linarith [hle, hm2w]
  -- Select ε from hmin.
  by_cases hcase : ‖e - u‖ ≤ ‖e + u‖
  · refine ⟨1, Or.inl rfl, ?_, ?_, hpar⟩
    · rw [one_smul]; rw [min_eq_left hcase] at hmin; exact hmin
    · exact hperp
  · push Not at hcase
    refine ⟨-1, Or.inr rfl, ?_, ?_, hpar⟩
    · rw [show ((-1 : ℝ) • e - u) = -(e + u) by rw [neg_smul, one_smul]; abel, norm_neg]
      rw [min_eq_right hcase.le] at hmin; exact hmin
    · exact hperp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- Triangle-inequality wrapper for `perp_component_frame_shift`: if the perpendicular
component of `v` relative to a unit vector `a` is `≤ α`, the norm of `v` is `≤ M`, and the
two unit directions are within `r`, then the perpendicular component relative to `b` is
`≤ α + 2 * M * r`. -/
private lemma perp_shift_combine {v a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {α M r : ℝ} (hperp : ‖v - (inner ℝ v a) • a‖ ≤ α)
    (hM : ‖v‖ ≤ M) (hr : ‖a - b‖ ≤ r) :
    ‖v - (inner ℝ v b) • b‖ ≤ α + 2 * M * r := by
  have hframe := perp_component_frame_shift v a b ha hb
  have h0M : (0 : ℝ) ≤ M := (norm_nonneg v).trans hM
  have h0r : (0 : ℝ) ≤ r := (norm_nonneg _).trans hr
  have key : ‖v - (inner ℝ v b) • b‖
      ≤ ‖v - (inner ℝ v a) • a‖
        + ‖(v - (inner ℝ v b) • b) - (v - (inner ℝ v a) • a)‖ := by
    have h := norm_add_le (v - (inner ℝ v a) • a)
      ((v - (inner ℝ v b) • b) - (v - (inner ℝ v a) • a))
    have he : (v - (inner ℝ v a) • a)
        + ((v - (inner ℝ v b) • b) - (v - (inner ℝ v a) • a))
        = v - (inner ℝ v b) • b := by abel
    rwa [he] at h
  calc ‖v - (inner ℝ v b) • b‖
      ≤ ‖v - (inner ℝ v a) • a‖
        + ‖(v - (inner ℝ v b) • b) - (v - (inner ℝ v a) • a)‖ := key
    _ ≤ α + 2 * ‖v‖ * ‖a - b‖ := add_le_add hperp hframe
    _ ≤ α + 2 * M * r := by gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- Triangle-inequality wrapper for `par_component_frame_shift`: if the parallel component
`⟪v, a⟫` is `≤ β`, the norm of `v` is `≤ M`, and the two unit directions are within `r`,
then the parallel component `⟪v, b⟫` is `≤ β + M * r`. -/
private lemma par_shift_combine {v a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {β M r : ℝ} (hpar : |inner ℝ v a| ≤ β)
    (hM : ‖v‖ ≤ M) (hr : ‖a - b‖ ≤ r) :
    |inner ℝ v b| ≤ β + M * r := by
  have hframe := par_component_frame_shift v a b ha hb
  have h0M : (0 : ℝ) ≤ M := (norm_nonneg v).trans hM
  have h0r : (0 : ℝ) ≤ r := (norm_nonneg _).trans hr
  have key : |inner ℝ v b|
      ≤ |inner ℝ v a| + |inner ℝ v b - inner ℝ v a| := by
    have he : inner ℝ v b
        = inner ℝ v a + (inner ℝ v b - inner ℝ v a) := by ring
    calc |inner ℝ v b|
        = |inner ℝ v a + (inner ℝ v b - inner ℝ v a)| := by rw [← he]
      _ ≤ |inner ℝ v a| + |inner ℝ v b - inner ℝ v a| := abs_add_le _ _
  calc |inner ℝ v b|
      ≤ |inner ℝ v a| + |inner ℝ v b - inner ℝ v a| := key
    _ ≤ β + ‖v‖ * ‖a - b‖ := add_le_add hpar hframe
    _ ≤ β + M * r := by gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- Rescaling helper: for `δ > 0`, scaling by `1/δ` turns a `C·δ` norm bound into a
plain `C` bound and back. (extracted by Fuse golfer) -/
private lemma norm_one_div_smul_le_iff {δ : ℝ} (hδ : 0 < δ) (x : E) (C : ℝ) :
    ‖(1 / δ) • x‖ ≤ C ↔ ‖x‖ ≤ C * δ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / δ),
    one_div_mul_eq_div, div_le_iff₀ hδ]

/-- **Generic small-δ packing core.**  Given dimension-free feature constants
`C_dir, C_perp, C_long > 0`, there is a threshold `δ₀` and a uniform cardinality
bound `C` such that: any pairwise-ED finset of `δ`-tubes (with `δ ≤ δ₀`) all
admitting the *direction / perp-midpoint / par-midpoint* feature bounds relative
to a fixed `T₀` has cardinality `≤ C`.  The features are exactly the data
produced either by `notED_rescaled_bounds` (non-essential-distinctness from `T₀`)
or by `containment_features` (containment of `T₀` inside the rescaled tube). -/
theorem packing_card_le_of_features (hn : 1 < Module.finrank ℝ E)
    (C_dir C_perp C_long : ℝ)
    (hCd_pos : 0 < C_dir) (hCp_pos : 0 < C_perp) (hCl_pos : 0 < C_long) :
    ∃ (δ₀ : ℝ) (C_small : ℕ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < C_small ∧
      ∀ {ι : Type*} {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ δ₀)
        (s : Finset ι) (T : ι → Tube δ E)
        (T₀ : Tube δ E),
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ s, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
          ‖ε • (T i).direction - T₀.direction‖ ≤ C_dir * (δ : ℝ) ∧
          ‖(T i).midpoint - T₀.midpoint -
              (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖
            ≤ C_perp * (δ : ℝ) ∧
          |inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction| ≤ C_long) →
        s.card ≤ C_small := by
  classical
  obtain ⟨c_pair_dir, c_pair_perp, c_pair_par, δ₀_sliding, hcpd_pos, hcpp_pos, hcppar_pos,
    hδ0sl_pos, hδ0sl_le1, hsliding⟩ :=
    sliding_T0_relative (E := E) hn
  -- Label meshes.
  set c_label_dir : ℝ := c_pair_dir / 2 with hcld_def
  set c_label_perp : ℝ := c_pair_perp / 4 with hclp_def
  set c_label_par : ℝ := min (c_pair_par / 4) (c_pair_perp / (16 * (C_dir + 1))) with hclpar_def
  have hcld_pos : 0 < c_label_dir := by rw [hcld_def]; positivity
  have hclp_pos : 0 < c_label_perp := by rw [hclp_def]; positivity
  have hclpar_pos : 0 < c_label_par := by
    rw [hclpar_def]
    refine lt_min ?_ ?_ <;> positivity
  have hclpar_le_cpa4 : c_label_par ≤ c_pair_par / 4 := by
    rw [hclpar_def]; exact min_le_left _ _
  have hclpar_le_cpp_C : c_label_par ≤ c_pair_perp / (16 * (C_dir + 1)) := by
    rw [hclpar_def]; exact min_le_right _ _
  have hCdir_p1_pos : 0 < 16 * (C_dir + 1) := by positivity
  have h_16Cdir_clpa : 16 * C_dir * c_label_par ≤ c_pair_perp := by
    have h := mul_le_mul_of_nonneg_left hclpar_le_cpp_C (by linarith : (0:ℝ) ≤ 16 * (C_dir + 1))
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hCdir_p1_pos.ne'] at h
    have hstep : 16 * C_dir * c_label_par ≤ 16 * (C_dir + 1) * c_label_par :=
      mul_le_mul_of_nonneg_right (by linarith) hclpar_pos.le
    linarith [h, hstep]
  have h_2clpa_Cdir : 2 * c_label_par * C_dir ≤ c_pair_perp / 8 := by
    have hrw : 2 * c_label_par * C_dir = (16 * C_dir * c_label_par) / 8 := by ring
    rw [hrw]; linarith [h_16Cdir_clpa]
  set Dperp : ℝ := 16 * c_label_perp * C_dir + 1 with hDperp_def
  set Dpar  : ℝ := 2 * (c_label_perp + c_label_par) * C_dir + 1 with hDpar_def
  have hDperp_pos : 0 < Dperp := by rw [hDperp_def]; positivity
  have hDpar_pos  : 0 < Dpar  := by rw [hDpar_def];  positivity
  set δ₀_perp : ℝ := c_pair_perp / Dperp with hδ0p_def
  set δ₀_par  : ℝ := c_pair_par  / Dpar  with hδ0pa_def
  have hδ0p_pos : 0 < δ₀_perp := by rw [hδ0p_def]; positivity
  have hδ0pa_pos : 0 < δ₀_par := by rw [hδ0pa_def]; positivity
  set δ₀ : ℝ := min 1 (min δ₀_sliding (min δ₀_perp δ₀_par)) with hδ0_def
  have hδ0_pos : 0 < δ₀ := by
    rw [hδ0_def]
    exact lt_min (by norm_num) (lt_min hδ0sl_pos (lt_min hδ0p_pos hδ0pa_pos))
  have hδ0_le1 : δ₀ ≤ 1 := by rw [hδ0_def]; exact min_le_left _ _
  have hδ0_le_sl : δ₀ ≤ δ₀_sliding := by
    rw [hδ0_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ0_le_p : δ₀ ≤ δ₀_perp := by
    rw [hδ0_def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ0_le_pa : δ₀ ≤ δ₀_par := by
    rw [hδ0_def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- Finite labelings.
  obtain ⟨N_dir, hN_dir_pos, label_dir, h_label_dir⟩ :=
    finite_label_of_bounded (E := E) C_dir c_label_dir hCd_pos.le hcld_pos
  obtain ⟨N_perp, hN_perp_pos, label_perp, h_label_perp⟩ :=
    finite_label_of_bounded (E := E) C_perp c_label_perp hCp_pos.le hclp_pos
  obtain ⟨N_par, hN_par_pos, label_par, h_label_par⟩ :=
    finite_label_of_bounded (E := E) C_long c_label_par hCl_pos.le hclpar_pos
  set C_small : ℕ := 2 * N_dir * N_perp * N_par with hC_small_def
  have hC_small_pos : 0 < C_small := by rw [hC_small_def]; positivity
  refine ⟨δ₀, C_small, hδ0_pos, hδ0_le1, hC_small_pos, ?_⟩
  intro ι' δ hδ hδ_le s T T₀ h_pairwise h_feat
  have hδ1 : δ ≤ 1 := hδ_le.trans hδ0_le1
  have hδr : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
  have h_unit_d0 : ‖T₀.direction‖ = 1 := by
    have := T₀.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  -- Choose ε for each i ∈ s (default 1 outside s).
  have h_choose : ∀ i : ι', ∃ (ε : ℝ),
      (i ∈ s → (ε = 1 ∨ ε = -1) ∧
        ‖ε • (T i).direction - T₀.direction‖ ≤ C_dir * δ ∧
        ‖(T i).midpoint - T₀.midpoint -
            (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖
          ≤ C_perp * δ ∧
        |inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction| ≤ C_long) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨ε, h1, h2, h3, h4⟩ := h_feat i hi
      exact ⟨ε, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, fun hi' => absurd hi' hi⟩
  choose εf hεf_all using h_choose
  have hεf : ∀ i ∈ s, εf i = 1 ∨ εf i = -1 := fun i hi => (hεf_all i hi).1
  have hεf_dir : ∀ i ∈ s, ‖εf i • (T i).direction - T₀.direction‖ ≤ C_dir * δ :=
    fun i hi => (hεf_all i hi).2.1
  have hεf_perp : ∀ i ∈ s,
      ‖(T i).midpoint - T₀.midpoint -
        (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖ ≤ C_perp * δ :=
    fun i hi => (hεf_all i hi).2.2.1
  have hεf_par : ∀ i ∈ s,
      |inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction| ≤ C_long :=
    fun i hi => (hεf_all i hi).2.2.2
  -- Rescaled features (total functions; default value 0 outside s does not matter).
  let D : ι' → E := fun i => (1 / (δ:ℝ)) • (εf i • (T i).direction - T₀.direction)
  let P : ι' → E := fun i =>
    (1 / (δ:ℝ)) • ((T i).midpoint - T₀.midpoint -
      (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction)
  let S : ι' → E := fun i =>
    (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction
  have hD_norm : ∀ i ∈ s, ‖D i‖ ≤ C_dir := fun i hi =>
    (norm_one_div_smul_le_iff hδr _ _).mpr (hεf_dir i hi)
  have hP_norm : ∀ i ∈ s, ‖P i‖ ≤ C_perp := fun i hi =>
    (norm_one_div_smul_le_iff hδr _ _).mpr (hεf_perp i hi)
  have hS_norm : ∀ i ∈ s, ‖S i‖ ≤ C_long := by
    intro i hi
    change ‖(inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖ ≤ C_long
    rw [norm_smul, Real.norm_eq_abs, h_unit_d0, mul_one]
    exact hεf_par i hi
  let sgn : ι' → Fin 2 := fun i => if εf i = 1 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  let lab : ι' → Fin 2 × Fin N_dir × Fin N_perp × Fin N_par := fun i =>
    ⟨sgn i, label_dir (D i), label_perp (P i), label_par (S i)⟩
  -- Same-label implies ¬ ED, contradicting pairwise.
  have h_inj : Set.InjOn lab s := by
    intro i hi j hj hij
    by_contra hne
    simp only [lab, Prod.mk.injEq] at hij
    obtain ⟨h_sign, h_d, h_p, h_s⟩ := hij
    -- Same sign.
    have h_eps : εf i = εf j := by
      rcases hεf i hi with h1 | h1 <;> rcases hεf j hj with h2 | h2
      · rw [h1, h2]
      · exfalso
        simp only [sgn, h1, h2, if_true, if_neg (by norm_num : (-1 : ℝ) ≠ 1)] at h_sign
        exact absurd (Fin.mk.inj_iff.mp h_sign) (by norm_num)
      · exfalso
        simp only [sgn, h1, h2, if_true, if_neg (by norm_num : (-1 : ℝ) ≠ 1)] at h_sign
        exact absurd (Fin.mk.inj_iff.mp h_sign) (by norm_num)
      · rw [h1, h2]
    set ε : ℝ := εf i with hε_def
    have hε_pm : ε = 1 ∨ ε = -1 := hεf i hi
    have hε_sq : ε * ε = 1 := by rcases hε_pm with h | h <;> (rw [h]; ring)
    have hε_abs : |ε| = 1 := by rcases hε_pm with h | h <;> (rw [h]; simp)
    -- Same direction bin ⇒ ‖D i - D j‖ ≤ c_label_dir.
    have hD_diff : ‖D i - D j‖ ≤ c_label_dir :=
      h_label_dir (D i) (D j) (hD_norm i hi) (hD_norm j hj) h_d
    have hP_diff : ‖P i - P j‖ ≤ c_label_perp :=
      h_label_perp (P i) (P j) (hP_norm i hi) (hP_norm j hj) h_p
    have hS_diff : ‖S i - S j‖ ≤ c_label_par :=
      h_label_par (S i) (S j) (hS_norm i hi) (hS_norm j hj) h_s
    -- Direction-bound bookkeeping.
    have hεTi : ‖ε • (T i).direction - T₀.direction‖ ≤ C_dir * δ := hεf_dir i hi
    have hεTj : ‖ε • (T j).direction - T₀.direction‖ ≤ C_dir * δ := by
      have hbase := hεf_dir j hj
      have hε_eq_εfj : ε = εf j := by rw [hε_def]; exact h_eps
      rw [hε_eq_εfj]
      exact hbase
    have h_Tij_dir_eq :
        ‖ε • (T i).direction - ε • (T j).direction‖
          = ‖(T i).direction - (T j).direction‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, hε_abs, one_mul]
    have h_label_dir_δ :
        ‖ε • (T i).direction - ε • (T j).direction‖ ≤ c_label_dir * δ := by
      have hDij : D i - D j =
          (1/(δ:ℝ)) • (ε • (T i).direction - ε • (T j).direction) := by
        change (1/(δ:ℝ)) • (εf i • (T i).direction - T₀.direction) -
            (1/(δ:ℝ)) • (εf j • (T j).direction - T₀.direction) =
            (1/(δ:ℝ)) • (ε • (T i).direction - ε • (T j).direction)
        rw [hε_def, ← h_eps, ← smul_sub]; congr 1; abel
      exact (norm_one_div_smul_le_iff hδr _ _).mp (hDij ▸ hD_diff)
    have h_Tij_dir : ‖(T i).direction - (T j).direction‖ ≤ c_label_dir * δ := by
      rw [← h_Tij_dir_eq]; exact h_label_dir_δ
    -- v_ij := T_i.mid - T_j.mid
    set v_ij : E := (T i).midpoint - (T j).midpoint with hv_ij_def
    have hperp_T0 :
        ‖v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction‖ ≤ c_label_perp * δ := by
      have hdecomp :
          v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction =
          ((T i).midpoint - T₀.midpoint -
            (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction) -
          ((T j).midpoint - T₀.midpoint -
            (inner ℝ ((T j).midpoint - T₀.midpoint) T₀.direction) • T₀.direction) := by
        have hv_split : v_ij =
            ((T i).midpoint - T₀.midpoint) - ((T j).midpoint - T₀.midpoint) := by
          rw [hv_ij_def]; abel
        rw [hv_split, inner_sub_left, sub_smul]; abel
      have hPij :
          P i - P j =
            (1/(δ:ℝ)) • (v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction) := by
        change (1/(δ:ℝ)) • ((T i).midpoint - T₀.midpoint -
              (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) • T₀.direction) -
            (1/(δ:ℝ)) • ((T j).midpoint - T₀.midpoint -
              (inner ℝ ((T j).midpoint - T₀.midpoint) T₀.direction) • T₀.direction) =
            (1/(δ:ℝ)) • (v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction)
        rw [← smul_sub, hdecomp]
      exact (norm_one_div_smul_le_iff hδr _ _).mp (hPij ▸ hP_diff)
    have hpar_T0 : |inner ℝ v_ij T₀.direction| ≤ c_label_par := by
      have hSi_eq : S i = (inner ℝ ((T i).midpoint - T₀.midpoint) T₀.direction) •
            T₀.direction := rfl
      have hSj_eq : S j = (inner ℝ ((T j).midpoint - T₀.midpoint) T₀.direction) •
            T₀.direction := rfl
      have hSij : S i - S j = (inner ℝ v_ij T₀.direction) • T₀.direction := by
        rw [hSi_eq, hSj_eq, ← sub_smul, ← inner_sub_left]
        congr 2; rw [hv_ij_def]; abel
      have hSnorm : ‖S i - S j‖ = |inner ℝ v_ij T₀.direction| := by
        rw [hSij, norm_smul, Real.norm_eq_abs, h_unit_d0, mul_one]
      rw [hSnorm] at hS_diff; exact hS_diff
    have hv_ij_norm_bound :
        ‖v_ij‖ ≤ c_label_perp * δ + c_label_par := by
      have hvdec : v_ij =
          (v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction) +
          (inner ℝ v_ij T₀.direction) • T₀.direction := by abel
      calc ‖v_ij‖
          = ‖(v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction) +
              (inner ℝ v_ij T₀.direction) • T₀.direction‖ := by rw [← hvdec]
        _ ≤ ‖v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction‖ +
              ‖(inner ℝ v_ij T₀.direction) • T₀.direction‖ := norm_add_le _ _
        _ = ‖v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction‖ +
              |inner ℝ v_ij T₀.direction| * ‖T₀.direction‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = ‖v_ij - (inner ℝ v_ij T₀.direction) • T₀.direction‖ +
              |inner ℝ v_ij T₀.direction| := by rw [h_unit_d0]; ring
        _ ≤ c_label_perp * δ + c_label_par := by linarith
    have hε_T0_norm : ‖ε • T₀.direction‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, hε_abs, one_mul, h_unit_d0]
    have hTj_unit : ‖(T j).direction‖ = 1 := by
      have := (T j).dist_eq_one
      rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
    have hTi_unit : ‖(T i).direction‖ = 1 := by
      have := (T i).dist_eq_one
      rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
    have h_Tj_εT0 :
        ‖(T j).direction - ε • T₀.direction‖ ≤ C_dir * δ := by
      have h1 : ε • ((T j).direction - ε • T₀.direction) =
          ε • (T j).direction - T₀.direction := by
        rw [smul_sub, smul_smul, hε_sq, one_smul]
      have h2 : ‖ε • ((T j).direction - ε • T₀.direction)‖
          = ‖(T j).direction - ε • T₀.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs, hε_abs, one_mul]
      rw [← h2, h1]; exact hεTj
    have h_inner_εT0 :
        inner ℝ v_ij (ε • T₀.direction) = ε * inner ℝ v_ij T₀.direction := by
      rw [inner_smul_right]
    have h_proj_εT0 :
        (inner ℝ v_ij (ε • T₀.direction)) • (ε • T₀.direction)
          = (inner ℝ v_ij T₀.direction) • T₀.direction := by
      rw [h_inner_εT0, smul_smul]
      rw [show ε * inner ℝ v_ij T₀.direction * ε = ε * ε * inner ℝ v_ij T₀.direction by ring,
          hε_sq, one_mul]
    have hperp_εT0 :
        ‖v_ij - (inner ℝ v_ij (ε • T₀.direction)) • (ε • T₀.direction)‖
          ≤ c_label_perp * δ := by
      rw [h_proj_εT0]; exact hperp_T0
    have hpar_εT0 :
        |inner ℝ v_ij (ε • T₀.direction)| ≤ c_label_par := by
      rw [h_inner_εT0, abs_mul, hε_abs, one_mul]; exact hpar_T0
    have h_ref_a : ‖(T i).direction - (T j).direction‖ ≤ c_pair_dir * δ := by
      have hcld_le : c_label_dir ≤ c_pair_dir := by rw [hcld_def]; linarith
      calc ‖(T i).direction - (T j).direction‖
          ≤ c_label_dir * δ := h_Tij_dir
        _ ≤ c_pair_dir * δ := mul_le_mul_of_nonneg_right hcld_le (by positivity)
    have h_ref_b : ‖(T j).direction - (T j).direction‖ ≤ c_pair_dir * δ := by
      rw [sub_self, norm_zero]; positivity
    have h_εT0_Tj_dir : ‖(ε • T₀.direction) - (T j).direction‖ ≤ C_dir * δ := by
      rw [show ((ε • T₀.direction) - (T j).direction)
              = -((T j).direction - ε • T₀.direction) by rw [neg_sub], norm_neg]
      exact h_Tj_εT0
    have h_ref_c : ‖v_ij - (inner ℝ v_ij (T j).direction) • (T j).direction‖
        ≤ c_pair_perp * δ := by
      have h_total :
          ‖v_ij - (inner ℝ v_ij (T j).direction) • (T j).direction‖
            ≤ c_label_perp * δ + 2 * (c_label_perp * δ + c_label_par) * (C_dir * δ) :=
        perp_shift_combine hε_T0_norm hTj_unit hperp_εT0 hv_ij_norm_bound h_εT0_Tj_dir
      have hC_dir_nn : 0 ≤ C_dir := hCd_pos.le
      have h_clp_nn : 0 ≤ c_label_perp := hclp_pos.le
      have h_clpa_nn : 0 ≤ c_label_par := hclpar_pos.le
      have hδ_nn : 0 ≤ δ := hδ.le
      have h_par_slack : 2 * c_label_par * C_dir * δ ≤ (c_pair_perp / 8) * δ :=
        mul_le_mul_of_nonneg_right h_2clpa_Cdir (by positivity)
      have h_δ_p : δ ≤ δ₀_perp := hδ_le.trans hδ0_le_p
      have h_δDperp : δ * Dperp ≤ c_pair_perp := by
        rw [hδ0p_def] at h_δ_p
        have := mul_le_mul_of_nonneg_right h_δ_p hDperp_pos.le
        rw [div_mul_cancel₀ _ hDperp_pos.ne'] at this
        exact this
      have h_16clperp_Cdir_δ : 16 * c_label_perp * C_dir * δ ≤ c_pair_perp := by
        have h1 : 16 * c_label_perp * C_dir * δ ≤ Dperp * δ := by
          rw [hDperp_def]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h2 : Dperp * δ = δ * Dperp := by ring
        rw [h2] at h1
        linarith
      have h_2clperp_Cdir_δ : 2 * c_label_perp * C_dir * δ ≤ c_pair_perp / 8 := by
        linarith [h_16clperp_Cdir_δ]
      have h_perp_δ2 : 2 * c_label_perp * C_dir * δ * δ ≤ (c_pair_perp / 8) * δ :=
        mul_le_mul_of_nonneg_right h_2clperp_Cdir_δ (by positivity)
      have h_slack_total :
          2 * (c_label_perp * δ + c_label_par) * (C_dir * δ) ≤ (c_pair_perp / 4) * δ := by
        have heq : 2 * (c_label_perp * δ + c_label_par) * (C_dir * δ) =
            2 * c_label_perp * C_dir * δ * δ + 2 * c_label_par * C_dir * δ := by ring
        rw [heq]; linarith
      calc ‖v_ij - (inner ℝ v_ij (T j).direction) • (T j).direction‖
          ≤ c_label_perp * δ + 2 * (c_label_perp * δ + c_label_par) * (C_dir * δ) := h_total
        _ ≤ c_label_perp * δ + (c_pair_perp / 4) * δ := by linarith
        _ = (c_label_perp + c_pair_perp / 4) * δ := by ring
        _ ≤ c_pair_perp * δ := by
            have hle : c_label_perp + c_pair_perp / 4 ≤ c_pair_perp := by
              rw [hclp_def]; linarith
            exact mul_le_mul_of_nonneg_right hle (by positivity)
    have h_ref_d : |inner ℝ v_ij (T j).direction| ≤ c_pair_par := by
      have h_total :
          |inner ℝ v_ij (T j).direction|
            ≤ c_label_par + (c_label_perp * δ + c_label_par) * (C_dir * δ) :=
        par_shift_combine hε_T0_norm hTj_unit hpar_εT0 hv_ij_norm_bound h_εT0_Tj_dir
      have hC_dir_nn : 0 ≤ C_dir := hCd_pos.le
      have h_clp_nn : 0 ≤ c_label_perp := hclp_pos.le
      have h_clpa_nn : 0 ≤ c_label_par := hclpar_pos.le
      have hδ_nn : 0 ≤ δ := hδ.le
      have h_δ_pa : δ ≤ δ₀_par := hδ_le.trans hδ0_le_pa
      have h_δDpar : δ * Dpar ≤ c_pair_par := by
        rw [hδ0pa_def] at h_δ_pa
        have := mul_le_mul_of_nonneg_right h_δ_pa hDpar_pos.le
        rw [div_mul_cancel₀ _ hDpar_pos.ne'] at this
        exact this
      have h_2sum_Cdir_δ :
          2 * (c_label_perp + c_label_par) * C_dir * δ ≤ c_pair_par := by
        have : 2 * (c_label_perp + c_label_par) * C_dir * δ ≤ Dpar * δ := by
          rw [hDpar_def]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have h2 : Dpar * δ = δ * Dpar := by ring
        rw [h2] at this; linarith
      have h_sum_Cdir_δ :
          (c_label_perp + c_label_par) * C_dir * δ ≤ c_pair_par / 2 := by
        linarith [h_2sum_Cdir_δ]
      have h_slack_par :
          (c_label_perp * δ + c_label_par) * (C_dir * δ) ≤ c_pair_par / 2 := by
        have heq :
            (c_label_perp * δ + c_label_par) * (C_dir * δ) =
              c_label_perp * C_dir * δ * δ + c_label_par * C_dir * δ := by ring
        rw [heq]
        have hδ2_le : c_label_perp * C_dir * δ * δ ≤ c_label_perp * C_dir * δ := by
          have hCpos : 0 ≤ c_label_perp * C_dir * δ := by positivity
          have : c_label_perp * C_dir * δ * δ ≤ c_label_perp * C_dir * δ * 1 :=
            mul_le_mul_of_nonneg_left hδ1 hCpos
          linarith
        have hsum_eq :
            c_label_perp * C_dir * δ + c_label_par * C_dir * δ =
              (c_label_perp + c_label_par) * C_dir * δ := by ring
        linarith [h_sum_Cdir_δ]
      calc |inner ℝ v_ij (T j).direction|
          ≤ c_label_par + (c_label_perp * δ + c_label_par) * (C_dir * δ) := h_total
        _ ≤ c_label_par + c_pair_par / 2 := by linarith
        _ ≤ c_pair_par := by linarith [hclpar_le_cpa4]
    -- Conclude: T_i and T_j are not essentially distinct.
    have h_not_ED : ¬ IsEssentiallyDistinct (T i).carrier (T j).carrier :=
      hsliding hδ (hδ_le.trans hδ0_le_sl) (T i) (T j) (T j) h_ref_a h_ref_b h_ref_c h_ref_d
    have h_ED : IsEssentiallyDistinct (T i).carrier (T j).carrier :=
      h_pairwise hi hj hne
    exact h_not_ED h_ED
  -- Cardinality via injection.
  have h_lab_card : s.card ≤ Fintype.card (Fin 2 × Fin N_dir × Fin N_perp × Fin N_par) := by
    have hinj : Set.InjOn lab s := h_inj
    classical
    have := Finset.card_le_card_of_injOn lab (fun i _ => Finset.mem_univ (lab i)) hinj
    simpa using this
  simp [hC_small_def, Fintype.card_prod, Fintype.card_fin] at h_lab_card ⊢
  linarith [h_lab_card]

/-- Small-δ packing bound: for δ below a dimension-dependent threshold δ₀, the cardinality of
any pairwise-ED finset of tubes that are all NOT essentially distinct from a fixed `T₀` is
bounded by a uniform constant. -/
theorem essDist_notED_bound_small (hn : 1 < Module.finrank ℝ E) :
    ∃ (δ₀ : ℝ) (C_small : ℕ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < C_small ∧
      ∀ {ι : Type*} {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ δ₀)
        (s : Finset ι) (T : ι → Tube δ E)
        (T₀ : Tube δ E),
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ s, ¬ IsEssentiallyDistinct (T i).carrier T₀.carrier) →
        s.card ≤ C_small := by
  obtain ⟨C_dir, C_perp, C_long, hCd_pos, hCp_pos, hCl_pos, hnotED⟩ :=
    notED_rescaled_bounds (E := E) hn
  obtain ⟨δ₀, C_small, hδ0_pos, hδ0_le1, hC_pos, hpack⟩ :=
    packing_card_le_of_features (E := E) hn C_dir C_perp C_long hCd_pos hCp_pos hCl_pos
  refine ⟨δ₀, C_small, hδ0_pos, hδ0_le1, hC_pos, ?_⟩
  intro ι δ hδ hδ_le s T T₀ h_pairwise h_notED
  have hδ1 : (δ : ℝ) ≤ 1 := hδ_le.trans hδ0_le1
  have hδ1' : δ ≤ 1 := by exact_mod_cast hδ1
  refine hpack hδ hδ_le s T T₀ h_pairwise ?_
  intro i hi
  obtain ⟨ε, h1, h2, h3, h4⟩ := hnotED hδ hδ1' (T i) T₀ (h_notED i hi)
  exact ⟨ε, h1, h2, h3, h4⟩

set_option maxHeartbeats 2000000 in
-- translation/packing proof body is large; requires elevated heartbeats
/-- **Generic large-δ packing core.**  If a pairwise-ED finset of `δ`-tubes
(with `δ` bounded below by `δ₀ > 0`) has all midpoints within a fixed radius
`Cmid` of a reference point `T₀.midpoint`, then its cardinality is bounded by a
uniform constant.  The midpoint bound is the only "feature" used; it is produced
either by `notED_rescaled_bounds` or by `containment_features`. -/
theorem packing_card_le_of_features_large (hn : 1 < Module.finrank ℝ E)
    (Cmid : ℝ) (hCmid : 0 ≤ Cmid) (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) :
    ∃ C_large : ℕ, 0 < C_large ∧
      ∀ {ι : Type*} {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ 1) (_ : δ₀ < (δ : ℝ))
        (s : Finset ι) (T : ι → Tube δ E)
        (T₀ : Tube δ E),
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ s, ‖(T i).midpoint - T₀.midpoint‖ ≤ Cmid) →
        s.card ≤ C_large := by
  classical
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega : 0 < Module.finrank ℝ E)
  set C_crude : ℝ := Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)
  have hC_crude_pos : 0 < C_crude := Tube.card_le_of_EssDistinct.C_pos
  set n := Module.finrank ℝ E with hn_def
  -- Carrier-extent bound: each (T i).carrier is within R of T₀.midpoint, where
  -- R := Cmid + 2.
  set R : ℝ := Cmid + 2 with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  set C_real : ℝ := C_crude * (R / δ₀) ^ (2 * n) with hC_real_def
  have hC_real_nonneg : 0 ≤ C_real := by
    rw [hC_real_def]
    refine mul_nonneg hC_crude_pos.le ?_
    exact pow_nonneg (div_nonneg hR_pos.le hδ₀_pos.le) _
  refine ⟨⌈C_real⌉₊ + 1, by omega, ?_⟩
  intro ι δ hδ hδ1 hδ_gt s T T₀ h_pairwise h_mid_bd
  -- Each (T i).midpoint is within Cmid of T₀.midpoint
  have h_unit_d0 : ‖T₀.direction‖ = 1 := by
    have := T₀.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  -- For each i ∈ s, every p ∈ (T i).carrier satisfies ‖p - T₀.midpoint‖ ≤ R.
  have h_carr_bd : ∀ i ∈ s, ∀ p ∈ (T i).carrier, ‖p - T₀.midpoint‖ ≤ R := by
    intro i hi p hp
    rw [(T i).carrier_eq] at hp
    obtain ⟨z, hz_seg, hpz⟩ := Set.mem_iUnion₂.mp hp
    -- z is in segment ℝ (T i).x (T i).y, so ‖z - (T i).midpoint‖ ≤ 1/2.
    obtain ⟨a, b, ha, hb, hab, hz_eq⟩ := hz_seg
    -- z - midpoint = (1/2 - b)·((T i).y - (T i).x)
    have hz_mid : z - (T i).midpoint = (1/2 - b) • ((T i).x - (T i).y) := by
      have hmid_eq : (T i).midpoint = (1/2 : ℝ) • (T i).x + (1/2 : ℝ) • (T i).y := by
        change (1/2 : ℝ) • ((T i).x + (T i).y) = _
        rw [smul_add]
      rw [← hz_eq, hmid_eq, show a = 1 - b from by linarith, sub_smul, one_smul, sub_smul]
      module
    have hxy_norm : ‖(T i).x - (T i).y‖ = 1 := by
      have := (T i).dist_eq_one
      rwa [dist_eq_norm] at this
    have hz_mid_norm : ‖z - (T i).midpoint‖ ≤ 1/2 := by
      rw [hz_mid, norm_smul, Real.norm_eq_abs, hxy_norm, mul_one, abs_le]
      constructor <;> linarith
    have hp_z : ‖p - z‖ ≤ δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hpz
      exact hpz
    -- ‖p - T₀.mid‖ ≤ ‖p - z‖ + ‖z - (T i).mid‖ + ‖(T i).mid - T₀.mid‖
    have hmid_bd : ‖(T i).midpoint - T₀.midpoint‖ ≤ Cmid := h_mid_bd i hi
    have h_norm_sum : ‖(p - z) + (z - (T i).midpoint)‖ ≤ ‖p - z‖ + ‖z - (T i).midpoint‖ :=
      norm_add_le _ _
    calc ‖p - T₀.midpoint‖
        = ‖(p - z) + (z - (T i).midpoint) + ((T i).midpoint - T₀.midpoint)‖ := by
          congr 1; abel
      _ ≤ ‖(p - z) + (z - (T i).midpoint)‖ + ‖(T i).midpoint - T₀.midpoint‖ :=
          norm_add_le _ _
      _ ≤ (δ + 1/2) + Cmid := by
          linarith [h_norm_sum, hp_z, hz_mid_norm, hmid_bd]
      _ ≤ R := by rw [hR_def]; linarith
  -- Translate by -T₀.midpoint.
  set T' : ι → Tube δ E := fun i => (T i).translate (-T₀.midpoint) with hT'_def
  -- Carrier of T' i equals image of T i carrier under translation by -T₀.midpoint.
  have hT'_carrier : ∀ i : ι,
      (T' i).carrier = (fun x : E => -T₀.midpoint + x) '' (T i).carrier := by
    intro i
    rw [hT'_def, Tube.translate_carrier]
    have h1 : Function.LeftInverse (fun x : E => -(-T₀.midpoint) + x)
              (fun x : E => -T₀.midpoint + x) := fun x => by
      change -(-T₀.midpoint) + (-T₀.midpoint + x) = x
      rw [neg_neg]; abel
    have h2 : Function.RightInverse (fun x : E => -(-T₀.midpoint) + x)
              (fun x : E => -T₀.midpoint + x) := fun x => by
      change -T₀.midpoint + (-(-T₀.midpoint) + x) = x
      rw [neg_neg]; abel
    have hfn : Set.image (fun x : E => -T₀.midpoint + x)
               = Set.preimage (fun x : E => -(-T₀.midpoint) + x) :=
      Set.image_eq_preimage_of_inverse h1 h2
    exact (congrFun hfn (T i).carrier).symm
  -- Translated tube carriers fit in closedBall(0, R).
  have hT'_in_ball : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall (0 : E) R := by
    intro i hi q hq
    rw [hT'_carrier i] at hq
    obtain ⟨p, hp_mem, hpq_eq⟩ := hq
    rw [Metric.mem_closedBall, dist_zero_right]
    have hbd : ‖p - T₀.midpoint‖ ≤ R := h_carr_bd i hi p hp_mem
    have : q = -T₀.midpoint + p := hpq_eq.symm
    rw [this]
    have hreplace : -T₀.midpoint + p = p - T₀.midpoint := by abel
    rw [hreplace]
    exact hbd
  -- Pairwise ED is preserved by translation.
  have hT'_ed : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
    intro i hi j hj hij
    have h_orig := h_pairwise hi hj hij
    rw [hT'_carrier i, hT'_carrier j]
    exact (isEssentiallyDistinct_translate _ _ _).mpr h_orig
  -- Apply crude bound to T'
  have h_crude : (s.card : ℝ) ≤ C_crude * (R / δ) ^ (2 * n) :=
    Tube.card_le_of_EssDistinct hδ R s T' hT'_in_ball hT'_ed
  -- Use δ ≥ δ₀ to bound (R / δ) ^ (2n) ≤ (R / δ₀) ^ (2n).
  have hRδ_pos : 0 < R / δ := div_pos hR_pos hδ
  have hRδ_le : R / δ ≤ R / δ₀ :=
    div_le_div_of_nonneg_left hR_pos.le hδ₀_pos hδ_gt.le
  have hpow_le : (R / δ) ^ (2 * n) ≤ (R / δ₀) ^ (2 * n) :=
    pow_le_pow_left₀ hRδ_pos.le hRδ_le _
  have h_card_real : (s.card : ℝ) ≤ C_real := by
    rw [hC_real_def]
    refine le_trans h_crude ?_
    exact mul_le_mul_of_nonneg_left hpow_le hC_crude_pos.le
  -- Convert to natural number bound.
  have h_le_ceil : (s.card : ℝ) ≤ (⌈C_real⌉₊ : ℝ) :=
    h_card_real.trans (Nat.le_ceil _)
  have h_le_ceil_succ : (s.card : ℝ) ≤ ((⌈C_real⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h_le_ceil_succ

/-- Large-δ packing bound: for any positive lower bound `δ₀` on δ, the cardinality of any
pairwise-ED finset of tubes that are all NOT essentially distinct from a fixed `T₀` is bounded
by a uniform constant (depending on `δ₀`). -/
theorem essDist_notED_bound_large (hn : 1 < Module.finrank ℝ E)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) :
    ∃ C_large : ℕ, 0 < C_large ∧
      ∀ {ι : Type*} {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ 1) (_ : δ₀ < (δ : ℝ))
        (s : Finset ι) (T : ι → Tube δ E)
        (T₀ : Tube δ E),
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ s, ¬ IsEssentiallyDistinct (T i).carrier T₀.carrier) →
        s.card ≤ C_large := by
  obtain ⟨C_dir, C_perp, C_long, hCd_pos, hCp_pos, hCl_pos, hnotED⟩ :=
    notED_rescaled_bounds (E := E) hn
  obtain ⟨C_large, hC_large_pos, hpack⟩ :=
    packing_card_le_of_features_large (E := E) hn (C_perp + C_long)
      (by positivity) δ₀ hδ₀_pos
  refine ⟨C_large, hC_large_pos, ?_⟩
  intro ι δ hδ hδ1 hδ_gt s T T₀ h_pairwise h_notED
  have h_unit_d0 : ‖T₀.direction‖ = 1 := by
    have := T₀.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  refine hpack hδ hδ1 hδ_gt s T T₀ h_pairwise ?_
  intro i hi
  obtain ⟨ε, _hε, _hε_dir, hperp, hpar⟩ := hnotED hδ hδ1 (T i) T₀ (h_notED i hi)
  set m : E := (T i).midpoint - T₀.midpoint with hm_def
  set par : ℝ := inner ℝ m T₀.direction with hpar_def
  have hperp_le : ‖m - par • T₀.direction‖ ≤ C_perp := by
    have hδ_mul : C_perp * (δ : ℝ) ≤ C_perp := by nlinarith [hCp_pos.le]
    exact hperp.trans hδ_mul
  have hpar_le : ‖par • T₀.direction‖ ≤ C_long := by
    rw [norm_smul, h_unit_d0, mul_one, Real.norm_eq_abs]; exact hpar
  have hmeq : m = (m - par • T₀.direction) + par • T₀.direction := by abel
  calc ‖m‖
      = ‖(m - par • T₀.direction) + par • T₀.direction‖ := by rw [← hmeq]
    _ ≤ ‖m - par • T₀.direction‖ + ‖par • T₀.direction‖ := norm_add_le _ _
    _ ≤ C_perp + C_long := add_le_add hperp_le hpar_le

end
end Kakeya
