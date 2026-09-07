import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaLocalPatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaPermutedDirection
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Pointwise
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

/-- Projection is nonexpansive. -/
lemma proj_nonexpansive (y p : E (m + 1)) :
    dist (proj y) (proj p) ≤ dist y p := by
  have h2 : ‖proj y - proj p‖ ^ 2 = ∑ i : Fin m, ((y - p) (Fin.castSucc i)) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, proj_apply] <;> rfl
  have h3 : ‖y - p‖ ^ 2 = ∑ i : Fin (m + 1), ((y - p) i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq (y - p)
  have h41 : (∑ i : Fin (m + 1), ((y - p) i) ^ 2) =
      (∑ i : Fin m, ((y - p) (Fin.castSucc i)) ^ 2) + ((y - p) (Fin.last m)) ^ 2 := by
    rw [Fin.sum_univ_castSucc] <;> rfl
  have h4 : (∑ i : Fin m, ((y - p) (Fin.castSucc i)) ^ 2) ≤
      (∑ i : Fin (m + 1), ((y - p) i) ^ 2) := by
    rw [h41] <;> exact le_add_of_nonneg_right (by positivity)
  have h5 : ‖proj y - proj p‖ ^ 2 ≤ ‖y - p‖ ^ 2 := by
    rw [h2, h3] <;> exact h4
  have h6 : 0 ≤ ‖proj y - proj p‖ := by positivity
  have h7 : 0 ≤ ‖y - p‖ := by positivity
  have h8 : ‖proj y - proj p‖ ≤ ‖y - p‖ := by nlinarith
  exact h8

/-- For t between t1 and t2, unsplit z t is a convex combination of unsplit z t1, unsplit z t2. -/
lemma unsplit_convex_comb (z : E m) (t1 t2 t : ℝ) (c : ℝ)
    (hc1 : 0 ≤ c) (hc2 : c ≤ 1) (ht : t = (1 - c) * t1 + c * t2) :
    unsplit z t = (1 - c) • unsplit z t1 + c • unsplit z t2 := by
  let sE : ℝ →L[ℝ] E (m + 1) := scaleE
  have h1 : ∀ (x : ℝ), unsplit z x = inclEm z + sE x := fun x => unsplit_eq x z
  have h_smul1 : sE ((1 - c) * t1) = (1 - c) • sE t1 := by
    have h : (1 - c) * t1 = (1 - c) • t1 := by simp [smul_eq_mul]
    rw [h, sE.map_smul]
  have h_smul2 : sE (c * t2) = c • sE t2 := by
    have h : c * t2 = c • t2 := by simp [smul_eq_mul]
    rw [h, sE.map_smul]
  have h2 : sE ((1 - c) * t1 + c * t2) = (1 - c) • sE t1 + c • sE t2 := by
    rw [sE.map_add, h_smul1, h_smul2]
  have h6 : (1 - c) + c = 1 := by ring
  have h7 : (1 - c) • inclEm z + c • inclEm z = inclEm z := by
    have h9 : (1 - c) • inclEm z + c • inclEm z = ((1 - c) + c) • inclEm z := by
      rw [←add_smul]
    rw [h9, h6] <;> simp
  have h_main : (1 - c) • (inclEm z + sE t1) + c • (inclEm z + sE t2) =
      inclEm z + ((1 - c) • sE t1 + c • sE t2) := by
    have h8 : (1 - c) • (inclEm z + sE t1) + c • (inclEm z + sE t2) =
        ((1 - c) • inclEm z + c • inclEm z) + ((1 - c) • sE t1 + c • sE t2) := by
      rw [smul_add, smul_add] <;> abel
    rw [h8, h7] <;> abel
  calc
    unsplit z t
      = inclEm z + sE t := h1 t
    _ = inclEm z + sE ((1 - c) * t1 + c * t2) := by rw [ht]
    _ = inclEm z + ((1 - c) • sE t1 + c • sE t2) := by rw [h2]
    _ = (1 - c) • (inclEm z + sE t1) + c • (inclEm z + sE t2) := h_main.symm
    _ = (1 - c) • unsplit z t1 + c • unsplit z t2 := by
      rw [←h1 t1, ←h1 t2]

/-- **Orientation helper**: local orientation equivalence at a graph point. -/
lemma orientation_helper
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u) (s : ℝ)
    (g : E m → ℝ) {L : NNReal} (hg : LipschitzWith L g)
    (W : Set (E (m + 1))) (hW_open : IsOpen W)
    (hW_prop : ∀ y ∈ W, 0 < (fderiv ℝ u y) (eLast : E (m + 1)))
    (B A : Set (E m)) (hA_sub_interior_B : A ⊆ interior B)
    (h_u_graph : ∀ z ∈ B, u (graphMap g z) = s)
    (h_graph_W : ∀ z ∈ B, graphMap g z ∈ W)
    (z : E m) (hz : z ∈ A) :
    ∃ (r : ℝ), 0 < r ∧
      ball (graphMap g z) r ∩ {y | u y > s} =
      ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
  let p := graphMap g z
  have hz_B : z ∈ B := interior_subset (hA_sub_interior_B hz)
  have hp_W : p ∈ W := h_graph_W z hz_B

  have h_g_cont : Continuous g := hg.continuous
  have h_graphmap_cont : Continuous (graphMap g) := by
    have h_eq : (graphMap g) = fun z : E m => inclEm z + scaleE (g z) := by
      funext z; exact unsplit_eq (g z) z
    rw [h_eq]
    exact inclEm.continuous.add (scaleE.continuous.comp h_g_cont)

  rcases Metric.mem_nhds_iff.mp (hW_open.mem_nhds hp_W) with ⟨R, hR_pos, hball_R⟩

  have h1_ev : ∀ᶠ z' in nhds z, dist (graphMap g z') p < R / 2 :=
    h_graphmap_cont.continuousAt.eventually (Metric.ball_mem_nhds p (by linarith))
  rcases Metric.mem_nhds_iff.mp h1_ev with ⟨δ1, hδ1_pos, hball1⟩

  have h2_ev : ∀ᶠ z' in nhds z, z' ∈ interior B :=
    isOpen_interior.mem_nhds (hA_sub_interior_B hz)
  rcases Metric.mem_nhds_iff.mp h2_ev with ⟨δ2, hδ2_pos, hball2⟩

  let r0 : ℝ := min (min δ1 δ2) (R / 2)
  have hr0_pos : 0 < r0 := by positivity
  let r : ℝ := r0 / 2
  have hr_pos : 0 < r := by positivity
  have hr_lt_delta1 : r < δ1 := by
    have h1 : r0 ≤ δ1 := by simp [r0] <;> exact min_le_left _ _
    have h2 : 0 < r0 := hr0_pos
    dsimp only [r] <;> linarith
  have hr_lt_delta2 : r < δ2 := by
    have h1 : r0 ≤ δ2 := by simp [r0] <;> exact min_le_of_right_le _ _ (min_le_right _ _)
    have h2 : 0 < r0 := hr0_pos
    dsimp only [r] <;> linarith
  have hr_lt_R2 : r < R / 2 := by
    have h1 : r0 ≤ R / 2 := by simp [r0] <;> exact min_le_right _ _
    have h2 : 0 < r0 := hr0_pos
    dsimp only [r] <;> linarith

  have h_main : ∀ y ∈ ball p r,
      u y > s ↔ (y : E (m + 1)) (Fin.last m) > g (proj y) := by
    intro y hy
    have h_y_dist : dist y p < r := mem_ball.mp hy
    set z' := proj y with hz'_def
    have h_proj_p : proj p = z := by
      rw [show p = graphMap g z from rfl]
      exact graphMap_proj g z
    have h_proj_dist : dist z' z ≤ dist y p := by
      have h := proj_nonexpansive y p
      rw [h_proj_p] at h
      exact h
    have h_z'_interior_B : z' ∈ interior B := by
      have h : dist z' z < δ2 := by linarith
      exact hball2 (mem_ball.mpr h)
    have h_z'_B : z' ∈ B := interior_subset h_z'_interior_B
    have h4 : dist (graphMap g z') p < R / 2 := by
      have h5 : dist z' z < δ1 := by linarith
      exact hball1 (mem_ball.mpr h5)
    have h6 : y ∈ ball p (R / 2) := by
      simp only [mem_ball] <;> linarith
    have h7 : graphMap g z' ∈ ball p (R / 2) := by
      simp only [mem_ball] <;> exact h4

    let t1 := g z'
    let t2 := y (Fin.last m)
    let h_fn : ℝ → ℝ := fun t => u (unsplit z' t)

    have h_y_eq : y = unsplit z' t2 := by
      ext i
      by_cases hlt : i.val < m
      · let j : Fin m := ⟨i.val, hlt⟩
        have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
        rw [hi]
        simp [hz'_def, unsplit, graphMap_apply_castSucc, proj_apply] <;> rfl
      · have hlast : i = Fin.last m := by apply Fin.ext; simp [hlt] <;> omega
        rw [hlast]
        simp [hz'_def, unsplit, graphMap_apply_last] <;> rfl

    have h_segment_in_W : ∀ t ∈ Set.Icc (min t1 t2) (max t1 t2),
        unsplit z' t ∈ W := by
      intro t ht
      have h_end1 : unsplit z' t1 ∈ ball p R := by
        have h_eq1 : unsplit z' t1 = graphMap g z' := by rfl
        rw [h_eq1]
        simp only [mem_ball] <;> linarith
      have h_end2 : unsplit z' t2 ∈ ball p R := by
        have h_eq2 : unsplit z' t2 = y := by
          ext i
          by_cases hlt : i.val < m
          · let j : Fin m := ⟨i.val, hlt⟩
            have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
            rw [hi]
            simp [hz'_def, unsplit, graphMap_apply_castSucc, proj_apply] <;> rfl
          · have hlast : i = Fin.last m := by apply Fin.ext; simp [hlt] <;> omega
            rw [hlast]
            simp [hz'_def, unsplit, graphMap_apply_last] <;> rfl
        rw [h_eq2]
        simp only [mem_ball] <;> linarith
      have h_ball_conv : Convex ℝ (ball p R) := convex_ball p R
      have h_in_ball : unsplit z' t ∈ ball p R := by
        by_cases h_order : t1 ≤ t2
        · have hti1 : t1 ≤ t := by
            have h9 : min t1 t2 ≤ t := ht.1
            simpa [h_order, min_eq_left] using h9
          have hti2 : t ≤ t2 := by
            have h10 : t ≤ max t1 t2 := ht.2
            simpa [h_order, max_eq_right] using h10
          by_cases heq : t1 = t2
          · have ht_eq : t = t1 := by linarith
            rw [ht_eq]
            exact h_end1
          · have hpos : 0 < t2 - t1 := by
              have h : t1 < t2 := lt_of_le_of_ne h_order heq
              exact sub_pos.mpr h
            let c : ℝ := (t - t1) / (t2 - t1)
            have hc1 : 0 ≤ c := by dsimp only [c] <;> apply div_nonneg <;> linarith
            have hc2 : c ≤ 1 := by dsimp only [c] <;> rw [div_le_one hpos] <;> linarith
            have h_t_eq : t = (1 - c) * t1 + c * t2 := by
              dsimp only [c] <;> field_simp [hpos.ne'] <;> ring
            have h1mc : 0 ≤ 1 - c := by linarith
            have hsum : (1 - c) + c = 1 := by ring
            have h_conv_pt : (1 - c) • unsplit z' t1 + c • unsplit z' t2 ∈ ball p R :=
              h_ball_conv h_end1 h_end2 h1mc hc1 hsum
            have h_eq : (1 - c) • unsplit z' t1 + c • unsplit z' t2 = unsplit z' t :=
              (unsplit_convex_comb z' t1 t2 t c hc1 hc2 h_t_eq).symm
            rw [←h_eq]
            exact h_conv_pt
        · have h_order2 : t2 ≤ t1 := by linarith
          have hti1 : t2 ≤ t := by
            have h9 : min t1 t2 ≤ t := ht.1
            simpa [h_order2, min_eq_right] using h9
          have hti2 : t ≤ t1 := by
            have h10 : t ≤ max t1 t2 := ht.2
            simpa [h_order2, max_eq_left] using h10
          by_cases heq : t2 = t1
          · have ht_eq : t = t1 := by linarith
            rw [ht_eq]
            exact h_end1
          · have hne : t1 ≠ t2 := by intro h; exact heq h.symm
            have hpos : 0 < t1 - t2 := by
              have h : t2 < t1 := lt_of_le_of_ne h_order2 hne.symm
              exact sub_pos.mpr h
            let c : ℝ := (t - t2) / (t1 - t2)
            have hc1 : 0 ≤ c := by dsimp only [c] <;> apply div_nonneg <;> linarith
            have hc2 : c ≤ 1 := by dsimp only [c] <;> rw [div_le_one hpos] <;> linarith
            have h_t_eq : t = (1 - c) * t2 + c * t1 := by
              dsimp only [c] <;> field_simp [hpos.ne'] <;> ring
            have h1mc : 0 ≤ 1 - c := by linarith
            have hsum : (1 - c) + c = 1 := by ring
            have h_conv_pt : (1 - c) • unsplit z' t2 + c • unsplit z' t1 ∈ ball p R :=
              h_ball_conv h_end2 h_end1 h1mc hc1 hsum
            have h_eq : (1 - c) • unsplit z' t2 + c • unsplit z' t1 = unsplit z' t :=
              (unsplit_convex_comb z' t2 t1 t c hc1 hc2 h_t_eq).symm
            rw [←h_eq]
            exact h_conv_pt
      exact hball_R h_in_ball

    have h_deriv : ∀ t ∈ Set.Icc (min t1 t2) (max t1 t2),
        HasDerivAt h_fn ((fderiv ℝ u (unsplit z' t)) (eLast : E (m + 1))) t := by
      intro t _
      have h_diff : Differentiable ℝ u := (contDiff_one_iff_fderiv.mp hu).1
      have h_fd : HasFDerivAt u (fderiv ℝ u (unsplit z' t)) (unsplit z' t) :=
        h_diff.differentiableAt.hasFDerivAt
      have h_unsplit_fd : HasFDerivAt (fun t : ℝ => unsplit z' t) scaleE t := by
        have h : (fun t : ℝ => unsplit z' t) = fun t => inclEm z' + scaleE t := by
          funext t; exact unsplit_eq t z'
        rw [h]
        have h_const : HasStrictFDerivAt (fun (_ : ℝ) => inclEm z') (0 : ℝ →L[ℝ] E (m + 1)) t :=
          hasStrictFDerivAt_const (x := t) (inclEm z')
        have h_scale : HasStrictFDerivAt (scaleE : ℝ → E (m + 1)) scaleE t :=
          scaleE.hasStrictFDerivAt
        have h_sum : HasStrictFDerivAt (fun t : ℝ => inclEm z' + scaleE t) (0 + scaleE : ℝ →L[ℝ] E (m + 1)) t :=
          h_const.add h_scale
        have h_zero : (0 + scaleE : ℝ →L[ℝ] E (m + 1)) = scaleE := by simp
        rw [h_zero] at h_sum
        exact h_sum.hasFDerivAt
      have h_comp : HasFDerivAt h_fn
          (fderiv ℝ u (unsplit z' t) ∘L scaleE) t :=
        h_fd.comp t h_unsplit_fd
      have h10 : HasDerivAt h_fn ((fderiv ℝ u (unsplit z' t) ∘L scaleE) 1) t :=
        h_comp.hasDerivAt
      convert h10 using 1
      <;> simp [scaleE] <;> rfl

    have h_deriv_pos : ∀ t ∈ Set.Icc (min t1 t2) (max t1 t2),
        0 < deriv h_fn t := by
      intro t ht
      have h9 : HasDerivAt h_fn ((fderiv ℝ u (unsplit z' t)) (eLast : E (m + 1))) t :=
        h_deriv t ht
      have h10 : deriv h_fn t = (fderiv ℝ u (unsplit z' t)) (eLast : E (m + 1)) := h9.deriv
      rw [h10]
      exact hW_prop (unsplit z' t) (h_segment_in_W t ht)

    have h_unsplit_cont : Continuous (fun t : ℝ => unsplit z' t) := by
      have h : (fun t : ℝ => unsplit z' t) = fun t => inclEm z' + scaleE t := by
        funext t; exact unsplit_eq t z'
      rw [h]
      exact continuous_const.add scaleE.continuous
    have h_cont_fn : ContinuousOn h_fn (Set.Icc (min t1 t2) (max t1 t2)) :=
      (hu.continuous.comp h_unsplit_cont).continuousOn

    have h_strict_mono : StrictMonoOn h_fn (Set.Icc (min t1 t2) (max t1 t2)) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) h_cont_fn
        (fun x hx => h_deriv_pos x (interior_subset hx))

    have h_val1 : h_fn t1 = s := by
      have h_eq1 : h_fn t1 = u (graphMap g z') := by rfl
      rw [h_eq1]
      exact h_u_graph z' h_z'_B

    have h_val2 : h_fn t2 = u y := by
      simpa [h_fn, h_y_eq] using rfl

    have h_t1_in : t1 ∈ Set.Icc (min t1 t2) (max t1 t2) := by
      simp [le_refl] <;> exact le_max_left _ _
    have h_t2_in : t2 ∈ Set.Icc (min t1 t2) (max t1 t2) := by
      simp [le_refl] <;> exact le_max_right _ _

    have h_iff : h_fn t2 > h_fn t1 ↔ t2 > t1 := by
      constructor
      · intro h
        by_contra h'
        have h'' : t2 ≤ t1 := by linarith
        have h3 : h_fn t2 ≤ h_fn t1 := by
          if h4 : t2 < t1 then
            exact (h_strict_mono h_t2_in h_t1_in h4).le
          else
            have h5 : t2 = t1 := by linarith
            rw [h5]
        linarith
      · intro h
        exact h_strict_mono h_t1_in h_t2_in h

    rw [h_val2, h_val1] at h_iff
    exact h_iff

  have h_set_eq : ball p r ∩ {y | u y > s} =
      ball p r ∩ {p | p (Fin.last m) > g (proj p)} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨h.1, (h_main y h.1).mp h.2⟩
    · intro h
      exact ⟨h.1, (h_main y h.1).mpr h.2⟩

  exact ⟨r, hr_pos, h_set_eq⟩

/-!
# Local Graph Patch for Regular Level Sets

Proves `local_graph_patch_last_pos`: given a C¹ function `u` and a point
`x0` on `{u=s}` with `∂u/∂eLast > 0`, produce a local oriented Lipschitz
graph patch using the inverse function theorem.

## Proof route

1. Call `local_coarea_patch_last` to get `φ : OpenPartialHomeomorph` with
   `φ y = projHCL y + u y • eLast = unsplit (proj y) (u y)`.
2. Define `g0(z) := last coordinate of φ.symm(unsplit z s)` for z near `proj x0`.
3. `g0` is C¹ on a compact neighborhood `B`, hence Lipschitz there.
4. Extend `g0` to a globally Lipschitz `g` via McShane.
5. Use a smaller compact `A ⊂ interior B` for the patch domain.
6. Prove cover, graph-subset-level-set, and orientation properties.
-/

-- ============================================================================
-- Helper: projHCL y = inclEm (proj y)
-- ============================================================================

lemma projHCL_eq_inclEm_proj (y : E (m + 1)) :
    projHCL y = inclEm (proj y) := by
  ext i
  by_cases hlt : i.val < m
  · let j : Fin m := ⟨i.val, hlt⟩
    have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
    rw [hi]
    have h_elast0 : (eLast : E (m + 1)) (Fin.castSucc j) = 0 := by
      simp [eLast, EuclideanSpace.single_apply] <;> omega
    have h_coord : coordECL y = y (Fin.last m) := by rfl
    have h_projHCL : (projHCL y) (Fin.castSucc j) = y (Fin.castSucc j) := by
      simp [projHCL, h_coord, h_elast0, add_apply] <;> ring
    have h_incl : (inclEm (proj y)) (Fin.castSucc j) = y (Fin.castSucc j) := by
      have h_incl_def : inclEm (proj y) = F_lin (0 : E m →L[ℝ] ℝ) (proj y) := by rfl
      rw [h_incl_def]
      have h : (F_lin (0 : E m →L[ℝ] ℝ) (proj y)) (Fin.castSucc j) = (proj y) j :=
        F_lin_apply_castSucc (0 : E m →L[ℝ] ℝ) (proj y) j
      rw [h, proj_apply]
    rw [h_projHCL, h_incl]
  · have hlast : i = Fin.last m := by apply Fin.ext; simp [hlt] <;> omega
    rw [hlast]
    have h1 : (projHCL y) (Fin.last m) = coordECL (projHCL y) := by rfl
    have h1' : (projHCL y) (Fin.last m) = 0 := by
      rw [h1, coordECL_projHCL]
    have h2 : (inclEm (proj y)) (Fin.last m) = 0 := by
      have h_incl_def : inclEm (proj y) = F_lin (0 : E m →L[ℝ] ℝ) (proj y) := by rfl
      rw [h_incl_def]
      exact F_lin_apply_last (0 : E m →L[ℝ] ℝ) (proj y)
    rw [h1', h2]

/-- Property that a set is a closed ball. -/
structure IsClosedBall {α : Type*} [MetricSpace α] (s : Set α) : Prop where
  proof : ∃ c r, s = closedBall c r

-- ============================================================================
-- Local graph patch (eLast direction, positive derivative)
-- ============================================================================

/-- **Local level-set graph patch** (eLast direction, ∂u/∂eLast > 0).

Given `x0` on `{u=s}` with `∂u/∂eLast > 0`, produce a graph function `g`,
compact domain `A`, and open neighborhood `N` of `x0` such that:
- `N ∩ {u=s} ⊆ graphMap g '' A`
- `graphMap g '' A ⊆ {u=s}`
- `g` is Lipschitz
- `{u > s}` is locally above the graph -/
lemma local_graph_patch_last_pos
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (s : ℝ) (x0 : E (m + 1)) (hx0 : u x0 = s)
    (h_pos : 0 < (fderiv ℝ u x0) (eLast : E (m + 1))) :
    ∃ (g : E m → ℝ) (L : NNReal) (A : Set (E m)) (N : Set (E (m + 1))),
      IsOpen N ∧ x0 ∈ N ∧ IsCompact A ∧
      IsClosedBall A ∧
      graphMap g '' interior A ⊆ N ∧
      LipschitzWith L g ∧
      (N ∩ {y | u y = s}) ⊆ graphMap g '' A ∧
      graphMap g '' A ⊆ {y | u y = s} ∧
      ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
        ball (graphMap g z) r ∩ {y | u y > s} =
        ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
  have h_ne : (fderiv ℝ u x0) (eLast : E (m + 1)) ≠ 0 := h_pos.ne'
  rcases local_coarea_patch_last u hu x0 h_ne with
    ⟨V, φ, hV_open, hx0_V, hφ_eq, hsymm_diff, hV_source, hV_reg⟩

  -- Key equality: φ y = unsplit (proj y) (u y)
  have hφ_unsplit : ∀ y : E (m + 1), φ y = unsplit (proj y) (u y) := by
    intro y
    have h1 : φ y = projHCL y + u y • (eLast : E (m + 1)) := by
      rw [hφ_eq] <;> rfl
    rw [h1]
    have h2 : projHCL y = inclEm (proj y) := projHCL_eq_inclEm_proj y
    rw [h2]
    have h3 : u y • (eLast : E (m + 1)) = scaleE (u y) := by
      ext i; simp [scaleE] <;> ring
    rw [h3]
    exact (unsplit_eq (u y) (proj y)).symm

  let z0 := proj x0

  have hx0_source : x0 ∈ φ.source := hV_source hx0_V
  have hφ_x0 : φ x0 = unsplit z0 s := by
    rw [hφ_unsplit x0, hx0]
  have h_target_z0 : unsplit z0 s ∈ φ.target := by
    rw [←hφ_x0]
    exact φ.map_source hx0_source

  -- U_target := {z | unsplit z s ∈ φ.target}, open neighborhood of z0
  let U_target : Set (E m) := {z | unsplit z s ∈ φ.target}
  have h_cont_unsplit : Continuous (fun z : E m => unsplit z s) := by
    have h : (fun z : E m => unsplit z s) = fun z => inclEm z + scaleE s := by
      funext z; exact unsplit_eq s z
    rw [h]; fun_prop
  have hU_target_open : IsOpen U_target :=
    φ.open_target.preimage h_cont_unsplit
  have hz0_U_target : z0 ∈ U_target := h_target_z0

  -- W := {y | ∂u/∂eLast > 0}, open neighborhood of x0
  let W : Set (E (m + 1)) := {y | 0 < (fderiv ℝ u y) (eLast : E (m + 1))}
  have h_cont_partial : Continuous (fun y : E (m + 1) => (fderiv ℝ u y) (eLast : E (m + 1))) := by
    have h1 : Continuous (fderiv ℝ u) := (contDiff_one_iff_fderiv.mp hu).2
    have h2 : Continuous (fun L : (E (m + 1) →L[ℝ] ℝ) => L (eLast : E (m + 1))) := by exact continuous_eval_const eLast
    exact h2.comp h1
  have hW_open : IsOpen W := isOpen_lt continuous_const h_cont_partial
  have hx0_W : x0 ∈ W := h_pos

  -- h_map(z) := φ.symm(unsplit z s)
  let h_map : E m → E (m + 1) := fun z => φ.symm (unsplit z s)
  have h_cont_hmap : ContinuousOn h_map U_target :=
    φ.continuousOn_symm.comp h_cont_unsplit.continuousOn (fun _ h => h)
  have h_hmap_z0 : h_map z0 = x0 := by
    dsimp only [h_map]
    have h : φ.symm (φ x0) = x0 := φ.left_inv hx0_source
    rw [hφ_x0] at *
    <;> exact h

  -- Get a ball around z0 where z ∈ U_target AND h_map z ∈ W
  have h1 : ∀ᶠ z in nhds z0, z ∈ U_target := hU_target_open.mem_nhds hz0_U_target
  have h_hmap_cont_at_z0 : ContinuousAt h_map z0 :=
    h_cont_hmap.continuousAt (hU_target_open.mem_nhds hz0_U_target)
  have h2 : ∀ᶠ z in nhds z0, h_map z ∈ W :=
    h_hmap_cont_at_z0.eventually (hW_open.mem_nhds (by simpa [h_hmap_z0] using hx0_W))
  have h2V : ∀ᶠ z in nhds z0, h_map z ∈ V :=
    h_hmap_cont_at_z0.eventually (hV_open.mem_nhds (by simpa [h_hmap_z0] using hx0_V))
  have h3 : ∀ᶠ z in nhds z0, z ∈ U_target ∧ h_map z ∈ W ∧ h_map z ∈ V :=
    h1.and (h2.and h2V)
  rcases Metric.mem_nhds_iff.mp h3 with ⟨rA, hrA_pos, hball⟩

  -- B := closedBall z0 (rA / 2) (compact set for Lipschitz extension)
  let B : Set (E m) := closedBall z0 (rA / 2)
  have hB_compact : IsCompact B := isCompact_closedBall z0 (rA / 2)
  have hB_convex : Convex ℝ B := convex_closedBall z0 (rA / 2)
  have hB_sub_ball : B ⊆ ball z0 rA := by
    intro z hz
    have h : dist z z0 ≤ rA / 2 := mem_closedBall.mp hz
    simp only [mem_ball]
    linarith
  have hB_sub_Utarget : B ⊆ U_target := fun z hz => (hball (hB_sub_ball hz)).1
  have h_hmap_B_W : h_map '' B ⊆ W := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (hball (hB_sub_ball hz)).2.1
  have h_hmap_B_V : ∀ z ∈ B, h_map z ∈ V := by
    intro z hz
    exact (hball (hB_sub_ball hz)).2.2

  -- g0(z) := last coordinate of h_map(z)
  let g0 : E m → ℝ := fun z => (h_map z) (Fin.last m)

  -- g0 is C¹ on B
  have h_hmap_c1 : ContDiffOn ℝ 1 h_map B := by
    have h1 : ContDiffOn ℝ 1 φ.symm φ.target := hsymm_diff
    have h2 : ContDiff ℝ ⊤ (fun z : E m => unsplit z s) := by
      have h3 : (fun z : E m => unsplit z s) = fun z => inclEm z + scaleE s := by
        funext z; exact unsplit_eq s z
      rw [h3]; fun_prop
    have h4 : ContDiffOn ℝ 1 (fun z : E m => unsplit z s) B := by
      have h41 : ContDiff ℝ 1 (fun z : E m => unsplit z s) := h2.of_le (by norm_num)
      exact h41.contDiffOn
    exact h1.comp h4 (fun z hz => hB_sub_Utarget hz)
  let lastCoord : E (m + 1) →L[ℝ] ℝ :=
    { toFun := fun y : E (m + 1) => y (Fin.last m)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have h_lastCoord_c1 : ContDiff ℝ 1 (lastCoord : E (m + 1) → ℝ) := by
    have h : ContDiff ℝ ⊤ (lastCoord : E (m + 1) → ℝ) := lastCoord.contDiff
    exact h.of_le (by norm_num)
  have h_g0_c1 : ContDiffOn ℝ 1 g0 B := by
    have h5 : g0 = fun z => lastCoord (h_map z) := by funext z; rfl
    rw [h5]
    exact h_lastCoord_c1.contDiffOn.comp h_hmap_c1 (fun _ _ => Set.mem_univ _)

  -- g0 is Lipschitz on B
  rcases h_g0_c1.exists_lipschitzOnWith (by norm_num) hB_convex hB_compact with ⟨L0, hL0⟩

  -- Extend g0 to globally Lipschitz g (McShane)
  rcases hL0.extend_real with ⟨g, hg_lip, hg_eq_on_B⟩

  -- A := closedBall z0 (rA / 4) (smaller compact set for the statement)
  let A : Set (E m) := closedBall z0 (rA / 4)
  have hA_compact : IsCompact A := isCompact_closedBall z0 (rA / 4)
  have hz0_A : z0 ∈ A := by
    simp [A, mem_closedBall, hrA_pos] <;> linarith
  have hA_sub_B : A ⊆ B := by
    intro z hz
    have h : dist z z0 ≤ rA / 4 := mem_closedBall.mp hz
    simp only [B, mem_closedBall]
    linarith
  have hA_sub_Utarget : A ⊆ U_target := Set.Subset.trans hA_sub_B hB_sub_Utarget

  -- graphMap g z = h_map z for z ∈ B
  have h_proj_hmap : ∀ z ∈ B, proj (h_map z) = z := by
    intro z hz
    have h_ztarget : unsplit z s ∈ φ.target := hB_sub_Utarget hz
    have h1 : φ (h_map z) = unsplit z s := φ.right_inv h_ztarget
    have h2 : φ (h_map z) = unsplit (proj (h_map z)) (u (h_map z)) := hφ_unsplit (h_map z)
    rw [h1] at h2
    have h3 : proj (unsplit z s) = proj (unsplit (proj (h_map z)) (u (h_map z))) := by rw [h2]
    have h4 : proj (unsplit z s) = z := graphMap_proj (fun _ => s) z
    have h5 : proj (unsplit (proj (h_map z)) (u (h_map z))) = proj (h_map z) := graphMap_proj (fun _ => u (h_map z)) (proj (h_map z))
    rw [h4, h5] at h3
    exact h3.symm
  have h_u_hmap : ∀ z ∈ B, u (h_map z) = s := by
    intro z hz
    have h_ztarget : unsplit z s ∈ φ.target := hB_sub_Utarget hz
    have h1 : φ (h_map z) = unsplit z s := φ.right_inv h_ztarget
    have h2 : φ (h_map z) = unsplit (proj (h_map z)) (u (h_map z)) := hφ_unsplit (h_map z)
    rw [h1] at h2
    have h4 : (unsplit z s) (Fin.last m) = (unsplit (proj (h_map z)) (u (h_map z))) (Fin.last m) := by
      rw [h2]
    have h5 : (unsplit z s) (Fin.last m) = s := graphMap_apply_last (fun _ => s) z
    have h6 : (unsplit (proj (h_map z)) (u (h_map z))) (Fin.last m) = u (h_map z) := graphMap_apply_last (fun _ => u (h_map z)) (proj (h_map z))
    rw [h5, h6] at h4
    exact h4.symm
  have h_graph_eq : ∀ z ∈ B, graphMap g z = h_map z := by
    intro z hz
    have h1 : g z = g0 z := (hg_eq_on_B hz).symm
    have h2 : proj (h_map z) = z := h_proj_hmap z hz
    ext i
    by_cases hlt : i.val < m
    · let j : Fin m := ⟨i.val, hlt⟩
      have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
      rw [hi]
      have h_g1 : (graphMap g z) (Fin.castSucc j) = z j := graphMap_apply_castSucc g z j
      have h_h1 : (proj (h_map z)) j = (h_map z) (Fin.castSucc j) := proj_apply (h_map z) j
      have h_z1 : z j = (proj (h_map z)) j := by rw [h2]
      rw [h_g1, h_z1, h_h1]
    · have hlast : i = Fin.last m := by apply Fin.ext; simp [hlt] <;> omega
      rw [hlast]
      rw [graphMap_apply_last, h1]
      <;> rfl

  -- N := V ∩ {y | proj y ∈ interior A}
  let N : Set (E (m + 1)) := V ∩ {y | proj y ∈ interior A}
  have hN_open : IsOpen N :=
    hV_open.inter (continuous_proj.isOpen_preimage _ isOpen_interior)
  have hz0_interior_A : z0 ∈ interior A := by
    apply mem_interior.mpr
    exact ⟨ball z0 (rA / 4), ball_subset_closedBall, isOpen_ball, mem_ball_self (by linarith)⟩
  have hx0_N : x0 ∈ N := by
    constructor
    · exact hx0_V
    · exact hz0_interior_A

  -- Cover: N ∩ {u=s} ⊆ graphMap g '' A
  have h_cover : (N ∩ {y | u y = s}) ⊆ graphMap g '' A := by
    intro y hy
    have hy_V : y ∈ V := hy.1.1
    have hy_proj : proj y ∈ interior A := hy.1.2
    have hy_us : u y = s := hy.2
    have h_y_source : y ∈ φ.source := hV_source hy_V
    have hφ_y : φ y = unsplit (proj y) s := by
      rw [hφ_unsplit y, hy_us]
    have h_y_eq : y = h_map (proj y) := by
      dsimp only [h_map]
      have h : φ.symm (φ y) = y := φ.left_inv h_y_source
      rw [hφ_y] at h
      exact h.symm
    have hproj_A : proj y ∈ A := interior_subset hy_proj
    have hproj_B : proj y ∈ B := hA_sub_B hproj_A
    refine ⟨proj y, hproj_A, ?_⟩
    rw [h_graph_eq (proj y) hproj_B]
    exact h_y_eq.symm

  -- Graph subset: graphMap g '' A ⊆ {u=s}
  have h_graph_subset : graphMap g '' A ⊆ {y | u y = s} := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hz_B : z ∈ B := hA_sub_B hz
    have h1 : graphMap g z = h_map z := h_graph_eq z hz_B
    rw [h1]
    exact h_u_hmap z hz_B

  -- proj is 1-Lipschitz
  have h_proj_one_lip : LipschitzWith (1 : NNReal) (proj : E (m + 1) → E m) := by
    have h : ∀ (p q : E (m + 1)), ‖proj p - proj q‖ ≤ ‖p - q‖ := by
      intro p q
      have h1 : ‖proj p - proj q‖ ^ 2 ≤ ‖p - q‖ ^ 2 := by
        have h2 : ‖proj p - proj q‖ ^ 2 = ∑ i : Fin m, ((p - q) (Fin.castSucc i)) ^ 2 := by
          simp [EuclideanSpace.real_norm_sq_eq, GraphAreaFormula.proj_apply] <;> rfl
        rw [h2]
        have h3 : ∑ i : Fin m, ((p - q) (Fin.castSucc i)) ^ 2 ≤
            ∑ i : Fin (m + 1), ((p - q) i) ^ 2 := by
          rw [Fin.sum_univ_castSucc]
          <;> simp [sq_nonneg] <;> ring_nf <;> nlinarith
        have h4 : ‖p - q‖ ^ 2 = ∑ i : Fin (m + 1), ((p - q) i) ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
        rw [h4] <;> exact h3
      nlinarith [norm_nonneg (proj p - proj q), norm_nonneg (p - q)]
    exact LipschitzWith.of_dist_le_mul fun p q => by
      simpa [dist_eq_norm] using h p q


  -- Orientation via MVT on vertical segments
  have hA_sub_interior_B : A ⊆ interior B := by
    intro z hz
    have h1 : dist z z0 ≤ rA / 4 := mem_closedBall.mp hz
    have h2 : dist z z0 < rA / 2 := by linarith
    have h3 : z ∈ ball z0 (rA / 2) := mem_ball.mpr h2
    have h4 : ball z0 (rA / 2) ⊆ interior (closedBall z0 (rA / 2)) := by
      intro x hx
      exact Metric.ball_subset_interior_closedBall hx
    exact h4 h3
  have h_u_graph_B : ∀ z ∈ B, u (graphMap g z) = s := by
    intro z hz
    have h1 : graphMap g z = h_map z := h_graph_eq z hz
    rw [h1]
    exact h_u_hmap z hz
  have h_graph_W_B : ∀ z ∈ B, graphMap g z ∈ W := by
    intro z hz
    have h1 : graphMap g z = h_map z := h_graph_eq z hz
    rw [h1]
    exact h_hmap_B_W (Set.mem_image_of_mem _ hz)
  have hW_prop : ∀ y ∈ W, 0 < (fderiv ℝ u y) (eLast : E (m + 1)) := by
    intro y hy
    exact hy
  have h_orient : ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
      ball (graphMap g z) r ∩ {y | u y > s} =
      ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
    intro z hz
    exact orientation_helper u hu s g hg_lip W hW_open hW_prop B A
      hA_sub_interior_B h_u_graph_B h_graph_W_B z hz

  have hA_ball : IsClosedBall A :=
    ⟨⟨z0, rA / 4, by simp [A]⟩⟩

  have h_graph_interior_subset_N : graphMap g '' interior A ⊆ N := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hz_A : z ∈ A := interior_subset hz
    have hz_B : z ∈ B := hA_sub_B hz_A
    have h1 : graphMap g z = h_map z := h_graph_eq z hz_B
    rw [h1]
    have h2 : h_map z ∈ V := h_hmap_B_V z hz_B
    have h3 : proj (h_map z) = z := h_proj_hmap z hz_B
    have h4 : proj (h_map z) ∈ interior A := by rw [h3]; exact hz
    exact ⟨h2, h4⟩

  exact ⟨g, L0, A, N, hN_open, hx0_N, hA_compact, hA_ball, h_graph_interior_subset_N, hg_lip, h_cover, h_graph_subset, h_orient⟩

/-- **Local graph patch in arbitrary coordinate direction**.

Given `u` C¹, `x0` on `{u=s}` with `∂u/∂e_j > 0`, produce a Lipschitz graph
patch in the rotated coordinates (swapping `j` with `eLast`), along with the
linear isometry `P = coordSwapEquiv j`.

The rotated function is `v = u ∘ P`, and the patch covers `{v = s}` near `P x0`.
This matches the `SmoothBoundaryCover` API where `φ '' V` is the rotated set. -/
lemma local_graph_patch_dir
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (s : ℝ) (x0 : E (m + 1)) (hx0 : u x0 = s)
    (j : Fin (m + 1))
    (h_pos : 0 < (fderiv ℝ u x0) (EuclideanSpace.single j (1 : ℝ))) :
    ∃ (P : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
      (g : E m → ℝ) (L : NNReal) (A : Set (E m)) (N : Set (E (m + 1))),
      IsOpen N ∧ P x0 ∈ N ∧ IsCompact A ∧
      IsClosedBall A ∧
      graphMap g '' interior A ⊆ N ∧
      LipschitzWith L g ∧
      (N ∩ {y | u (P y) = s}) ⊆ graphMap g '' A ∧
      graphMap g '' A ⊆ {y | u (P y) = s} ∧
      ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
        ball (graphMap g z) r ∩ {y | u (P y) > s} =
        ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
  let P : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := coordSwapEquiv j
  let v : E (m + 1) → ℝ := u ∘ P
  have hP_diff : ContDiff ℝ 1 (P : E (m + 1) → E (m + 1)) := by exact LinearIsometryEquiv.contDiff P
  have hv : ContDiff ℝ 1 v := hu.comp hP_diff
  let y0 : E (m + 1) := P x0
  have hy0 : v y0 = s := by
    have hP2 : P (P x0) = x0 := coordSwapEquiv_involutive j x0
    have h : v y0 = u (P (P x0)) := by rfl
    rw [h, hP2, hx0]
  let Pclm : E (m + 1) →L[ℝ] E (m + 1) := P.toContinuousLinearMap
  have hPy0 : P y0 = x0 := by
    dsimp only [y0]
    exact coordSwapEquiv_involutive j x0
  have h_fderiv_v : fderiv ℝ v y0 =
      (fderiv ℝ u x0).comp Pclm := by
    have h1 : HasFDerivAt u (fderiv ℝ u x0) x0 :=
      (contDiff_one_iff_fderiv.mp hu).1.differentiableAt.hasFDerivAt
    have h1' : HasFDerivAt u (fderiv ℝ u x0) (P y0) := by
      rw [hPy0]; exact h1
    have h2 : HasFDerivAt P Pclm y0 :=
      Pclm.hasStrictFDerivAt.hasFDerivAt
    exact (h1'.comp y0 h2).fderiv
  have h_pos' : 0 < (fderiv ℝ v y0) (eLast : E (m + 1)) := by
    have h_eval : (fderiv ℝ v y0) (eLast : E (m + 1)) =
        (fderiv ℝ u x0) (P (eLast : E (m + 1))) := by
      rw [h_fderiv_v] <;> rfl
    rw [h_eval, coordSwapEquiv_eLast j]
    exact h_pos
  rcases local_graph_patch_last_pos v hv s y0 hy0 h_pos' with
    ⟨g, L, A, N, hN_open, hy0_N, hA_compact, hA_closedBall, h_interior_subset,
      hg_lip, h_cover, h_graph_subset, h_orient⟩
  have h_eq1 : {y : E (m + 1) | u (P y) = s} = {y | v y = s} := by ext y; rfl
  have h_eq2 : {y : E (m + 1) | u (P y) > s} = {y | v y > s} := by ext y; rfl
  have h_cover' : (N ∩ {y | u (P y) = s}) ⊆ graphMap g '' A := by
    rw [h_eq1]; exact h_cover
  have h_graph_subset' : graphMap g '' A ⊆ {y | u (P y) = s} := by
    rw [h_eq1]; exact h_graph_subset
  have h_orient' : ∀ z ∈ A, ∃ (r : ℝ), 0 < r ∧
      ball (graphMap g z) r ∩ {y | u (P y) > s} =
      ball (graphMap g z) r ∩ {p | p (Fin.last m) > g (proj p)} := by
    intro z hz
    rcases h_orient z hz with ⟨r, hr_pos, h_eq⟩
    refine ⟨r, hr_pos, ?_⟩
    rw [h_eq2] at *
    exact h_eq
  exact ⟨P, g, L, A, N, hN_open, hy0_N, hA_compact, hA_closedBall, h_interior_subset,
    hg_lip, h_cover', h_graph_subset', h_orient'⟩

-- ============================================================================
-- Regular open helper lemmas for level sets
-- ============================================================================

/-- Helper: nonzero continuous linear map to ℝ is surjective. -/
lemma nonzero_linear_map_surj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) : f.range = ⊤ := by
  have h1 : ∃ (v : E), f v ≠ 0 := by
    by_contra h
    push Not at h
    have h2 : f = 0 := by ext x; exact h x
    exact hf h2
  rcases h1 with ⟨v, hv⟩
  rw [LinearMap.range_eq_top]
  intro r
  use (r / f v) • v
  simp [hv] <;> ring

/-- Helper: any neighborhood of `s` in ℝ contains points `> s` and `< s`. -/
lemma nhds_real_both_sides (s : ℝ) {N : Set ℝ} (hN : N ∈ nhds s) :
    (∃ y ∈ N, y > s) ∧ (∃ y ∈ N, y < s) := by
  rcases Metric.mem_nhds_iff.mp hN with ⟨ε, hε_pos, hε_sub⟩
  have h1 : s + ε / 2 ∈ Metric.ball s ε := by
    have h11 : dist (s + ε / 2) s < ε := by
      rw [Real.dist_eq]
      have h13 : s + ε / 2 - s = ε / 2 := by ring
      rw [h13, abs_of_pos (by linarith)] <;> linarith
    exact h11
  have h2 : s - ε / 2 ∈ Metric.ball s ε := by
    have h21 : dist (s - ε / 2) s < ε := by
      rw [Real.dist_eq]
      have h23 : s - ε / 2 - s = -(ε / 2) := by ring
      rw [h23, abs_neg, abs_of_pos (by linarith)] <;> linarith
    exact h21
  exact ⟨⟨s + ε / 2, hε_sub h1, by linarith⟩, ⟨s - ε / 2, hε_sub h2, by linarith⟩⟩

/-- Helper: if `fderiv ℝ u p ≠ 0`, then `u` maps neighborhoods of `p` to
neighborhoods of `u p`, so any neighborhood contains points with `u > u p`
and points with `u < u p`. -/
lemma submersion_both_sides
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (p : E (m + 1)) (hgrad : fderiv ℝ u p ≠ 0)
    (N : Set (E (m + 1))) (hN : N ∈ nhds p) :
    (∃ x ∈ N, u x > u p) ∧ (∃ x ∈ N, u x < u p) := by
  have h_surj : (fderiv ℝ u p).range = ⊤ :=
    nonzero_linear_map_surj (fderiv ℝ u p) hgrad
  have h_strict : HasStrictFDerivAt u (fderiv ℝ u p) p :=
    hu.contDiffAt.hasStrictFDerivAt one_ne_zero
  have h_nhds : Filter.map u (nhds p) = nhds (u p) :=
    HasStrictFDerivAt.map_nhds_eq_of_surj h_strict h_surj
  have h_image : u '' N ∈ nhds (u p) := by
    rw [←h_nhds]; exact image_mem_map hN
  have h_both := nhds_real_both_sides (u p) h_image
  rcases h_both with ⟨h1_exists, h2_exists⟩
  rcases h1_exists with ⟨y1, hy1_in, hy1_gt⟩
  rcases h2_exists with ⟨y2, hy2_in, hy2_lt⟩
  have h1 : ∃ (x : E (m + 1)), x ∈ N ∧ u x = y1 := by
    simpa [Set.mem_image] using hy1_in
  have h2 : ∃ (x : E (m + 1)), x ∈ N ∧ u x = y2 := by
    simpa [Set.mem_image] using hy2_in
  rcases h1 with ⟨x1, hx1N, hux1⟩
  rcases h2 with ⟨x2, hx2N, hux2⟩
  have h_gt1 : u x1 > u p := by rw [hux1]; exact hy1_gt
  have h_lt2 : u x2 < u p := by rw [hux2]; exact hy2_lt
  exact ⟨⟨x1, hx1N, h_gt1⟩, ⟨x2, hx2N, h_lt2⟩⟩

/-- **Interior of closure of {u > s} equals {u > s}** under nonzero gradient
on the level set. Follows from a submersion argument: if a point in the
interior of the closure had `u = s`, the nonzero gradient would give points
with `u < s` in every neighborhood, contradicting being in the closure of
`{u > s}`. -/
lemma interior_closure_gt_eq_self
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (s : ℝ) (h_reg : ∀ x ∈ {x | u x = s}, fderiv ℝ u x ≠ 0) :
    interior (closure {x | u x > s}) = {x | u x > s} := by
  let U := {x | u x > s}
  have hU_open : IsOpen U := isOpen_lt continuous_const hu.continuous
  have h_ge_closed : IsClosed {x : E (m + 1) | u x ≥ s} :=
    isClosed_le continuous_const hu.continuous
  have hU_sub : U ⊆ {x | u x ≥ s} := by
    intro x hx
    have h_gt : u x > s := by simpa [U] using hx
    exact le_of_lt h_gt
  have h1 : closure U ⊆ {x | u x ≥ s} := closure_minimal hU_sub h_ge_closed
  have h2 : {x | u x = s} ⊆ closure U := by
    intro p hp
    have hgrad : fderiv ℝ u p ≠ 0 := h_reg p hp
    exact mem_closure_iff_nhds.mpr fun N hN =>
      let h_exists : ∃ x ∈ N, u x > u p := (submersion_both_sides u hu p hgrad N hN).1
      let x := Classical.choose h_exists
      have hx : x ∈ N ∧ u x > u p := Classical.choose_spec h_exists
      have h_us : u p = s := hp
      have h_gt : u x > s := by rw [h_us] at hx; exact hx.2
      have h_xU : x ∈ U := by simpa [U] using h_gt
      ⟨x, hx.1, h_xU⟩
  have h_closure : closure U = {x | u x ≥ s} := by
    apply Set.Subset.antisymm h1
    intro x hx
    have h_ge : u x ≥ s := by simpa [Set.mem_setOf_eq] using hx
    by_cases h_gt : u x > s
    · exact subset_closure (by simpa [U] using h_gt)
    · have h_eq : u x = s := by linarith
      exact h2 (by simpa using h_eq)
  have h31 : U ⊆ interior {x | u x ≥ s} :=
    hU_open.subset_interior_iff.mpr hU_sub
  have h32 : interior {x | u x ≥ s} ⊆ U := by
    intro x hx
    have h_ge : u x ≥ s := by
      have h4 : x ∈ {x | u x ≥ s} := interior_subset hx
      simpa [Set.mem_setOf_eq] using h4
    by_cases h_gt : u x > s
    · simpa [U] using h_gt
    · have h_eq : u x = s := by linarith
      have hgrad : fderiv ℝ u x ≠ 0 := h_reg x (by simpa using h_eq)
      have hN : interior {x | u x ≥ s} ∈ nhds x := isOpen_interior.mem_nhds hx
      have h_contra : ∃ z ∈ interior {x | u x ≥ s}, u z < u x :=
        (submersion_both_sides u hu x hgrad (interior {x | u x ≥ s}) hN).2
      let z := Classical.choose h_contra
      have hz : z ∈ interior {x | u x ≥ s} ∧ u z < u x := Classical.choose_spec h_contra
      have h5 : z ∈ {x | u x ≥ s} := interior_subset hz.1
      have h6 : u z ≥ s := by simpa [Set.mem_setOf_eq] using h5
      have h7 : u x = s := h_eq
      linarith
  have h_interior : interior {x | u x ≥ s} = U :=
    Set.Subset.antisymm h32 h31
  rw [h_closure, h_interior]

/-- **Frontier of interior(closure {u > s}) equals {u = s}.**

Under the regular value condition, `{u > s}` is regular open, so its
frontier is exactly the level set `{u = s}`. -/
lemma frontier_interior_closure_eq_level_set
    (u : E (m + 1) → ℝ) (hu : ContDiff ℝ 1 u)
    (s : ℝ) (h_reg : ∀ x ∈ {x | u x = s}, fderiv ℝ u x ≠ 0) :
    frontier (interior (closure {x | u x > s})) = {x | u x = s} := by
  let U := {x | u x > s}
  have h_main : interior (closure U) = U := interior_closure_gt_eq_self u hu s h_reg
  have hU_open : IsOpen U := isOpen_lt continuous_const hu.continuous
  have h_ge_closed : IsClosed {x : E (m + 1) | u x ≥ s} :=
    isClosed_le continuous_const hu.continuous
  have hU_sub_ge : U ⊆ {x | u x ≥ s} := by
    intro x hx
    have h_gt : u x > s := by simpa [U] using hx
    exact le_of_lt h_gt
  have h1 : closure U ⊆ {x | u x ≥ s} := closure_minimal hU_sub_ge h_ge_closed
  have h2 : {x | u x = s} ⊆ closure U := by
    intro p hp
    have hgrad : fderiv ℝ u p ≠ 0 := h_reg p hp
    exact mem_closure_iff_nhds.mpr fun N hN => by
      have h_exists : ∃ x ∈ N, u x > u p := (submersion_both_sides u hu p hgrad N hN).1
      rcases h_exists with ⟨x, hxN, hx_gt⟩
      have h_us : u p = s := hp
      have h_gt : u x > s := by rw [h_us] at hx_gt; exact hx_gt
      have h_xU : x ∈ U := by simpa [U] using h_gt
      exact ⟨x, hxN, h_xU⟩
  have h_closure : closure U = {x | u x ≥ s} := by
    apply Set.Subset.antisymm h1
    intro x hx
    have h_ge : u x ≥ s := by simpa [Set.mem_setOf_eq] using hx
    by_cases h_gt : u x > s
    · exact subset_closure (by simpa [U] using h_gt)
    · have h_eq : u x = s := by linarith
      exact h2 (by simpa using h_eq)
  have h_frontier_U : frontier U = {x | u x = s} := by
    have h4 : frontier U = closure U \ interior U := by exact Eq.symm (closure_sdiff_interior U)
    rw [h4, h_closure, hU_open.interior_eq]
    ext x
    simp only [U, Set.mem_setOf_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      have h5 : u x = s := by linarith
      exact h5
    · intro h
      exact ⟨by linarith, by linarith⟩
  rw [h_main]
  exact h_frontier_U

/-- The level set `{u = s}` is compact when `u` has compact support and
`∇u ≠ 0` on the level set. -/
lemma level_set_compact
    (u : E (m + 1) → ℝ) (hu : Continuous u)
    (h_support : HasCompactSupport u)
    (s : ℝ) (h_reg : ∀ x ∈ {x | u x = s}, fderiv ℝ u x ≠ 0) :
    IsCompact {x | u x = s} := by
  have hK : IsCompact (tsupport u) := by exact HasCompactSupport.isCompact h_support
  by_cases hs : s = 0
  · exfalso
    have h1 : ∀ x ∉ tsupport u, u x = 0 := by
      intro x hx; exact image_eq_zero_of_notMem_tsupport hx
    have h_univ_sub : (Set.univ : Set (E (m + 1))) ⊆ tsupport u := by
      intro x _
      by_contra hx
      have hux : u x = 0 := h1 x hx
      have h2 : x ∈ {x | u x = 0} := by simpa using hux
      rw [hs] at h_reg
      have h3 : fderiv ℝ u x ≠ 0 := h_reg x h2
      have h4 : u =ᶠ[nhds x] 0 := by exact notMem_tsupport_iff_eventuallyEq.mp hx
      have h5 : fderiv ℝ u x = fderiv ℝ (0 : E (m + 1) → ℝ) x := h4.fderiv_eq
      have h6 : fderiv ℝ (0 : E (m + 1) → ℝ) x = 0 := by simp
      have h7 : fderiv ℝ u x = 0 := by rw [h5, h6]
      exact h3 h7
    have h_univ_compact : IsCompact (Set.univ : Set (E (m + 1))) :=
      hK.of_isClosed_subset isClosed_univ h_univ_sub
    have h_not : ¬ IsCompact (Set.univ : Set (E (m + 1))) := by exact NoncompactSpace.noncompact_univ
    exact h_not h_univ_compact
  · have h1 : {x | u x = s} ⊆ Function.support u := by
      intro x hx
      have h2 : u x = s := hx
      have h3 : u x ≠ 0 := by
        intro h4; rw [h4] at h2; exact hs h2.symm
      exact h3
    have h2 : Function.support u ⊆ tsupport u := by
      intro x hx
      exact subset_closure hx
    have h3 : {x | u x = s} ⊆ tsupport u := Set.Subset.trans h1 h2
    have h4 : IsClosed {x | u x = s} := isClosed_eq hu continuous_const
    exact hK.of_isClosed_subset h4 h3

end Geometry.Isoperimetric
