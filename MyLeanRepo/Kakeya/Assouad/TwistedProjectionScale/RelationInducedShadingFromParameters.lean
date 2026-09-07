import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
WZ2 Section 7: twisted-image control for a relation-valued induced coarse
shading from explicit vertical-chart line-parameter bounds.
-/

namespace Kakeya.Assouad

private lemma coord_abs_le_norm' {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    |x k| ≤ ‖x‖ := by
  have h1 : (x k)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ i : Fin n, (x i)^2 :=
      EuclideanSpace.real_norm_sq_eq x
    rw [h2]
    apply Finset.single_le_sum
      (fun i _ => sq_nonneg (x i)) (Finset.mem_univ k)
  have h4 : |x k|^2 ≤ ‖x‖^2 := by
    have h5 : |x k|^2 = (x k)^2 := by rw [sq_abs]
    rw [h5]
    exact h1
  have h8 : |(|x k|)| ≤ |‖x‖| := sq_le_sq.mp h4
  simpa using h8

private lemma nonsingular_lipschitz_on_Icc
    {f : SlopeFunction} (h_ns : f.IsNonsingular)
    {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    |f a - f b| ≤ 2 * |a - b| := by
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖deriv f x‖ ≤ 2 := by
    intro x hx
    have h : |deriv f x| ≤ 2 := (h_ns x hx).2.1
    simpa using h
  have h_conv : Convex ℝ (Set.Icc (-1 : ℝ) 1) :=
    convex_Icc (-1 : ℝ) 1
  have h_diff_on :
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ f x := by
    intro x hx
    have h1 : 1 ≤ |deriv f x| := (h_ns x hx).1
    have h2 : deriv f x ≠ 0 := by
      have h3 : 0 < |deriv f x| := by linarith
      exact abs_ne_zero.mp (ne_of_gt h3)
    by_cases h4 : DifferentiableAt ℝ f x
    · exact h4
    · have h5 : deriv f x = 0 :=
        deriv_zero_of_not_differentiableAt h4
      contradiction
  have hft : ‖f a - f b‖ ≤ 2 * ‖a - b‖ :=
    h_conv.norm_image_sub_le_of_norm_deriv_le
      h_diff_on hderiv hb ha
  simpa using hft

private lemma twistedProjection_lipschitz_40
    {f : SlopeFunction} (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    {q x : Point3}
    (hq_z : q 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hx_z : x 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hx_y : |x 1| ≤ 17) :
    dist (twistedProjection f q) (twistedProjection f x) ≤
      40 * dist q x := by
  set d : ℝ := dist q x
  have h_d_nonneg : 0 ≤ d := dist_nonneg
  have h_coord0 : |q 0 - x 0| ≤ d :=
    coord_abs_le_norm' (q - x) 0
  have h_coord1 : |q 1 - x 1| ≤ d :=
    coord_abs_le_norm' (q - x) 1
  have h_coord2 : |q 2 - x 2| ≤ d :=
    coord_abs_le_norm' (q - x) 2
  have h_fq : |f (q 2)| ≤ 2 :=
    nonsingular_f_bound h_ns h0 hq_z
  have h_f_diff :
      |f (q 2) - f (x 2)| ≤ 2 * |q 2 - x 2| :=
    nonsingular_lipschitz_on_Icc h_ns hq_z hx_z
  have h_fdiff2 : |f (q 2) - f (x 2)| ≤ 2 * d := by
    calc
      |f (q 2) - f (x 2)| ≤ 2 * |q 2 - x 2| := h_f_diff
      _ ≤ 2 * d := by gcongr <;> linarith
  set v : Point2 :=
    twistedProjection f q - twistedProjection f x
  have h_v1 : v 1 = q 2 - x 2 := by
    simp [v, twistedProjection]
  set a : ℝ := q 0 - x 0
  set b : ℝ := f (q 2) * (q 1 - x 1)
  set c : ℝ := (f (q 2) - f (x 2)) * x 1
  have ha : |a| ≤ d := h_coord0
  have hb : |b| ≤ 2 * d := by
    rw [show b = f (q 2) * (q 1 - x 1) by rfl, abs_mul]
    gcongr <;> linarith
  have hc : |c| ≤ 34 * d := by
    rw [show c = (f (q 2) - f (x 2)) * x 1 by rfl, abs_mul]
    calc
      |f (q 2) - f (x 2)| * |x 1| ≤ (2 * d) * 17 := by
        gcongr <;> linarith
      _ = 34 * d := by ring
  have h_v0_eq : v 0 = a + b + c := by
    simp [v, twistedProjection, a, b, c]
    ring
  have h_abs_v0 : |v 0| ≤ 37 * d := by
    rw [h_v0_eq]
    have h_tri : |a + b + c| ≤ |a| + |b| + |c| := by
      calc
        |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
        _ ≤ |a| + |b| + |c| := by
          have h2 : |a + b| ≤ |a| + |b| := abs_add_le _ _
          linarith
    have h_sum : |a| + |b| + |c| ≤ 37 * d := by
      linarith
    linarith
  have h_abs_v1 : |v 1| ≤ d := by
    rw [h_v1]
    exact h_coord2
  have h8 : (v 0) ^ 2 ≤ (37 * d) ^ 2 := by
    have h_pos : 0 ≤ 37 * d := by positivity
    have h : |v 0| ≤ |37 * d| := by
      rw [abs_of_nonneg h_pos]
      exact h_abs_v0
    exact sq_le_sq.mpr h
  have h9 : (v 1) ^ 2 ≤ d ^ 2 := by
    have h : |v 1| ≤ |d| := by
      rw [abs_of_nonneg h_d_nonneg]
      exact h_abs_v1
    exact sq_le_sq.mpr h
  have h_norm_sq :
      ‖v‖ ^ 2 ≤ (37 * d) ^ 2 + d ^ 2 := by
    have h7 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq]
    rw [h7]
    linarith
  have h10 : (37 * d) ^ 2 + d ^ 2 ≤ (40 * d) ^ 2 := by
    nlinarith [h_d_nonneg]
  have h11 : ‖v‖ ≤ 40 * d := by
    have h12 : ‖v‖ ^ 2 ≤ (40 * d) ^ 2 := by linarith
    have h13 : 0 ≤ ‖v‖ := norm_nonneg v
    have h14 : 0 ≤ 40 * d := by positivity
    have h15 : |‖v‖| ≤ |40 * d| := sq_le_sq.mp h12
    rwa [abs_of_nonneg h13, abs_of_nonneg h14] at h15
  have h12 :
      dist (twistedProjection f q) (twistedProjection f x) = ‖v‖ := by
    simp [v, dist_eq_norm]
  rw [h12]
  exact h11

theorem twisted_projection_relation_induced_shading_from_parameters :
    TwistedProjectionRelationInducedShadingFromParametersStatement := by
  intro delta rho r hdelta_pos hdelta_one hr fine hvert hparams
    coarse Rel Y hY W hW f h_ns h0
  intro p hp
  rcases (Set.mem_image _ _ _).mp hp with ⟨q, hq, rfl⟩
  simp [Kakeya.Streamlined.Shading.union] at hq
  rcases hq with ⟨j, hj⟩
  let S : Set Point3 :=
    {x | ∃ i : Fin fine.card, Rel i j ∧ x ∈ Y.carrier i}
  have hq_carrier : q ∈ W.carrier j := hj
  have hWj :
      W.carrier j =
        (coarse.tube j).carrier ∩ horizontalSlab (-1) 1 ∩
          Metric.cthickening r S :=
    hW j
  rw [hWj] at hq_carrier
  have hq_z : q 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [horizontalSlab] using hq_carrier.1.2
  have hq_thick : q ∈ Metric.cthickening r S := hq_carrier.2
  have hS_nonempty : S.Nonempty := by
    by_contra h
    have h_empty : S = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    have h_top : Metric.infEDist q S = ⊤ := by
      rw [h_empty]
      exact Metric.infEDist_empty
    have h_le : Metric.infEDist q S ≤ ENNReal.ofReal r := by
      simpa [Metric.mem_cthickening_iff] using hq_thick
    rw [h_top] at h_le
    simp at h_le
  have h_main :
      ∀ ε : ℝ, 0 < ε →
        Metric.infEDist (twistedProjection f q) (twistedUnion Y f) ≤
          ENNReal.ofReal (40 * (r + ε)) := by
    intro ε hε
    have h1 : Metric.infEDist q S < ENNReal.ofReal (r + ε) := by
      have h2 : Metric.infEDist q S ≤ ENNReal.ofReal r := by
        simpa [Metric.mem_cthickening_iff] using hq_thick
      have h3 : ENNReal.ofReal r < ENNReal.ofReal (r + ε) := by
        have h4 : r < r + ε := by linarith
        exact
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mpr h4
      exact lt_of_le_of_lt h2 h3
    rcases Metric.infEDist_lt_iff.mp h1 with
      ⟨x, hxS, hx_edist⟩
    have hx_dist : dist q x < r + ε := by
      rwa [edist_lt_ofReal] at hx_edist
    rcases hxS with ⟨i, _hrel, hxi⟩
    have hx_union : x ∈ Y.union := by
      simpa [Kakeya.Streamlined.Shading.union] using ⟨i, hxi⟩
    have hx_z : x 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [horizontalSlab] using hY hx_union
    have hx_y : |x 1| ≤ 17 :=
      (tube_point_bounds_of_params hparams hvert hdelta_pos hdelta_one i
        (Y.subset_body i hxi) hx_z).2
    have h_lip :
        dist (twistedProjection f q) (twistedProjection f x) ≤
          40 * dist q x :=
      twistedProjection_lipschitz_40 h_ns h0 hq_z hx_z hx_y
    have h4 :
        dist (twistedProjection f q) (twistedProjection f x) ≤
          40 * (r + ε) := by
      calc
        dist (twistedProjection f q) (twistedProjection f x) ≤
            40 * dist q x := h_lip
        _ ≤ 40 * (r + ε) := by gcongr <;> linarith
    have h5 : twistedProjection f x ∈ twistedUnion Y f :=
      ⟨x, hx_union, rfl⟩
    have h6 :
        Metric.infEDist (twistedProjection f q) (twistedUnion Y f) ≤
          edist (twistedProjection f q) (twistedProjection f x) :=
      Metric.infEDist_le_edist_of_mem h5
    have h7 :
        edist (twistedProjection f q) (twistedProjection f x) ≤
          ENNReal.ofReal (40 * (r + ε)) := by
      rw [edist_le_ofReal (by linarith)]
      exact h4
    exact h6.trans h7
  have h_finite :
      Metric.infEDist (twistedProjection f q) (twistedUnion Y f) ≠ ⊤ := by
    have h9 := h_main 1 (by norm_num)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h9
  let b :=
    ENNReal.toReal
      (Metric.infEDist (twistedProjection f q) (twistedUnion Y f))
  have h_eq :
      Metric.infEDist (twistedProjection f q) (twistedUnion Y f) =
        ENNReal.ofReal b := by
    rw [ENNReal.ofReal_toReal h_finite]
  have h_forall : ∀ ε : ℝ, 0 < ε → b ≤ 40 * (r + ε) := by
    intro ε hε
    have h9 :
        ENNReal.ofReal b ≤ ENNReal.ofReal (40 * (r + ε)) := by
      have h10 := h_main ε hε
      rw [h_eq] at h10
      exact h10
    by_contra h11
    have h12 : 40 * (r + ε) < b := by linarith
    have h13 : 0 ≤ 40 * (r + ε) := by linarith
    have h14 :
        ENNReal.ofReal (40 * (r + ε)) < ENNReal.ofReal b :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h13).mpr h12
    exact (lt_irrefl _ (lt_of_le_of_lt h9 h14))
  have h_b_le : b ≤ 40 * r := by
    by_contra h
    have h' : 40 * r < b := by linarith
    set ε : ℝ := (b - 40 * r) / 80
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have h10 : b ≤ 40 * (r + ε) := h_forall ε hε_pos
    have h11 : 40 * (r + ε) = (40 * r + b) / 2 := by
      dsimp [ε]
      ring
    rw [h11] at h10
    linarith
  have h_final :
      Metric.infEDist (twistedProjection f q) (twistedUnion Y f) ≤
        ENNReal.ofReal (40 * r) := by
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_b_le
  simpa [Metric.mem_cthickening_iff] using h_final

end Kakeya.Assouad
