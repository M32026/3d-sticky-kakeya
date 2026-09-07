import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceStripBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

/-- **Distance to complement equals distance to frontier.**

For `x ∈ U` with `U` open, `infDist x Uᶜ = infDist x (frontier U)`. -/
lemma infDist_compl_eq_frontier {n : ℕ} {U : Set (E n)}
    (hU : IsOpen U) {x : E n} (hx : x ∈ U) :
    infDist x Uᶜ = infDist x (frontier U) := by
  by_cases hU_univ : U = Set.univ
  · have hUc_empty : Uᶜ = (∅ : Set (E n)) := by
      rw [hU_univ] <;> simp
    have hfr_empty : frontier U = (∅ : Set (E n)) := by
      rw [hU_univ] <;> simp
    rw [hUc_empty, hfr_empty] <;> simp
  · have h1 : frontier U ⊆ Uᶜ := by
      intro y hy
      have h3 : y ∉ interior U := hy.2
      have h4 : interior U = U := hU.interior_eq
      rw [h4] at h3
      exact h3
    have hfr_nonempty : (frontier U).Nonempty := by
      by_contra h
      have hfr_empty : frontier U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hU_empty_or_univ : U = ∅ ∨ U = Set.univ :=
        frontier_eq_empty_iff.mp hfr_empty
      rcases hU_empty_or_univ with (hU_empty | hU_univ')
      · exfalso
        rw [hU_empty] at hx
        simpa using hx
      · exact hU_univ hU_univ'
    have h_le1 : infDist x Uᶜ ≤ infDist x (frontier U) :=
      Metric.infDist_le_infDist_of_subset h1 hfr_nonempty
    have h_main : ∃ (y : E n), y ∈ frontier U ∧ infDist x Uᶜ = dist x y :=
      exists_mem_frontier_infDist_compl_eq_dist hx hU_univ
    rcases h_main with ⟨y, hy_frontier, h_eq⟩
    have h_le2 : infDist x (frontier U) ≤ dist x y :=
      Metric.infDist_le_dist_of_mem hy_frontier
    have h_le3 : infDist x (frontier U) ≤ infDist x Uᶜ := by
      calc
        infDist x (frontier U) ≤ dist x y := h_le2
        _ = infDist x Uᶜ := h_eq.symm
    exact le_antisymm h_le1 h_le3

/-- `proj` is 1-Lipschitz. -/
lemma proj_one_lip : LipschitzWith (1 : NNReal) (proj : E (m + 1) → E m) := by
  have h : ∀ (p q : E (m + 1)), ‖proj p - proj q‖ ≤ ‖p - q‖ := by
    intro p q
    have h1 : ‖proj p - proj q‖ ^ 2 ≤ ‖p - q‖ ^ 2 := by
      have h2 : ‖proj p - proj q‖ ^ 2 = ∑ i : Fin m, ((p - q) (Fin.castSucc i)) ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq, proj_apply] <;> rfl
      rw [h2]
      have h3 : ∑ i : Fin m, ((p - q) (Fin.castSucc i)) ^ 2 ≤
          ∑ i : Fin (m + 1), ((p - q) i) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        <;> simp [sq_nonneg] <;> ring_nf <;> nlinarith
      have h4 : ‖p - q‖ ^ 2 = ∑ i : Fin (m + 1), ((p - q) i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      rw [h4]
      exact h3
    nlinarith [norm_nonneg (proj p - proj q), norm_nonneg (p - q)]
  exact LipschitzWith.of_dist_le_mul fun p q => by
    simpa [dist_eq_norm] using h p q

/-- Helper: uniform orientation radius from local orientation on compact set. -/
lemma uniform_orientation_radius
    {K : Set (E (m + 1))} (hK : IsCompact K)
    {U above : Set (E (m + 1))} (hU : IsOpen U)
    (h : ∀ y ∈ K, ∃ (r : ℝ), 0 < r ∧ ball y r ∩ U ⊆ above) :
    ∃ (r : ℝ), 0 < r ∧ ∀ y ∈ K, ball y r ∩ U ⊆ above := by
  by_cases hK_empty : K = ∅
  · exact ⟨1, by norm_num, fun y hy => by rw [hK_empty] at hy; simpa using hy⟩
  · let c : (x : E (m + 1)) → (x ∈ K) → Set (E (m + 1)) := fun x hx =>
      ball x (Classical.choose (h x hx))
    have hc : ∀ (x : E (m + 1)) (hx : x ∈ K), c x hx ∈ nhds x := by
      intro x hx
      have h2 : 0 < Classical.choose (h x hx) := (Classical.choose_spec (h x hx)).1
      have h3 : x ∈ c x hx := by
        dsimp only [c]
        simpa [Metric.mem_ball] using h2
      exact IsOpen.mem_nhds isOpen_ball h3
    rcases lebesgue_number_lemma_of_emetric_nhds' hK hc with ⟨δ, hδ_pos, hδ⟩
    -- Pick a real r > 0 with ENNReal.ofReal r < δ
    have h_exists_r : ∃ (r : ℝ), 0 < r ∧ ENNReal.ofReal r < δ := by
      by_cases h_top : δ = ⊤
      · refine ⟨1, by norm_num, ?_⟩
        rw [h_top] <;> simp
      · have h_lt_top : δ ≠ ⊤ := h_top
        have h_pos2 : 0 < δ.toReal := ENNReal.toReal_pos (ne_of_gt hδ_pos) h_lt_top
        let r : ℝ := δ.toReal / 2
        have hr_pos : 0 < r := by positivity
        have h_lt1 : r < δ.toReal := by
          dsimp only [r] <;> linarith
        have h4 : ENNReal.ofReal r < ENNReal.ofReal δ.toReal :=
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr h_lt1
        have h5 : ENNReal.ofReal δ.toReal = δ := ENNReal.ofReal_toReal h_lt_top
        refine ⟨r, hr_pos, ?_⟩
        rw [h5] at h4
        exact h4
    rcases h_exists_r with ⟨r, hr_pos, hr_lt⟩
    have h_main : ∀ (y : E (m + 1)), y ∈ K → ball y r ∩ U ⊆ above := by
      intro y hy
      rcases hδ y hy with ⟨y0, h_eball⟩
      have h1 : ball y r ⊆ c y0 y0.property := by
        intro z hz
        have h3 : dist z y < r := by simpa [Metric.mem_ball] using hz
        have h3' : dist y z < r := by rwa [dist_comm] at h3
        have h4 : ENNReal.ofReal (dist y z) ≤ ENNReal.ofReal r :=
          ENNReal.ofReal_le_ofReal (le_of_lt h3')
        have h5 : edist y z < δ := by
          have h6 : edist y z = ENNReal.ofReal (dist y z) := by
            simp [edist_dist]
          rw [h6]
          exact h4.trans_lt hr_lt
        have h5' : edist z y < δ := by rwa [edist_comm] at h5
        have h_z_in : z ∈ eball y δ := by
          simpa [Metric.mem_eball] using h5'
        exact h_eball h_z_in
      have h4 : c y0 y0.property = ball (↑y0) (Classical.choose (h (↑y0) y0.property)) := by
        dsimp only [c] <;> rfl
      rw [h4] at h1
      have h5 : ball y r ∩ U ⊆ ball (↑y0) (Classical.choose (h (↑y0) y0.property)) ∩ U := by
        intro z hz
        exact ⟨h1 hz.1, hz.2⟩
      exact subset_trans h5 (Classical.choose_spec (h (↑y0) y0.property)).2
    exact ⟨r, hr_pos, h_main⟩

/-- **Inner strip cover by oriented graph strips + null neighborhood.**

Given a finite cover of `frontier U` by compact Lipschitz graph patches with
local orientation (U above each graph), and `s > 0`, there exists `t₀ > 0`
such that for all `0 < t < t₀`, the inner strip is covered by graph strips
over `thickening s (A i)` plus the t-neighborhood of `N`. -/
lemma inner_strip_graph_cover
    {U : Set (E (m + 1))} (hU : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {k : ℕ} (g : Fin k → (E m → ℝ))
    (A : Fin k → Set (E m))
    (hA_compact : ∀ i, IsCompact (A i))
    (hg_cont : ∀ i, Continuous (g i))
    (N : Set (E (m + 1)))
    (h_cover : frontier U ⊆ (⋃ i, graphMap (g i) '' (A i)) ∪ N)
    (h_orient : ∀ i (z : E m), z ∈ A i →
      ∃ (r : ℝ), 0 < r ∧
        ball (graphMap (g i) z) r ∩ U ⊆
          {p | p (Fin.last m) > g i (proj p)})
    (s : ℝ) (hs : 0 < s) :
    ∃ (t₀ : ℝ), 0 < t₀ ∧ ∀ (t : ℝ), 0 < t → t < t₀ →
      {x : E (m + 1) | x ∈ U ∧ 0 < infDist x Uᶜ ∧ infDist x Uᶜ < t} ⊆
      (⋃ i, distanceStrip (g i) (Metric.thickening s (A i)) t) ∪
        {x : E (m + 1) | infDist x N < t} := by
  -- Frontier is compact
  have h_frontier_closed : IsClosed (frontier U) := isClosed_frontier
  have h_frontier_bdd : Bornology.IsBounded (frontier U) :=
    hU_bdd.closure.subset frontier_subset_closure
  have h_frontier_compact : IsCompact (frontier U) :=
    Metric.isCompact_of_isClosed_isBounded h_frontier_closed h_frontier_bdd

  -- graphMap (g i) is continuous
  have h_graphMap_cont : ∀ i, Continuous (graphMap (g i)) := by
    intro i
    let f : E m → (Fin (m + 1) → ℝ) := fun y =>
      fun j : Fin (m + 1) => if h : j.val < m then y ⟨j.val, h⟩ else g i y
    have h1 : Continuous f := by
      dsimp only [f]
      apply continuous_pi
      intro j
      by_cases h : j.val < m
      · let idx : Fin m := ⟨j.val, h⟩
        have h_cont : Continuous (fun y : E m => y idx) :=
          (EuclideanSpace.proj idx : E m →L[ℝ] ℝ).continuous
        simpa [h, idx] using h_cont
      · simpa [h] using hg_cont i
    let e2l := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
    have h2 : Continuous e2l := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous
    have h4 : (graphMap (g i)) = e2l ∘ f := by
      funext y
      rfl
    rw [h4]
    exact h2.comp h1

  let K : Fin k → Set (E (m + 1)) := fun i => graphMap (g i) '' (A i)
  have hK_compact : ∀ i, IsCompact (K i) := by
    intro i
    exact (hA_compact i).image (h_graphMap_cont i)

  -- Uniform orientation radius for each patch
  have h_uniform : ∀ i, ∃ (r_i : ℝ), 0 < r_i ∧
      ∀ (y : E (m + 1)), y ∈ K i →
        ball y r_i ∩ U ⊆ {p | p (Fin.last m) > g i (proj p)} := by
    intro i
    let above := {p : E (m + 1) | p (Fin.last m) > g i (proj p)}
    have h1 : ∀ (y : E (m + 1)), y ∈ K i →
        ∃ (r : ℝ), 0 < r ∧ ball y r ∩ U ⊆ above := by
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact h_orient i z hz
    exact uniform_orientation_radius (hK_compact i) hU h1
  choose r_i hr_i_pos hr_i_uniform using h_uniform

  by_cases h_k : k = 0
  · -- k = 0: frontier U ⊆ N, inner strip covered by N-neighborhood
    refine ⟨s, hs, fun t ht_pos ht_lt => ?_⟩
    intro x hx
    have hxU : x ∈ U := hx.1
    have h_frontier_nonempty : (frontier U).Nonempty := by
      by_contra h
      have h' : frontier U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hU_empty_or_univ : U = ∅ ∨ U = Set.univ := frontier_eq_empty_iff.mp h'
      rcases hU_empty_or_univ with (hU_empty | hU_univ)
      · rw [hU_empty] at hxU; simpa using hxU
      · rw [hU_univ] at hU_bdd; exact NormedSpace.unbounded_univ ℝ (E (m + 1)) hU_bdd
    have h_eq_frontier : infDist x Uᶜ = infDist x (frontier U) :=
      infDist_compl_eq_frontier hU hxU
    have h_exists_y : ∃ (y : E (m + 1)), y ∈ frontier U ∧ infDist x (frontier U) = dist x y :=
      h_frontier_compact.exists_infDist_eq_dist h_frontier_nonempty x
    rcases h_exists_y with ⟨y, hy_frontier, h_dist_eq⟩
    have h_y_in_N : y ∈ N := by
      have h9 : y ∈ (⋃ i : Fin k, K i) ∪ N := h_cover hy_frontier
      rcases h9 with (h | h)
      · have h10 : IsEmpty (Fin k) := by
          subst h_k
          exact Fin.isEmpty'
        have h11 : (⋃ i : Fin k, K i) = (∅ : Set (E (m + 1))) := by
          exact Set.iUnion_eq_empty.mpr (fun i => IsEmpty.elim h10 i)
        rw [h11] at h
        simpa using h
      · exact h
    have h10 : infDist x N ≤ dist x y := Metric.infDist_le_dist_of_mem h_y_in_N
    have h11 : infDist x N < t := by
      calc infDist x N ≤ dist x y := h10
        _ = infDist x (frontier U) := h_dist_eq.symm
        _ = infDist x Uᶜ := h_eq_frontier.symm
        _ < t := hx.2.2
    exact Or.inr h11

  · -- k > 0
    have h_k_pos : 0 < k := by omega
    have h_fin_nonempty : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp h_k_pos
    let r_vals : Finset ℝ := Finset.image r_i Finset.univ
    have h_rv_nonempty : r_vals.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.univ_nonempty_iff.mpr h_fin_nonempty
    let min_r : ℝ := r_vals.min' h_rv_nonempty
    have h_min_pos : 0 < min_r := by
      have h_mem : min_r ∈ r_vals := Finset.min'_mem r_vals h_rv_nonempty
      rcases Finset.mem_image.mp h_mem with ⟨i, _, h_eq⟩
      have h : min_r = r_i i := h_eq.symm
      rw [h]
      exact hr_i_pos i
    let t₀ : ℝ := min s min_r
    have ht₀_pos : 0 < t₀ := by
      dsimp only [t₀]
      exact lt_min hs h_min_pos
    have ht₀_le_s : t₀ ≤ s := min_le_left _ _
    have ht₀_le_r : ∀ i, t₀ ≤ r_i i := by
      intro i
      have h6 : r_i i ∈ r_vals := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have h7 : min_r ≤ r_i i := Finset.min'_le r_vals (r_i i) h6
      dsimp only [t₀, min_r]
      exact le_trans (min_le_right _ _) h7
    refine ⟨t₀, ht₀_pos, fun t ht_pos ht_lt => ?_⟩
    intro x hx
    have hx_in_U : x ∈ U := hx.1
    have h_d_pos : 0 < infDist x Uᶜ := hx.2.1
    have h_d_lt_t : infDist x Uᶜ < t := hx.2.2

    -- Frontier nonempty
    have h_frontier_nonempty : (frontier U).Nonempty := by
      by_contra h
      have h' : frontier U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hU_empty_or_univ : U = ∅ ∨ U = Set.univ := frontier_eq_empty_iff.mp h'
      rcases hU_empty_or_univ with (hU_empty | hU_univ)
      · rw [hU_empty] at hx_in_U; simpa using hx_in_U
      · rw [hU_univ] at hU_bdd
        exact NormedSpace.unbounded_univ ℝ (E (m + 1)) hU_bdd

    -- Nearest point on frontier
    have h_eq_frontier : infDist x Uᶜ = infDist x (frontier U) :=
      infDist_compl_eq_frontier hU hx_in_U
    have h_exists_y : ∃ (y : E (m + 1)), y ∈ frontier U ∧ infDist x (frontier U) = dist x y :=
      h_frontier_compact.exists_infDist_eq_dist h_frontier_nonempty x
    rcases h_exists_y with ⟨y, hy_frontier, h_dist_eq⟩
    have h_dist_lt_t : dist x y < t := by
      rw [←h_dist_eq, ←h_eq_frontier] <;> exact h_d_lt_t

    have h_y_in_cover : y ∈ (⋃ i, K i) ∪ N := h_cover hy_frontier
    rcases h_y_in_cover with (h_y_in_graph | h_y_in_N)
    · -- y ∈ ⋃ K i
      rcases Set.mem_iUnion.mp h_y_in_graph with ⟨i, hy_in_Ki⟩
      rcases hy_in_Ki with ⟨z, hz_in_A, hy_eq⟩
      let y0 : E (m + 1) := graphMap (g i) z
      have h_y_eq : y = y0 := hy_eq.symm

      -- 1. x is above the graph
      have h1_above : x (Fin.last m) > g i (proj x) := by
        have h_ball : x ∈ ball y0 (r_i i) := by
          simpa [Metric.mem_ball] using
            calc dist x y0 = dist x y := by rw [h_y_eq]
              _ < t := h_dist_lt_t
              _ < t₀ := ht_lt
              _ ≤ r_i i := ht₀_le_r i
        have h : x ∈ ball y0 (r_i i) ∩ U := ⟨h_ball, hx_in_U⟩
        have h_y0_in_K : y0 ∈ K i := ⟨z, hz_in_A, rfl⟩
        exact hr_i_uniform i y0 h_y0_in_K h

      -- 2. y0 is on the graph
      have h_y0_on_graph : y0 ∈ GraphAreaFormula.graph (g i) := by
        have h31 : y0 (Fin.last m) = g i (proj y0) := by
          simp [y0, graphMap_apply_last, graphMap_proj] <;> rfl
        simpa [GraphAreaFormula.graph] using h31

      -- 3. infDist x (graph (g i)) < t
      have h2_lt : infDist x (GraphAreaFormula.graph (g i)) < t := by
        have h4 : infDist x (GraphAreaFormula.graph (g i)) ≤ dist x y0 :=
          Metric.infDist_le_dist_of_mem h_y0_on_graph
        have h5 : dist x y0 < t := by
          have h_eq2 : dist x y0 = dist x y := by rw [h_y_eq]
          rw [h_eq2]
          exact h_dist_lt_t
        exact h4.trans_lt h5

      -- 4. infDist x (graph (g i)) > 0
      have h_fst : Continuous (fun p : E (m + 1) => p (Fin.last m)) :=
        PiLp.continuous_apply 2 (fun x => ℝ) (Fin.last m)
      have h_snd : Continuous (fun p : E (m + 1) => g i (proj p)) :=
        (hg_cont i).comp proj_one_lip.continuous
      have h_graph_closed : IsClosed (GraphAreaFormula.graph (g i)) :=
        isClosed_eq h_fst h_snd
      have h_graph_nonempty : (GraphAreaFormula.graph (g i)).Nonempty :=
        ⟨y0, h_y0_on_graph⟩
      have h_x_notin_graph : x ∉ GraphAreaFormula.graph (g i) := by
        intro h10
        have h11 : x (Fin.last m) = g i (proj x) := by
          simpa [GraphAreaFormula.graph] using h10
        linarith [h1_above]
      have h3_pos : 0 < infDist x (GraphAreaFormula.graph (g i)) :=
        (h_graph_closed.notMem_iff_infDist_pos h_graph_nonempty).mp h_x_notin_graph

      -- 5. proj x ∈ thickening s (A i)
      have h4_proj : proj x ∈ Metric.thickening s (A i) := by
        have h_proj_dist : ∀ (a b : E (m + 1)), dist (proj a) (proj b) ≤ dist a b := by
          intro a b
          have h := proj_one_lip.dist_le_mul a b
          simpa using h
        have h_z : z = proj y0 := by
          simpa [y0, graphMap_proj] using rfl
        have h5 : dist (proj x) z ≤ dist x y0 := by
          rw [h_z]
          exact h_proj_dist x y0
        have h6 : dist (proj x) z < s := by
          calc dist (proj x) z ≤ dist x y0 := h5
            _ = dist x y := by rw [h_y_eq]
            _ < t := h_dist_lt_t
            _ < t₀ := ht_lt
            _ ≤ s := ht₀_le_s
        have h7 : infDist (proj x) (A i) < s := by
          have h8 : infDist (proj x) (A i) ≤ dist (proj x) z :=
            Metric.infDist_le_dist_of_mem hz_in_A
          exact h8.trans_lt h6
        have h9 : ∃ w ∈ A i, dist (proj x) w < s :=
          (Metric.infDist_lt_iff (show (A i).Nonempty from ⟨z, hz_in_A⟩)).mp h7
        simpa [Metric.mem_thickening_iff] using h9

      have h_x_in_strip : x ∈ distanceStrip (g i) (Metric.thickening s (A i)) t :=
        ⟨h4_proj, h3_pos, h2_lt, h1_above⟩
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, h_x_in_strip⟩)

    · -- y ∈ N
      have h5 : infDist x N ≤ dist x y := Metric.infDist_le_dist_of_mem h_y_in_N
      have h6 : infDist x N < t := h5.trans_lt h_dist_lt_t
      exact Or.inr h6

end Geometry.Isoperimetric
