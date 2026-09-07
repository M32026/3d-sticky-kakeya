import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LowerStripBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.InnerStripGraphCover
import MyLeanRepo.Kakeya.CV.Isoperimetric.MinkowskiContent.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.MinkowskiContent.GraphMeasure
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# Smooth Outer Minkowski Content

For a bounded open set `V` with C¹ compact boundary, the outer Minkowski
content is bounded by the Hausdorff measure of the boundary.

## Whiteprint

Node `smooth_outer_minkowski_content`, part of the outer Minkowski
content route.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory Pointwise
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

-- ============================================================================
-- Smooth boundary cover structure
-- ============================================================================

/-- **Finite smooth boundary cover** with strict local orientation. -/
structure SmoothBoundaryCover (V : Set (E (m + 1))) (ε : ENNReal) where
  k : ℕ
  φ : Fin k → (E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
  g : Fin k → (E m → ℝ)
  A : Fin k → Set (E m)
  L : Fin k → NNReal
  hA_compact : ∀ i, IsCompact (A i)
  hg_lip : ∀ i, LipschitzWith (L i) (g i)
  h_cover : frontier V ⊆ ⋃ i, (φ i).symm '' (graphMap (g i) '' (A i))
  h_orient : ∀ i (z : E m), z ∈ A i →
    ∃ (r : ℝ), 0 < r ∧
      ball (graphMap (g i) z) r ∩ ((φ i) '' V) =
      ball (graphMap (g i) z) r ∩ {p | p (Fin.last m) > g i (proj p)}
  h_patch_subset_frontier : ∀ i, (φ i).symm '' (graphMap (g i) '' (A i)) ⊆ frontier V
  h_sum : ∑ i : Fin k, μHE[m] ((φ i).symm '' (graphMap (g i) '' (A i))) ≤
    μHE[m] (frontier V) + ε

-- ============================================================================
-- Local continuity of graphMap
-- ============================================================================

lemma smooth_graphMap_continuous {g : E m → ℝ} (hg : Continuous g) :
    Continuous (graphMap g) := by
  let f : E m → (Fin (m + 1) → ℝ) := fun y =>
    fun j : Fin (m + 1) => if h : j.val < m then y ⟨j.val, h⟩ else g y
  have h1 : Continuous f := by
    dsimp only [f]
    apply continuous_pi
    intro j
    by_cases h : j.val < m
    · let idx : Fin m := ⟨j.val, h⟩
      have h_cont : Continuous (fun y : E m => y idx) :=
        (EuclideanSpace.proj idx : E m →L[ℝ] ℝ).continuous
      simpa [h, idx] using h_cont
    · simpa [h] using hg
  let e2l := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
  have h2 : Continuous e2l := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous
  have h4 : (graphMap g) = e2l ∘ f := by
    funext y
    rfl
  rw [h4]
  exact h2.comp h1

-- ============================================================================
-- Outer analog: infDist to set equals infDist to frontier for x ∉ V
-- ============================================================================

/-- For `x ∉ V` with `V` open and bounded,
`infDist x V = infDist x (frontier V)`. -/
lemma infDist_set_eq_frontier_of_not_mem
    {n : ℕ} {V : Set (E n)} (hV : IsOpen V) {x : E n} (hx : x ∉ V)
    (hBdd : Bornology.IsBounded V) :
    infDist x V = infDist x (frontier V) := by
  have h1 : infDist x V = infDist x (closure V) := by
    rw [Metric.infDist_closure]
  rw [h1]
  have h_closure_closed : IsClosed (closure V) := isClosed_closure
  have h_closure_bdd : Bornology.IsBounded (closure V) := hBdd.closure
  have h_closure_compact : IsCompact (closure V) :=
    Metric.isCompact_of_isClosed_isBounded h_closure_closed h_closure_bdd
  by_cases hV_empty : V = ∅
  · rw [hV_empty]
    simp [frontier_empty]
  have hV_nonempty : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hV_empty
  have h_closure_nonempty : (closure V).Nonempty := hV_nonempty.closure
  have h_exists : ∃ (y : E n), y ∈ closure V ∧ infDist x (closure V) = dist x y :=
    h_closure_compact.exists_infDist_eq_dist h_closure_nonempty x
  rcases h_exists with ⟨y, hy_closure, h_dist_eq⟩
  have hy_notin_V : y ∉ V := by
    by_contra hyV
    have h2 : ∃ (ε : ℝ), 0 < ε ∧ ball y ε ⊆ V :=
      Metric.mem_nhds_iff.mp (hV.mem_nhds hyV)
    rcases h2 with ⟨ε, hε_pos, hball⟩
    have hxy_ne : x ≠ y := by
      intro h_eq
      exact hx (h_eq ▸ hyV)
    set d : ℝ := dist x y with hd_def
    have hd_pos : 0 < d := by
      rw [dist_pos] <;> exact hxy_ne
    set t : ℝ := min (ε / (2 * d)) (1 / 2 : ℝ) with ht_def
    have ht_pos : 0 < t := by positivity
    have ht_lt_one : t < 1 := by
      have h : t ≤ (1 / 2 : ℝ) := min_le_right _ _
      linarith
    have h_td_lt_eps : t * d < ε := by
      have h : t ≤ ε / (2 * d) := min_le_left _ _
      have h2 : t * d ≤ (ε / (2 * d)) * d := by gcongr
      have h3 : (ε / (2 * d)) * d = ε / 2 := by
        field_simp [hd_pos.ne'] <;> ring
      rw [h3] at h2
      linarith
    set z : E n := y + t • (x - y) with hz_def
    have h_dist_yz : dist y z = t * d := by
      have h_eq1 : z - y = t • (x - y) := by
        simp [hz_def] <;> abel
      have h_norm : ‖y - z‖ = ‖z - y‖ := by rw [norm_sub_rev]
      rw [dist_eq_norm, h_norm, h_eq1, norm_smul]
      have h4 : ‖t‖ = t := by
        rw [Real.norm_eq_abs, abs_of_pos ht_pos]
      rw [h4]
      have h5 : ‖x - y‖ = d := by simpa [hd_def, dist_eq_norm] using rfl
      rw [h5] <;> ring
    have hz_in_V : z ∈ V := by
      have h : dist y z < ε := by
        rw [h_dist_yz] <;> exact h_td_lt_eps
      have h5 : z ∈ ball y ε := by
        simpa [Metric.mem_ball, dist_comm y z] using h
      exact hball h5
    have h_dist_xz : dist x z = (1 - t) * d := by
      have h_eq1 : x - z = (1 - t) • (x - y) := by
        have h : x - z = x - (y + t • (x - y)) := by rfl
        rw [h]
        have h2 : x - (y + t • (x - y)) = (x - y) - t • (x - y) := by abel
        rw [h2]
        have h3 : (x - y) - t • (x - y) = (1 - t) • (x - y) := by
          have h41 : (1 : ℝ) • (x - y) = (x - y) := by simp
          calc
            (x - y) - t • (x - y)
              = (1 : ℝ) • (x - y) - t • (x - y) := by rw [h41]
            _ = ((1 : ℝ) - t) • (x - y) := by rw [sub_smul]
            _ = (1 - t) • (x - y) := by norm_cast
        exact h3
      rw [dist_eq_norm, h_eq1, norm_smul]
      have h4 : ‖1 - t‖ = 1 - t := by
        rw [Real.norm_eq_abs, abs_of_pos] <;> linarith
      rw [h4]
      have h5 : ‖x - y‖ = d := by simpa [hd_def, dist_eq_norm] using rfl
      rw [h5] <;> ring
    have h9 : infDist x (closure V) ≤ dist x z :=
      Metric.infDist_le_dist_of_mem (subset_closure hz_in_V)
    rw [h_dist_eq] at h9
    rw [h_dist_xz] at h9
    have h10 : d ≤ (1 - t) * d := h9
    have h11 : (1 - t) * d < d := by
      have h12 : 0 < d := hd_pos
      have h13 : 0 < t := ht_pos
      nlinarith
    linarith
  have h_frontier_eq : frontier V = closure V \ interior V := by
    exact (closure_sdiff_interior V).symm
  have hy_frontier : y ∈ frontier V := by
    have h11 : y ∉ interior V := by
      intro h12
      exact hy_notin_V (interior_subset h12)
    rw [h_frontier_eq]
    exact ⟨hy_closure, h11⟩
  have h12 : infDist x (frontier V) ≤ dist x y :=
    Metric.infDist_le_dist_of_mem hy_frontier
  have h_sub : frontier V ⊆ closure V := frontier_subset_closure
  have hne : (frontier V).Nonempty := ⟨y, hy_frontier⟩
  have h13 : infDist x (closure V) ≤ infDist x (frontier V) :=
    Metric.infDist_le_infDist_of_subset h_sub hne
  have h14 : infDist x (frontier V) ≤ infDist x (closure V) := by
    have h15 : infDist x (closure V) = dist x y := h_dist_eq
    rw [h15]
    exact h12
  exact le_antisymm h13 h14

-- ============================================================================
-- Outer strip graph cover
-- ============================================================================

/-- **Outer strip is covered by lower strips of the graph atlas, up to a
null graph set**.

Given a finite cover of `frontier V` by compact Lipschitz graph patches with
strict local orientation (V is exactly the region above each graph), and
`s > 0`, there exists `t₀ > 0` such that for all `0 < t < t₀`, the outer strip
is covered by lower strips over `thickening s (A i)`, union the graph images
themselves (a null set for volume). -/
lemma smooth_outer_strip_graph_cover
    {V : Set (E (m + 1))} (hV : IsOpen V) (hBdd : Bornology.IsBounded V)
    {k : ℕ}
    (φ : Fin k → (E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)))
    (g : Fin k → (E m → ℝ))
    (A : Fin k → Set (E m))
    (hA_compact : ∀ i, IsCompact (A i))
    (hg_cont : ∀ i, Continuous (g i))
    (h_cover : frontier V ⊆ ⋃ i, (φ i).symm '' (graphMap (g i) '' (A i)))
    (h_orient : ∀ i (z : E m), z ∈ A i →
      ∃ (r : ℝ), 0 < r ∧
        ball (graphMap (g i) z) r ∩ ((φ i) '' V) =
        ball (graphMap (g i) z) r ∩ {p | p (Fin.last m) > g i (proj p)})
    (s : ℝ) (hs : 0 < s) :
    ∃ (t₀ : ℝ), 0 < t₀ ∧ ∀ (t : ℝ), 0 < t → t < t₀ →
      {x : E (m + 1) | x ∉ V ∧ 0 < infDist x V ∧ infDist x V < t} ⊆
        (⋃ i, (φ i).symm '' (lowerStrip (g i) (Metric.thickening s (A i)) t)) ∪
        (⋃ i, (φ i).symm '' GraphAreaFormula.graph (g i)) := by
  have h_frontier_closed : IsClosed (frontier V) := isClosed_frontier
  have h_frontier_bdd : Bornology.IsBounded (frontier V) :=
    hBdd.closure.subset frontier_subset_closure
  have h_frontier_compact : IsCompact (frontier V) :=
    Metric.isCompact_of_isClosed_isBounded h_frontier_closed h_frontier_bdd

  have h_graphMap_cont : ∀ i, Continuous (graphMap (g i)) :=
    fun i => smooth_graphMap_continuous (hg_cont i)

  let K' : Fin k → Set (E (m + 1)) := fun i => graphMap (g i) '' (A i)
  have hK'_compact : ∀ i, IsCompact (K' i) := by
    intro i; exact (hA_compact i).image (h_graphMap_cont i)

  have hV'_open : ∀ i, IsOpen ((φ i) '' V) := by
    intro i; exact (φ i).toHomeomorph.isOpenMap _ hV

  -- For each patch, get uniform radius for the "above ⊆ V" direction
  have h_uniform : ∀ i, ∃ (r_i : ℝ), 0 < r_i ∧
      ∀ (y : E (m + 1)), y ∈ K' i →
        ball y r_i ∩ {p : E (m + 1) | p (Fin.last m) > g i (proj p)} ⊆ (φ i) '' V := by
    intro i
    let above := {p : E (m + 1) | p (Fin.last m) > g i (proj p)}
    have h_above_open : IsOpen above := by
      have h1 : Continuous (fun p : E (m + 1) => p (Fin.last m)) := by fun_prop
      have h2 : Continuous (fun p : E (m + 1) => g i (proj p)) :=
        (hg_cont i).comp proj_one_lip.continuous
      exact isOpen_lt h2 h1
    have h1 : ∀ (y : E (m + 1)), y ∈ K' i →
        ∃ (r : ℝ), 0 < r ∧ ball y r ∩ above ⊆ (φ i) '' V := by
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases h_orient i z hz with ⟨r, hr_pos, heq⟩
      refine ⟨r, hr_pos, ?_⟩
      have h3 : ball (graphMap (g i) z) r ∩ above ⊆ (φ i) '' V := by
        rw [←heq]
        <;> exact inter_subset_right
      exact h3
    exact uniform_orientation_radius (hK'_compact i) h_above_open h1
  choose r_i hr_i_pos hr_i_uniform using h_uniform

  by_cases h_k : k = 0
  · have h_frontier_empty : frontier V = ∅ := by
      have h1 : (⋃ i : Fin k, (φ i).symm '' (K' i)) = ∅ := by
        subst h_k; simp
      have h2 : frontier V ⊆ ∅ := by rw [h1] at h_cover; exact h_cover
      exact Set.Subset.antisymm h2 (Set.empty_subset _)
    have hV_empty : V = ∅ := by
      have h : V = ∅ ∨ V = Set.univ := frontier_eq_empty_iff.mp h_frontier_empty
      rcases h with (h | h)
      · exact h
      · exfalso; rw [h] at hBdd; exact NormedSpace.unbounded_univ ℝ (E (m + 1)) hBdd
    refine ⟨1, by norm_num, fun t _ _ => ?_⟩
    rw [hV_empty]; simp

  · have h_k_pos : 0 < k := Nat.pos_of_ne_zero h_k
    let r_vals : Finset ℝ := Finset.image r_i Finset.univ
    have h_rv_nonempty : r_vals.Nonempty := by
      apply Finset.Nonempty.image
      exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp h_k_pos)
    let min_r : ℝ := r_vals.min' h_rv_nonempty
    have h_min_pos : 0 < min_r := by
      have h_mem : min_r ∈ r_vals := Finset.min'_mem r_vals h_rv_nonempty
      rcases Finset.mem_image.mp h_mem with ⟨i, _, h_eq⟩
      exact h_eq ▸ hr_i_pos i
    let t₀ : ℝ := min s min_r
    have ht₀_pos : 0 < t₀ := by
      dsimp only [t₀]; exact lt_min hs h_min_pos
    have ht₀_le_s : t₀ ≤ s := min_le_left _ _
    have ht₀_le_r : ∀ i, t₀ ≤ r_i i := by
      intro i
      have h6 : r_i i ∈ r_vals := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have h7 : min_r ≤ r_i i := Finset.min'_le r_vals (r_i i) h6
      dsimp only [t₀, min_r]; exact le_trans (min_le_right _ _) h7

    refine ⟨t₀, ht₀_pos, fun t ht_pos ht_lt => ?_⟩
    intro x hx
    have hxV : x ∉ V := hx.1
    have h_d_pos : 0 < infDist x V := hx.2.1
    have h_d_lt_t : infDist x V < t := hx.2.2

    have h_frontier_nonempty : (frontier V).Nonempty := by
      by_contra h
      have h' : frontier V = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hV_empty_or_univ : V = ∅ ∨ V = Set.univ := frontier_eq_empty_iff.mp h'
      rcases hV_empty_or_univ with (hV_empty | hV_univ)
      · rw [hV_empty] at h_d_pos
        have h10 : infDist x (∅ : Set (E (m + 1))) = 0 := by simp
        rw [h10] at h_d_pos <;> linarith
      · rw [hV_univ] at hBdd; exact NormedSpace.unbounded_univ ℝ (E (m + 1)) hBdd

    have h_eq_frontier : infDist x V = infDist x (frontier V) :=
      infDist_set_eq_frontier_of_not_mem hV hxV hBdd
    have h_exists_y : ∃ (y : E (m + 1)), y ∈ frontier V ∧ infDist x (frontier V) = dist x y :=
      h_frontier_compact.exists_infDist_eq_dist h_frontier_nonempty x
    rcases h_exists_y with ⟨y, hy_frontier, h_dist_eq⟩
    have h_dist_lt_t : dist x y < t := by
      rw [←h_dist_eq, ←h_eq_frontier]; exact h_d_lt_t

    have h_y_in_cover : y ∈ ⋃ i, (φ i).symm '' (K' i) := h_cover hy_frontier
    rcases Set.mem_iUnion.mp h_y_in_cover with ⟨i, hy_in_patch⟩
    rcases hy_in_patch with ⟨y', hy'_in_K', h_y_eq⟩
    have h_φy : φ i y = y' := by
      have h : φ i ((φ i).symm y') = y' := (φ i).apply_symm_apply y'
      simpa [h_y_eq] using h
    rcases hy'_in_K' with ⟨z, hz_in_A, hy'_eq⟩
    let y0 : E (m + 1) := graphMap (g i) z
    have h_y0_eq : y' = y0 := hy'_eq.symm

    let x' : E (m + 1) := φ i x
    have h_x'_notin_V' : x' ∉ (φ i) '' V := by
      intro h
      rcases h with ⟨v, hv, h_eq⟩
      have h2 : (φ i).symm x' = x := by simp [x']
      have h3 : (φ i).symm ((φ i) v) = v := (φ i).symm_apply_apply v
      have h4 : (φ i) v = x' := h_eq
      have h5 : (φ i).symm x' = (φ i).symm ((φ i) v) := by rw [h4]
      have h6 : x = v := by
        simpa [h2, h3] using h5
      exact hxV (h6 ▸ hv)
    have h_dist_x'y0 : dist x' y0 = dist x y := by
      have h1 : dist x' (φ i y) = dist x y := (φ i).dist_map x y
      have h2 : φ i y = y' := h_φy
      have h3 : y' = y0 := h_y0_eq
      have h4 : dist x' y0 = dist x' (φ i y) := by rw [h2, h3]
      rw [h4, h1]
    have h_dist_lt_t' : dist x' y0 < t := by
      rw [h_dist_x'y0]; exact h_dist_lt_t

    have h_ball : x' ∈ ball y0 (r_i i) := by
      simpa [Metric.mem_ball] using calc
        dist x' y0 < t := h_dist_lt_t'
        _ < t₀ := ht_lt
        _ ≤ r_i i := ht₀_le_r i
    have h_y0_in_K' : y0 ∈ K' i := ⟨z, hz_in_A, rfl⟩

    -- Case 1: x' is on the graph → put in exceptional set
    by_cases h_on_graph : x' ∈ GraphAreaFormula.graph (g i)
    · have h_x_in_exceptional : x ∈ (φ i).symm '' GraphAreaFormula.graph (g i) := by
        refine ⟨x', h_on_graph, ?_⟩
        simp [x']
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, h_x_in_exceptional⟩)

    -- Case 2: x' is not on the graph
    · have h_x'_notin_graph : x' ∉ GraphAreaFormula.graph (g i) := h_on_graph

      have h_not_above : ¬ (x' (Fin.last m) > g i (proj x')) := by
        intro h_above
        have h_in_above : x' ∈ {p : E (m + 1) | p (Fin.last m) > g i (proj p)} := h_above
        have h_in_ball_above : x' ∈ ball y0 (r_i i) ∩ {p : E (m + 1) | p (Fin.last m) > g i (proj p)} :=
          ⟨h_ball, h_in_above⟩
        have h_in_V' : x' ∈ (φ i) '' V := hr_i_uniform i y0 h_y0_in_K' h_in_ball_above
        exact h_x'_notin_V' h_in_V'

      have h_y0_on_graph : y0 ∈ GraphAreaFormula.graph (g i) := by
        have h31 : y0 (Fin.last m) = g i (proj y0) := by
          simp [y0, graphMap_apply_last, graphMap_proj]
        simpa [GraphAreaFormula.graph] using h31
      have h_infDist_lt : infDist x' (GraphAreaFormula.graph (g i)) < t := by
        have h4 : infDist x' (GraphAreaFormula.graph (g i)) ≤ dist x' y0 :=
          Metric.infDist_le_dist_of_mem h_y0_on_graph
        exact h4.trans_lt h_dist_lt_t'

      have h_graph_closed : IsClosed (GraphAreaFormula.graph (g i)) := by
        have h_fst : Continuous (fun p : E (m + 1) => p (Fin.last m)) := by fun_prop
        have h_snd : Continuous (fun p : E (m + 1) => g i (proj p)) :=
          (hg_cont i).comp proj_one_lip.continuous
        exact isClosed_eq h_fst h_snd
      have h_graph_nonempty : (GraphAreaFormula.graph (g i)).Nonempty := ⟨y0, h_y0_on_graph⟩
      have h_infDist_pos : 0 < infDist x' (GraphAreaFormula.graph (g i)) :=
        (h_graph_closed.notMem_iff_infDist_pos h_graph_nonempty).mp h_x'_notin_graph

      have h_below : x' (Fin.last m) < g i (proj x') := by
        have h_le : x' (Fin.last m) ≤ g i (proj x') := by
          by_contra h
          have h' : x' (Fin.last m) > g i (proj x') := by exact lt_of_not_ge h
          exact h_not_above h'
        have h_ne : x' (Fin.last m) ≠ g i (proj x') := by
          intro h_eq
          exact h_x'_notin_graph (by simpa [GraphAreaFormula.graph] using h_eq)
        exact lt_of_le_of_ne h_le h_ne

      have h_proj_y0 : proj y0 = z := graphMap_proj (g i) z
      have h_proj_dist : dist (proj x') z ≤ dist x' y0 := by
        have h := proj_one_lip.dist_le_mul x' y0
        simpa [h_proj_y0] using h
      have h_proj_lt_s : dist (proj x') z < s := by
        calc dist (proj x') z ≤ dist x' y0 := h_proj_dist
          _ < t := h_dist_lt_t'
          _ < t₀ := ht_lt
          _ ≤ s := ht₀_le_s
      have h_proj_in_thick : proj x' ∈ Metric.thickening s (A i) := by
        have h7 : z ∈ A i := hz_in_A
        have h8 : dist (proj x') z < s := h_proj_lt_s
        exact Metric.mem_thickening_iff.mpr ⟨z, h7, h8⟩

      have h_x'_in_strip : x' ∈ lowerStrip (g i) (Metric.thickening s (A i)) t :=
        ⟨h_proj_in_thick, h_infDist_pos, h_infDist_lt, h_below⟩

      have h_x_in : x ∈ (φ i).symm '' (lowerStrip (g i) (Metric.thickening s (A i)) t) := by
        refine ⟨x', h_x'_in_strip, ?_⟩
        simp [x']
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, h_x_in⟩)

-- ============================================================================
-- Graph image measure continuity
-- ============================================================================

/-- Alias for `graph_image_measure_continuous`. -/
lemma smooth_graph_measure_continuous
    {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    {A : Set (E m)} (hA : IsCompact A) (ε : ENNReal) (hε : 0 < ε) :
    ∃ (s : ℝ), 0 < s ∧
      μHE[m] (graphMap g '' Metric.thickening s A) ≤
      μHE[m] (graphMap g '' A) + ε :=
  graph_image_measure_continuous hg hA ε hε

/-- A Lipschitz graph patch has Lebesgue measure zero in the ambient space. -/
lemma volume_graph_patch_zero {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    {A : Set (E m)} (φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)) :
    volume (φ.symm '' (graphMap g '' A)) = 0 := by
  have h1 : volume (GraphAreaFormula.graph g) = 0 :=
    graph_volume_zero hg.continuous
  have h2 : graphMap g '' A ⊆ GraphAreaFormula.graph g := by
    intro z hz
    rcases hz with ⟨x, _, rfl⟩
    have h21 : (graphMap g x) (Fin.last m) = g (proj (graphMap g x)) := by
      simp [graphMap_apply_last, graphMap_proj]
    simpa [GraphAreaFormula.graph] using h21
  have h3 : volume (graphMap g '' A) = 0 := measure_mono_null h2 h1
  have hmp : MeasurePreserving φ.symm volume volume :=
    LinearIsometryEquiv.measurePreserving φ.symm
  have h_eq1 : φ.symm '' (graphMap g '' A) = φ ⁻¹' (graphMap g '' A) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, h_eq⟩
      have h_phi_y : φ y = z := by
        calc φ y = φ (φ.symm z) := by rw [h_eq]
             _ = z := φ.apply_symm_apply z
      exact h_phi_y ▸ hz
    · intro hy
      exact ⟨φ y, hy, φ.symm_apply_apply y⟩
  rw [h_eq1]
  have hmp2 : MeasurePreserving φ volume volume := φ.measurePreserving
  exact hmp2.preimage_null h3

-- ============================================================================
-- Main assembly theorem
-- ============================================================================

/-- **Outer Minkowski upper bound from a smooth boundary cover**.

Given a `SmoothBoundaryCover V ε'` for every `ε' > 0`, prove
`HasUpperMinkowskiContent (m+1) V (μHE[m] (frontier V))`. -/
theorem smooth_outer_minkowski_from_cover
    {V : Set (E (m + 1))} (hV : IsOpen V) (hBdd : Bornology.IsBounded V)
    (hcover : ∀ (ε' : ENNReal), 0 < ε' → ε' < ⊤ → SmoothBoundaryCover V ε')
    (hH_lt_top : μHE[m] (frontier V) < ⊤) :
    HasUpperMinkowskiContent (m + 1) V (μHE[m] (frontier V)) := by
  let H : ENNReal := μHE[m] (frontier V)
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨1, by norm_num, fun t ht_pos _ _ => ?_⟩
    have h_ne' : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht_pos).ne'
    have h_top : H + ε = ⊤ := by rw [hε_top] <;> simp
    have h_mul : (H + ε) * ENNReal.ofReal t = ⊤ := by
      rw [h_top]
      exact ENNReal.top_mul h_ne'
    have h_goal : volume V + (H + ε) * ENNReal.ofReal t = ⊤ := by
      rw [h_mul] <;> simp
    rw [h_goal]
    exact le_top
  have hε_lt_top : ε < ⊤ := lt_top_iff_ne_top.mpr hε_top

  let ε₁ : ENNReal := ε / 6
  let ε₂ : ENNReal := ε / 6
  have hε₁_pos : 0 < ε₁ := ENNReal.div_pos hε.ne' (by norm_num)
  have hε₂_pos : 0 < ε₂ := ENNReal.div_pos hε.ne' (by norm_num)
  have hε₁_lt_top : ε₁ < ⊤ := ENNReal.div_lt_top hε_lt_top.ne (by norm_num)

  let cover := hcover ε₁ hε₁_pos hε₁_lt_top
  let k := cover.k

  by_cases hk : cover.k = 0
  · have h_k_eq : k = 0 := by simpa [k] using hk
    have h_frontier_empty : frontier V = ∅ := by
      have h1 : (⋃ i : Fin cover.k, (cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i))) = ∅ := by
        haveI : IsEmpty (Fin cover.k) := by
          rw [hk] <;> exact Fin.isEmpty'
        simp
      have hcov : frontier V ⊆ (⋃ i : Fin cover.k, (cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i))) := cover.h_cover
      rw [h1] at hcov
      exact Set.Subset.antisymm hcov (Set.empty_subset _)
    have hV_empty : V = ∅ := by
      have h : V = ∅ ∨ V = Set.univ := frontier_eq_empty_iff.mp h_frontier_empty
      rcases h with (h | h)
      · exact h
      · exfalso; rw [h] at hBdd; exact NormedSpace.unbounded_univ ℝ (E (m + 1)) hBdd
    refine ⟨1, by norm_num, fun t _ _ _ => ?_⟩
    have h_empty : (∅ : Set (E (m + 1))) + t • unitBall (m + 1) = ∅ := by simp
    rw [hV_empty, h_empty]
    <;> simp
    <;> exact zero_le _
  · have h : k ≠ 0 := hk
    have h_k_pos : 0 < k := Nat.pos_of_ne_zero h

    by_cases hV_empty : V = ∅
    · refine ⟨1, by norm_num, fun t _ _ _ => ?_⟩
      rw [hV_empty] <;> simp <;> exact zero_le _
    have hV_nonempty : V.Nonempty := Set.nonempty_iff_ne_empty.mpr hV_empty

    have h_exists_ε₃ : ∃ (ε₃ : ℝ), 0 < ε₃ ∧
        ENNReal.ofReal (1 + ε₃) * (H + ε₁ + ε₂) ≤ H + ε / 2 := by
      set X : ENNReal := H + ε₁ + ε₂ with hX_def
      set Y : ENNReal := H + ε / 2 with hY_def
      have hX_lt_top : X ≠ ⊤ := by
        rw [hX_def]
        have h_six_ne_zero : (6 : ENNReal) ≠ 0 := by norm_num
        have hε₁_top : ε₁ ≠ ⊤ := (ENNReal.div_lt_top hε_lt_top.ne h_six_ne_zero).ne
        have hε₂_top : ε₂ ≠ ⊤ := (ENNReal.div_lt_top hε_lt_top.ne h_six_ne_zero).ne
        have h1 : H + ε₁ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hH_lt_top.ne, hε₁_top⟩
        exact ENNReal.add_ne_top.mpr ⟨h1, hε₂_top⟩
      have hY_lt_top : Y ≠ ⊤ := by
        rw [hY_def]
        have h_two_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
        have h_half_top : ε / 2 ≠ ⊤ := (ENNReal.div_lt_top hε_lt_top.ne h_two_ne_zero).ne
        exact ENNReal.add_ne_top.mpr ⟨hH_lt_top.ne, h_half_top⟩
      have h_sum_lt : X < Y := by
        dsimp only [X, Y, ε₁, ε₂]
        have h1 : ε / 6 + ε / 6 < ε / 2 := by
          have h4 : ε / 6 + ε / 6 = (2 : ENNReal) * (ε / 6) := by rw [two_mul]
          have h6 : (3 : ENNReal) * (ε / 6) = ε / 2 := by
            calc
              (3 : ENNReal) * (ε / 6)
                = ((3 : ENNReal) * ε) / 6 := by rw [←mul_div_assoc]
              _ = (ε * (3 : ENNReal)) / 6 := by rw [mul_comm]
              _ = ε * ((3 : ENNReal) / 6) := by rw [mul_div_assoc]
              _ = ε * ((1 : ENNReal) / 2) := by
                have h10 : (3 : ENNReal) / 6 = (1 : ENNReal) / 2 := by
                  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
                  <;> norm_num
                rw [h10]
              _ = ε / 2 := by
                have h_last : ε * ((1 : ENNReal) / 2) = ε / 2 := by
                  have h : ε * ((1 : ENNReal) / 2) = (ε * (1 : ENNReal)) / 2 := by rw [←mul_div_assoc]
                  rw [h] <;> simp
                exact h_last
          have h_pos6 : 0 < ε / 6 := ENNReal.div_pos hε.ne' (by norm_num)
          have h_ne_top : ε / 6 ≠ ⊤ := (ENNReal.div_lt_top hε_lt_top.ne (by norm_num)).ne
          have h_lt : (2 : ENNReal) * (ε / 6) < (3 : ENNReal) * (ε / 6) := by
            have h_pos : 0 < ε / 6 := ENNReal.div_pos hε.ne' (by norm_num)
            have h_ne_top : ε / 6 ≠ ⊤ := (ENNReal.div_lt_top hε_lt_top.ne (by norm_num)).ne
            exact ENNReal.mul_lt_mul_left h_pos.ne' h_ne_top (by norm_num)
          rw [h4]
          rw [h6] at h_lt
          exact h_lt
        have h_assoc : H + ε / 6 + ε / 6 = H + (ε / 6 + ε / 6) := by rw [add_assoc]
        rw [h_assoc]
        exact ENNReal.add_lt_add_left hH_lt_top.ne h1
      let x : ℝ := ENNReal.toReal X
      let y : ℝ := ENNReal.toReal Y
      have hx_lt_y : x < y := (ENNReal.toReal_lt_toReal hX_lt_top hY_lt_top).mpr h_sum_lt
      have hx_nonneg : 0 ≤ x := by positivity
      by_cases hx : x = 0
      · refine ⟨1, by norm_num, ?_⟩
        have hX_zero : X = 0 := by
          have h : X.toReal = 0 := hx
          have h' : X = 0 ∨ X = ⊤ := (ENNReal.toReal_eq_zero_iff X).mp h
          exact h'.resolve_right hX_lt_top
        rw [hX_zero]; simp
      · have hx_pos : 0 < x := by
          exact lt_of_le_of_ne hx_nonneg (Ne.symm hx)
        let ε₃ : ℝ := (y - x) / (2 * x)
        have h5 : 0 < y - x := by linarith
        have hε₃_pos : 0 < ε₃ := by
          dsimp only [ε₃]; exact div_pos h5 (by positivity)
        have h7 : (1 + ε₃) * x ≤ y := by
          dsimp only [ε₃]
          have h8 : (1 + (y - x) / (2 * x)) * x = x + (y - x) / 2 := by
            field_simp [hx_pos.ne'] <;> ring
          rw [h8]; linarith
        have hX_eq : X = ENNReal.ofReal x := by
          rw [← ENNReal.ofReal_toReal hX_lt_top] <;> rfl
        have h9 : ENNReal.ofReal (1 + ε₃) * X = ENNReal.ofReal ((1 + ε₃) * x) := by
          have h10 : 0 ≤ 1 + ε₃ := by linarith
          rw [hX_eq, ← ENNReal.ofReal_mul h10] <;> rfl
        have h11 : ENNReal.ofReal ((1 + ε₃) * x) ≤ ENNReal.ofReal y := ENNReal.ofReal_le_ofReal h7
        have h12 : ENNReal.ofReal y = Y := by
          rw [← ENNReal.ofReal_toReal hY_lt_top] <;> rfl
        have h_goal : ENNReal.ofReal (1 + ε₃) * X ≤ Y := by
          rw [h9]; exact h11.trans (le_of_eq h12)
        exact ⟨ε₃, hε₃_pos, h_goal⟩
    rcases h_exists_ε₃ with ⟨ε₃, hε₃_pos, hε₃_choice⟩

    have h_main_s : ∀ i : Fin k, ∃ (s : ℝ), 0 < s ∧
        μHE[m] (graphMap (cover.g i) '' Metric.thickening s (cover.A i)) ≤
        μHE[m] (graphMap (cover.g i) '' (cover.A i)) + ε₂ / k := by
      intro i
      have h_k_ne_zero : (k : ENNReal) ≠ 0 := by exact_mod_cast h_k_pos.ne'
      have h_pos2 : 0 < ε₂ / k := by
        have h : ε₂ / k = ε₂ * (k : ENNReal)⁻¹ := by rfl
        rw [h]; exact ENNReal.mul_pos hε₂_pos.ne' (by simp [h_k_pos.ne'])
      exact smooth_graph_measure_continuous (cover.hg_lip i) (cover.hA_compact i) (ε₂ / k) h_pos2
    choose s_i hs_i_pos hs_i_measure using h_main_s

    have h_main_s2 : ∃ (s : ℝ), 0 < s ∧ (∀ i : Fin k, s ≤ s_i i) := by
      let s_vals : Finset ℝ := Finset.image s_i Finset.univ
      have h_sv_nonempty : s_vals.Nonempty := by
        have h_univ_nonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
          ⟨⟨0, h_k_pos⟩, by simp⟩
        exact Finset.Nonempty.image h_univ_nonempty s_i
      let s : ℝ := s_vals.min' h_sv_nonempty
      have hs_pos : 0 < s := by
        have h_mem : s ∈ s_vals := Finset.min'_mem s_vals h_sv_nonempty
        rcases Finset.mem_image.mp h_mem with ⟨i, _, h_eq⟩
        rw [←h_eq]; exact hs_i_pos i
      have hs_le : ∀ i, s ≤ s_i i := by
        intro i
        have h6 : s_i i ∈ s_vals := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        exact Finset.min'_le s_vals (s_i i) h6
      exact ⟨s, hs_pos, hs_le⟩
    rcases h_main_s2 with ⟨s, hs_pos, hs_le⟩

    rcases smooth_outer_strip_graph_cover hV hBdd cover.φ cover.g cover.A
        cover.hA_compact (fun i => (cover.hg_lip i).continuous) cover.h_cover cover.h_orient s hs_pos
      with ⟨t₁, ht₁_pos, h_strip_cover⟩

    have h_strip_bounds : ∀ i : Fin k, ∃ (t₂ : ℝ), 0 < t₂ ∧ ∀ (t : ℝ), 0 < t → t < t₂ →
        volume ((cover.φ i).symm '' (lowerStrip (cover.g i)
            (Metric.thickening s (cover.A i)) t)) ≤
          ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t *
          μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i))) := by
      intro i
      have hA'_meas : MeasurableSet (Metric.thickening s (cover.A i)) :=
        isOpen_thickening.measurableSet
      have hA'_bdd : Bornology.IsBounded (Metric.thickening s (cover.A i)) :=
        (cover.hA_compact i).isBounded.thickening
      exact rotated_LipschitzGraph_lowerStripBound (cover.φ i) (cover.g i)
        (cover.hg_lip i) (Metric.thickening s (cover.A i)) hA'_meas hA'_bdd ε₃ hε₃_pos
    let t₂ : Fin k → ℝ := fun i => Classical.choose (h_strip_bounds i)
    have h_spec := fun i => Classical.choose_spec (h_strip_bounds i)
    have ht₂_pos : ∀ i, 0 < t₂ i := fun i => (h_spec i).1
    have ht₂_bound := fun i => (h_spec i).2

    let t₂_vals : Finset ℝ := Finset.image t₂ Finset.univ
    have h_t2v_nonempty : t₂_vals.Nonempty := by
      have h1 : (Finset.univ : Finset (Fin k)).Nonempty := by
        rw [Finset.univ_nonempty_iff]
        <;> exact Fin.pos_iff_nonempty.mp h_k_pos
      exact Finset.Nonempty.image h1 t₂
    let t₂_min : ℝ := t₂_vals.min' h_t2v_nonempty
    have ht₂_min_pos : 0 < t₂_min := by
      have h_mem : t₂_min ∈ t₂_vals := Finset.min'_mem t₂_vals h_t2v_nonempty
      rcases Finset.mem_image.mp h_mem with ⟨i, _, h_eq⟩
      rw [←h_eq]; exact ht₂_pos i

    have h_vol_frontier_zero : volume (frontier V) = 0 := by
      let S_i : Fin k → Set (E (m + 1)) := fun i =>
        (cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i))
      have h3 : ∀ i, volume (S_i i) = 0 := by
        intro i
        exact volume_graph_patch_zero (cover.hg_lip i) (cover.φ i)
      have h_union_eq : (⋃ i : Fin k, S_i i) = (⋃ i ∈ (Finset.univ : Finset (Fin k)), S_i i) := by
        ext x; simp
      have h4 : volume (⋃ i : Fin k, S_i i) ≤ ∑ i : Fin k, volume (S_i i) := by
        rw [h_union_eq]
        exact MeasureTheory.measure_biUnion_finset_le (Finset.univ) S_i
      have h5 : ∑ i : Fin k, volume (S_i i) = 0 := by
        rw [Finset.sum_congr rfl (fun i _ => h3 i)]
        simp
      have h6 : volume (⋃ i : Fin k, S_i i) = 0 := by
        rw [h5] at h4
        exact le_zero_iff.mp h4
      exact measure_mono_null cover.h_cover h6

    let graph_union : Set (E (m + 1)) :=
      ⋃ i : Fin k, (cover.φ i).symm '' GraphAreaFormula.graph (cover.g i)

    have h_graph_zero : volume graph_union = 0 := by
      have h1 : ∀ i : Fin k, volume ((cover.φ i).symm '' GraphAreaFormula.graph (cover.g i)) = 0 := by
        intro i
        have h2 : volume (GraphAreaFormula.graph (cover.g i)) = 0 :=
          graph_volume_zero (cover.hg_lip i).continuous
        have h_eq : (cover.φ i).symm '' GraphAreaFormula.graph (cover.g i) =
            (cover.φ i) ⁻¹' GraphAreaFormula.graph (cover.g i) := by
          ext y
          simp only [Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨z, hz, rfl⟩
            simpa using hz
          · intro hy
            refine ⟨(cover.φ i) y, hy, ?_⟩
            simp
        rw [h_eq]
        have hmp2 : MeasurePreserving (cover.φ i) volume volume := (cover.φ i).measurePreserving
        exact hmp2.preimage_null h2
      have h_union_eq : graph_union = (⋃ i ∈ (Finset.univ : Finset (Fin k)), (cover.φ i).symm '' GraphAreaFormula.graph (cover.g i)) := by
        ext x; simp [graph_union]
      rw [h_union_eq]
      have h3 : volume _ ≤ ∑ i : Fin k, volume ((cover.φ i).symm '' GraphAreaFormula.graph (cover.g i)) :=
        measure_biUnion_finset_le (Finset.univ : Finset (Fin k)) _
      rw [Finset.sum_congr rfl (fun i _ => h1 i)] at h3
      simpa using h3

    have h_sum_measure : ∑ i : Fin k,
        μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i))) ≤
        H + ε₁ + ε₂ := by
      have h1 : ∀ i : Fin k,
          μHE[m] (graphMap (cover.g i) '' Metric.thickening s (cover.A i)) ≤
          μHE[m] (graphMap (cover.g i) '' (cover.A i)) + ε₂ / k := by
        intro i
        have h_thick_mono : Metric.thickening s (cover.A i) ⊆ Metric.thickening (s_i i) (cover.A i) := by
          intro x hx
          rcases (Metric.mem_thickening_iff).mp hx with ⟨z, hz, hdist⟩
          have h10 : dist x z < s_i i := lt_of_lt_of_le hdist (hs_le i)
          exact (Metric.mem_thickening_iff).mpr ⟨z, hz, h10⟩
        have h71 : graphMap (cover.g i) '' Metric.thickening s (cover.A i) ⊆
            graphMap (cover.g i) '' Metric.thickening (s_i i) (cover.A i) := by
          intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          exact ⟨x, h_thick_mono hx, rfl⟩
        have h72 : μHE[m] (graphMap (cover.g i) '' Metric.thickening s (cover.A i)) ≤
            μHE[m] (graphMap (cover.g i) '' Metric.thickening (s_i i) (cover.A i)) :=
          measure_mono h71
        exact le_trans h72 (hs_i_measure i)
      have h2 : ∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i))) ≤
          ∑ i : Fin k, (μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i))) + ε₂ / k) :=
        Finset.sum_le_sum (fun i _ => by
          have h_iso : Isometry (cover.φ i).symm := (cover.φ i).symm.isometry
          have h8 : μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i))) =
              μHE[m] (graphMap (cover.g i) '' Metric.thickening s (cover.A i)) :=
            Isometry.euclideanHausdorffMeasure_image (d := m) h_iso (graphMap (cover.g i) '' Metric.thickening s (cover.A i))
          have h9 : μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i))) =
              μHE[m] (graphMap (cover.g i) '' (cover.A i)) :=
            Isometry.euclideanHausdorffMeasure_image (d := m) h_iso (graphMap (cover.g i) '' (cover.A i))
          rw [h8, h9]
          exact h1 i)
      have h3 : ∑ i : Fin k, (μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i))) + ε₂ / k) =
          (∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i)))) + ε₂ := by
        rw [Finset.sum_add_distrib]
        have h10 : ∑ i : Fin k, (ε₂ / k) = (k : ENNReal) * (ε₂ / k) := by
          rw [Finset.sum_const, Finset.card_fin]
          <;> ring
        rw [h10]
        have h11 : (k : ENNReal) * (ε₂ / k) = ε₂ := by
          rw [ENNReal.mul_div_cancel'] <;> simp [h_k_pos.ne'] <;> norm_cast
        rw [h11] <;> ring
      rw [h3] at h2
      have h4 : (∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i)))) ≤ H + ε₁ :=
        cover.h_sum
      calc
        (∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i))))
          ≤ (∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i)))) + ε₂ := h2
        _ ≤ (H + ε₁) + ε₂ := by
          have h5 : (∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' (cover.A i)))) + ε₂ ≤ (H + ε₁) + ε₂ :=
            add_le_add h4 (le_refl ε₂)
          exact h5
        _ = H + ε₁ + ε₂ := by ring

    have h_final : ENNReal.ofReal (1 + ε₃) * (H + ε₁ + ε₂) ≤ H + ε / 2 := hε₃_choice

    let t₀ : ℝ := min (min t₁ t₂_min) s
    have ht₀_pos : 0 < t₀ := by positivity

    refine ⟨t₀, ht₀_pos, fun t ht_pos ht_lt hmeas => ?_⟩

    have ht_lt_t1 : t < t₁ := by
      have h : t₀ ≤ t₁ := by
        dsimp only [t₀]; exact le_trans (min_le_left _ _) (min_le_left _ _)
      exact lt_of_lt_of_le ht_lt h
    have ht_lt_t2 : ∀ i, t < t₂ i := by
      intro i
      have h1 : t₀ ≤ t₂_min := by
        dsimp only [t₀]
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      have h2 : t < t₂_min := lt_of_lt_of_le ht_lt h1
      exact lt_of_lt_of_le h2 (Finset.min'_le t₂_vals (t₂ i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    have ht_le_s : t ≤ s := by
      have h : t₀ ≤ s := by
        dsimp only [t₀]; exact min_le_right _ _
      exact ht_lt.le.trans h

    -- General bound for any t' < t₀
    let posSet (t' : ℝ) : Set (E (m + 1)) :=
      {x | x ∉ V ∧ 0 < infDist x V ∧ infDist x V < t'}

    have h_pos_bound : ∀ (t' : ℝ), 0 < t' → t' < t₀ →
        volume (posSet t') ≤ ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t' * (H + ε₁ + ε₂) := by
      intro t' ht'_pos ht'_lt
      have ht'_lt_t1 : t' < t₁ := by
        have h : t₀ ≤ t₁ := by dsimp only [t₀]; exact le_trans (min_le_left _ _) (min_le_left _ _)
        exact lt_of_lt_of_le ht'_lt h
      have ht'_lt_t2 : ∀ i, t' < t₂ i := by
        intro i
        have h1 : t₀ ≤ t₂_min := by dsimp only [t₀]; exact le_trans (min_le_left _ _) (min_le_right _ _)
        have h2 : t' < t₂_min := lt_of_lt_of_le ht'_lt h1
        exact lt_of_lt_of_le h2 (Finset.min'_le t₂_vals (t₂ i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      let strip_i' : Fin k → Set (E (m + 1)) := fun i =>
        (cover.φ i).symm '' (lowerStrip (cover.g i) (Metric.thickening s (cover.A i)) t')
      let graph_union' : Set (E (m + 1)) :=
        ⋃ i : Fin k, (cover.φ i).symm '' GraphAreaFormula.graph (cover.g i)
      have h_graph_zero' : volume graph_union' = 0 := h_graph_zero
      let strip_union' : Set (E (m + 1)) := ⋃ i ∈ (Finset.univ : Finset (Fin k)), strip_i' i
      have h_cover : posSet t' ⊆ strip_union' ∪ graph_union' := by
        have h1 := h_strip_cover t' ht'_pos ht'_lt_t1
        have h_eq1 : (⋃ i : Fin k, strip_i' i) = strip_union' := by ext x; simp [strip_union']
        rw [h_eq1] at h1
        exact h1
      have h_vol_covered : volume (posSet t') ≤ volume strip_union' := by
        calc volume (posSet t')
            ≤ volume (strip_union' ∪ graph_union') := measure_mono h_cover
          _ ≤ volume strip_union' + volume graph_union' := measure_union_le _ _
          _ = volume strip_union' + 0 := by rw [h_graph_zero']
          _ = volume strip_union' := by simp
      calc volume (posSet t')
          ≤ volume strip_union' := h_vol_covered
        _ ≤ ∑ i : Fin k, volume (strip_i' i) := measure_biUnion_finset_le (Finset.univ : Finset (Fin k)) strip_i'
        _ ≤ ∑ i : Fin k, (ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t' *
              μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i)))) := by
          apply Finset.sum_le_sum
          intro i _
          exact ht₂_bound i t' ht'_pos (ht'_lt_t2 i)
        _ = ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t' *
              ∑ i : Fin k, μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i))) := by
            let c : ENNReal := ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t'
            let f : Fin k → ENNReal := fun i => μHE[m] ((cover.φ i).symm '' (graphMap (cover.g i) '' Metric.thickening s (cover.A i)))
            have h1 : ∑ i : Fin k, (c * f i) = c * ∑ i : Fin k, f i := by
              exact (Finset.mul_sum (Finset.univ : Finset (Fin k)) f c).symm
            exact h1
        _ ≤ ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t' * (H + ε₁ + ε₂) := by
            exact mul_le_mul' le_rfl h_sum_measure

    have h_full_bound : ∀ (t' : ℝ), 0 < t' → t' < t₀ →
        volume {x | infDist x V < t'} ≤ volume V + (H + ε) * ENNReal.ofReal t' := by
      intro t' ht'_pos ht'_lt
      have h_disj : Disjoint V (posSet t') := by
        rw [Set.disjoint_left]
        intro x hxV hxPos
        exact hxPos.1 hxV
      have h_sub1 : V ∪ posSet t' ⊆ {x | infDist x V < t'} := by
        intro x hx
        rcases hx with (hxV | hxPos)
        · have h_inf : infDist x V = 0 := Metric.infDist_zero_of_mem hxV
          have h_goal : infDist x V < t' := by
            rw [h_inf] <;> linarith [ht'_pos]
          exact h_goal
        · exact hxPos.2.2
      have h_sub2 : {x | infDist x V < t'} \ (V ∪ posSet t') ⊆ frontier V := by
        intro x hx
        have h_lt : infDist x V < t' := hx.1
        have h_notin_union : x ∉ V ∪ posSet t' := hx.2
        have h_notin_V : x ∉ V := by
          intro h
          exact h_notin_union (Or.inl h)
        have h_not_pos : x ∉ posSet t' := by
          intro h
          exact h_notin_union (Or.inr h)
        have h_no_pos : ¬(0 < infDist x V) := by
          by_contra h_pos
          exact h_not_pos ⟨h_notin_V, h_pos, h_lt⟩
        have h_nonneg : 0 ≤ infDist x V := Metric.infDist_nonneg
        have h_inf_zero : infDist x V = 0 := by linarith
        have h_closure : x ∈ closure V := by
          have h_iff : x ∈ closure V ↔ infDist x V = 0 :=
            Metric.mem_closure_iff_infDist_zero hV_nonempty
          exact h_iff.mpr h_inf_zero
        have h_not_interior : x ∉ interior V := by
          intro h_int
          exact h_notin_V (interior_subset h_int)
        have h_frontier_eq : frontier V = closure V \ interior V :=
          (closure_sdiff_interior V).symm
        rw [h_frontier_eq]
        exact ⟨h_closure, h_not_interior⟩
      have h_meas_V : MeasurableSet V := hV.measurableSet
      have h_cont : Continuous (fun x : E (m + 1) => infDist x V) := continuous_infDist_pt V
      have h_meas_Ioi : MeasurableSet {x | 0 < infDist x V} :=
        (h_cont.isOpen_preimage _ isOpen_Ioi).measurableSet
      have h_meas_Iio : MeasurableSet {x | infDist x V < t'} :=
        (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
      have h_meas_pos : MeasurableSet (posSet t') :=
        h_meas_V.compl.inter (h_meas_Ioi.inter h_meas_Iio)
      have h_meas_set : MeasurableSet {x | infDist x V < t'} := h_meas_Iio
      have h_diff_null : volume ({x | infDist x V < t'} \ (V ∪ posSet t')) = 0 :=
        measure_mono_null h_sub2 h_vol_frontier_zero
      have h_union2 : {x | infDist x V < t'} = (V ∪ posSet t') ∪ ({x | infDist x V < t'} \ (V ∪ posSet t')) := by
        ext y
        simp only [Set.mem_union, Set.mem_diff]
        constructor
        · intro hy
          by_cases h : y ∈ V ∪ posSet t'
          · exact Or.inl h
          · exact Or.inr ⟨hy, h⟩
        · rintro (h1 | h2)
          · exact h_sub1 h1
          · exact h2.1
      have h_disj2 : Disjoint (V ∪ posSet t') ({x | infDist x V < t'} \ (V ∪ posSet t')) := by
        rw [Set.disjoint_left]
        intro a ha hb
        exact hb.2 ha
      have h_meas_union : MeasurableSet (V ∪ posSet t') := h_meas_V.union h_meas_pos
      have h_meas_diff : MeasurableSet ({x | infDist x V < t'} \ (V ∪ posSet t')) :=
        h_meas_set.diff h_meas_union
      have h_eq_vol : volume {x | infDist x V < t'} = volume (V ∪ posSet t') := by
        rw [h_union2]
        rw [measure_union h_disj2 h_meas_diff]
        <;> rw [h_diff_null] <;> simp
      rw [h_eq_vol]
      rw [measure_union h_disj h_meas_pos]
      have h_bound : volume (posSet t') ≤ (H + ε) * ENNReal.ofReal t' := by
        calc volume (posSet t')
            ≤ ENNReal.ofReal (1 + ε₃) * ENNReal.ofReal t' * (H + ε₁ + ε₂) := h_pos_bound t' ht'_pos ht'_lt
          _ = (ENNReal.ofReal (1 + ε₃) * (H + ε₁ + ε₂)) * ENNReal.ofReal t' := by
            rw [mul_assoc, mul_comm (ENNReal.ofReal t') (H + ε₁ + ε₂), ←mul_assoc]
          _ ≤ (H + ε / 2) * ENNReal.ofReal t' := by
            exact mul_le_mul' h_final le_rfl
          _ ≤ (H + ε) * ENNReal.ofReal t' := by
            have h2 : ε / 2 ≤ ε := by
              have h3 : ε / 2 + ε / 2 = ε := by
                have h4 : ε / 2 + ε / 2 = (2 : ENNReal) * (ε / 2) := by ring
                rw [h4]
                have h5 : (2 : ENNReal) * (ε / 2) = ε := by
                  rw [ENNReal.mul_div_cancel'] <;> norm_num
                exact h5
              have h4 : ε / 2 ≤ ε / 2 + ε / 2 := le_add_of_nonneg_right (by simp)
              rw [h3] at h4
              exact h4
            have h5 : H + ε / 2 ≤ H + ε := by
              exact add_le_add_right h2 H
            exact mul_le_mul' h5 le_rfl
      exact add_le_add_right h_bound (volume V)

    -- Now prove the main bound using real toReal limit argument
    have h_main : volume (V + t • unitBall (m + 1)) ≤ volume V + (H + ε) * ENNReal.ofReal t := by
      have h_thickening_subset : ∀ (t' : ℝ), t < t' → V + t • unitBall (m + 1) ⊆ {x | infDist x V < t'} := by
        intro t' htt'
        intro x hx
        rcases hx with ⟨v, hv, y, hy, rfl⟩
        have h_ynorm_le : ‖y‖ ≤ t := by
          have h1 : y ∈ t • unitBall (m + 1) := hy
          rw [smul_unitClosedBall t] at h1
          have h2 : dist y 0 ≤ t := by
            simpa [abs_of_pos ht_pos] using mem_closedBall.mp h1
          simpa [dist_zero_right] using h2
        have h_dist : dist (v + y) v < t' := by
          simpa [dist_eq_norm] using h_ynorm_le.trans_lt htt'
        exact Metric.infDist_le_dist_of_mem hv |>.trans_lt h_dist
      have h_b_lt_top : volume V < ⊤ := hBdd.measure_lt_top
      have h_c_lt_top : H + ε < ⊤ := by
        exact ENNReal.add_lt_top.mpr ⟨hH_lt_top, hε_lt_top⟩
      have h_seq_bound : ∀ (δ : ℝ), 0 < δ → t + δ < t₀ →
          volume (V + t • unitBall (m + 1)) ≤ volume V + (H + ε) * ENNReal.ofReal (t + δ) := by
        intro δ hδ hlt
        have h_pos : 0 < t + δ := by linarith
        exact (measure_mono (h_thickening_subset (t + δ) (by linarith))).trans
          (h_full_bound (t + δ) h_pos hlt)
      have h_exists_delta : ∃ (δ : ℝ), 0 < δ ∧ t + δ < t₀ := by
        have h_pos : 0 < t₀ - t := by linarith
        refine ⟨(t₀ - t) / 2, by linarith, by linarith⟩
      rcases h_exists_delta with ⟨δ0, hδ0_pos, hδ0_lt⟩
      have h_a_lt_top : volume (V + t • unitBall (m + 1)) < ⊤ := by
        have h := h_seq_bound δ0 hδ0_pos hδ0_lt
        have h' : volume V + (H + ε) * ENNReal.ofReal (t + δ0) < ⊤ := by
          exact ENNReal.add_lt_top.mpr ⟨h_b_lt_top,
            ENNReal.mul_lt_top h_c_lt_top ENNReal.ofReal_lt_top⟩
        exact h.trans_lt h'
      have h_real_bound : ∀ (δ : ℝ), 0 < δ → t + δ < t₀ →
          (volume (V + t • unitBall (m + 1))).toReal ≤
          (volume V).toReal + (H + ε).toReal * (t + δ) := by
        intro δ hδ hlt
        have h := h_seq_bound δ hδ hlt
        have h_rhs_lt_top : volume V + (H + ε) * ENNReal.ofReal (t + δ) < ⊤ := by
          exact ENNReal.add_lt_top.mpr ⟨h_b_lt_top,
            ENNReal.mul_lt_top h_c_lt_top ENNReal.ofReal_lt_top⟩
        have h_rhs_real : (volume V + (H + ε) * ENNReal.ofReal (t + δ)).toReal =
            (volume V).toReal + (H + ε).toReal * (t + δ) := by
          have h_mul_ne : (H + ε) * ENNReal.ofReal (t + δ) ≠ ⊤ :=
            ENNReal.mul_ne_top h_c_lt_top.ne ENNReal.ofReal_ne_top
          rw [ENNReal.toReal_add h_b_lt_top.ne h_mul_ne, ENNReal.toReal_mul]
          rw [ENNReal.toReal_ofReal (by linarith)]
          <;> rfl
        have h_le : (volume (V + t • unitBall (m + 1))).toReal ≤ (volume V + (H + ε) * ENNReal.ofReal (t + δ)).toReal :=
          (ENNReal.toReal_le_toReal h_a_lt_top.ne h_rhs_lt_top.ne).mpr h
        rw [h_rhs_real] at h_le
        exact h_le
      have h_real_limit : (volume (V + t • unitBall (m + 1))).toReal ≤
          (volume V).toReal + (H + ε).toReal * t := by
        by_contra h
        set f : ℝ → ℝ := fun s => (volume V).toReal + (H + ε).toReal * s with hf_def
        set L : ℝ := (volume (V + t • unitBall (m + 1))).toReal with hL_def
        have h' : f t < L := by
          simpa [hf_def, hL_def] using by linarith
        have h_cont : ContinuousAt f t :=
          (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
        have h_eventually : ∀ᶠ s in nhds t, f s < L :=
          h_cont.tendsto (Iio_mem_nhds h')
        have h1 : ∃ (s : ℝ), t < s ∧ s < t₀ ∧ f s < L := by
          have h_preimage : f ⁻¹' Set.Iio L ∈ nhds t := h_cont.tendsto (Iio_mem_nhds h')
          have h2 : ∃ ε > 0, Metric.ball t ε ⊆ f ⁻¹' Set.Iio L := Metric.mem_nhds_iff.mp h_preimage
          rcases h2 with ⟨ε, hε_pos, hε⟩
          let δ := min (ε / 2) ((t₀ - t) / 2)
          have hδ_pos : 0 < δ := by positivity
          have h3 : t + δ ∈ Metric.ball t ε := by
            simp [Metric.mem_ball, dist_eq_norm, abs_of_pos hδ_pos]
            <;> linarith [show δ ≤ ε / 2 from min_le_left _ _]
          have h4 : t + δ ∈ f ⁻¹' Set.Iio L := hε h3
          have h5 : f (t + δ) < L := by
            simpa [Set.mem_preimage] using h4
          have h6 : t + δ < t₀ := by
            dsimp only [δ]
            linarith [show δ ≤ (t₀ - t) / 2 from min_le_right _ _]
          exact ⟨t + δ, by linarith, h6, h5⟩
        rcases h1 with ⟨s, hs_gt_t, hs_lt_t0, hfs_lt⟩
        let δ := s - t
        have hδ_pos : 0 < δ := by linarith
        have hδ_lt : t + δ < t₀ := by simpa [δ] using hs_lt_t0
        have h_bound2 := h_real_bound δ hδ_pos hδ_lt
        have h6 : L ≤ f s := by
          simpa [hf_def, hL_def, δ] using h_bound2
        have h7 : ¬(f s < L) := by linarith
        exact h7 hfs_lt
      set a : ENNReal := volume (V + t • unitBall (m + 1)) with ha_def
      set b : ENNReal := volume V with hb_def
      set c : ENNReal := (H + ε) * ENNReal.ofReal t with hc_def
      have hc_lt_top2 : c < ⊤ := ENNReal.mul_lt_top h_c_lt_top ENNReal.ofReal_lt_top
      have h_bc_lt_top : b + c < ⊤ := ENNReal.add_lt_top.mpr ⟨h_b_lt_top, hc_lt_top2⟩
      have h_goal : a ≤ b + c := by
        have h1 : a.toReal ≤ (b + c).toReal := by
          have h2 : (b + c).toReal = b.toReal + c.toReal := ENNReal.toReal_add h_b_lt_top.ne hc_lt_top2.ne
          have h3 : c.toReal = (H + ε).toReal * t := by
            rw [hc_def]
            have h_mul : ((H + ε) * ENNReal.ofReal t).toReal = (H + ε).toReal * (ENNReal.ofReal t).toReal :=
              ENNReal.toReal_mul
            rw [h_mul]
            have h_ofReal : (ENNReal.ofReal t).toReal = t := ENNReal.toReal_ofReal (by linarith)
            rw [h_ofReal] <;> rfl
          rw [h2, h3]
          exact h_real_limit
        exact (ENNReal.toReal_le_toReal h_a_lt_top.ne h_bc_lt_top.ne).mp h1
      exact h_goal

    exact h_main

/-- **Smooth outer Minkowski content**.

For a bounded open set `V` with C¹ compact boundary (equivalently,
admitting a `SmoothBoundaryCover` for every excess `ε`),

  `HasUpperMinkowskiContent (m+1) V (μHE[m] (frontier V))`. -/
theorem smooth_outer_minkowski_content
    {V : Set (E (m + 1))} (hV : IsOpen V) (hBdd : Bornology.IsBounded V)
    (hcover : ∀ (ε : ENNReal), 0 < ε → ε < ⊤ → SmoothBoundaryCover V ε)
    (hH_lt_top : μHE[m] (frontier V) < ⊤) :
    HasUpperMinkowskiContent (m + 1) V (μHE[m] (frontier V)) :=
  smooth_outer_minkowski_from_cover hV hBdd hcover hH_lt_top

end Geometry.Isoperimetric
