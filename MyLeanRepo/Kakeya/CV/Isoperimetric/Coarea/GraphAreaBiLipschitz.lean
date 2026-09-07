import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Smooth Graph Area — Bi-Lipschitz Comparison Lemma

Key lemma for the smooth graph area formula: if `g` is C¹ and its derivative
oscillates by at most `ε` on a convex set `A`, then the graph map of `g` is
`√(1+2ε)`-bi-Lipschitz equivalent to the graph map of the affine tangent
approximation at any point `h₀ ∈ A`.

## Main result

`graph_bilipschitz_comparison`: for all `x, y ∈ A`,
  `‖G(x) - G(y)‖ ≤ √(1+2ε) · ‖G₀(x) - G₀(y)‖`
and the symmetric reverse bound,
where `G` is the graph map of `g` and `G₀` is the graph map of the affine
tangent `h ↦ g(h₀) + Dg(h₀)(h - h₀)`.

This supports the partition-and-limit argument for the full smooth graph
area formula.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace GraphAreaFormula

variable {m : ℕ} [Nonempty (Fin m)]

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- More general norm identity: for two (possibly different) functions g₁, g₂,
‖graphMap g₁ x - graphMap g₂ y‖² = ‖x - y‖² + (g₁ x - g₂ y)². -/
lemma graphMap_norm_sq_diff (g₁ g₂ : E m → ℝ) (x y : E m) :
    ‖graphMap g₁ x - graphMap g₂ y‖ ^ 2 = ‖x - y‖ ^ 2 + (g₁ x - g₂ y) ^ 2 := by
  let u : E m := x - y
  let b : ℝ := g₁ x - g₂ y
  have h_coord : ∀ (i : Fin (m + 1)),
      (graphMap g₁ x - graphMap g₂ y) i =
        if h : i.val < m then u ⟨i.val, h⟩ else b := by
    intro i
    simp [graphMap, EuclideanSpace.equiv, u, b] <;> split_ifs <;> rfl
  have h1 : ‖graphMap g₁ x - graphMap g₂ y‖ ^ 2 =
      ∑ i : Fin (m + 1), ((graphMap g₁ x - graphMap g₂ y) i) ^ 2 := by
    have h_inner : inner ℝ (graphMap g₁ x - graphMap g₂ y) (graphMap g₁ x - graphMap g₂ y) =
        ∑ i : Fin (m + 1), ((graphMap g₁ x - graphMap g₂ y) i) ^ 2 := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      have h : inner ℝ ((graphMap g₁ x - graphMap g₂ y) i) ((graphMap g₁ x - graphMap g₂ y) i) =
          ((graphMap g₁ x - graphMap g₂ y) i) ^ 2 := by simp
      rw [h]
    have h_norm : inner ℝ (graphMap g₁ x - graphMap g₂ y) (graphMap g₁ x - graphMap g₂ y) =
        ‖graphMap g₁ x - graphMap g₂ y‖ ^ 2 := inner_self_eq_norm_sq_to_K _
    linarith
  rw [h1]
  have h2 : ∑ i : Fin (m + 1), ((graphMap g₁ x - graphMap g₂ y) i) ^ 2 =
      (∑ j : Fin m, (u j) ^ 2) + b ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    have h3 : ∀ (j : Fin m), (graphMap g₁ x - graphMap g₂ y) (Fin.castSucc j) = u j := by
      intro j
      rw [h_coord (Fin.castSucc j)] <;> simp
    have h4 : (graphMap g₁ x - graphMap g₂ y) (Fin.last m) = b := by
      rw [h_coord (Fin.last m)] <;> simp
    rw [h4]
    apply congr_arg (fun z => z + b ^ 2)
    apply Finset.sum_congr rfl
    intro j _
    have h5 := h3 j
    rw [h5]
  rw [h2]
  have h3 : ‖u‖ ^ 2 = ∑ j : Fin m, (u j) ^ 2 := by
    have h_inner : inner ℝ u u = ∑ j : Fin m, (u j) ^ 2 := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j _
      have h : inner ℝ (u j) (u j) = (u j) ^ 2 := by simp
      rw [h]
    have h_norm : inner ℝ u u = ‖u‖ ^ 2 := inner_self_eq_norm_sq_to_K u
    linarith
  rw [h3] <;> ring

/-- Algebraic lemma: if |b - a| ≤ ε*u_norm and 0 ≤ ε ≤ 1, then
    b² ≤ a² + 2ε(u_norm² + a²). -/
private lemma sq_osc_bound (a b u_norm ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h : |b - a| ≤ ε * u_norm) :
    b ^ 2 ≤ a ^ 2 + 2 * ε * (u_norm ^ 2 + a ^ 2) := by
  set d : ℝ := b - a with hd_def
  have hd_abs : |d| ≤ ε * u_norm := h
  have h_d2 : d ^ 2 ≤ ε ^ 2 * u_norm ^ 2 := by
    have h1 : d ^ 2 = |d| ^ 2 := by simp [sq_abs]
    rw [h1]
    have h2 : |d| ^ 2 ≤ (ε * u_norm) ^ 2 := by gcongr
    have h3 : (ε * u_norm) ^ 2 = ε ^ 2 * u_norm ^ 2 := by ring
    rw [h3] at h2
    exact h2
  have h_amgm : 2 * |a| * u_norm ≤ a ^ 2 + u_norm ^ 2 := by
    have h_pos : (|a| - u_norm) ^ 2 ≥ 0 := by positivity
    have h2 : 2 * |a| * u_norm ≤ |a| ^ 2 + u_norm ^ 2 := by nlinarith
    have h3 : |a| ^ 2 = a ^ 2 := by simp [sq_abs]
    rw [h3] at h2
    exact h2
  have h_ad : 2 * a * d ≤ ε * (a ^ 2 + u_norm ^ 2) := by
    calc
      2 * a * d ≤ |2 * a * d| := le_abs_self _
      _ = 2 * |a| * |d| := by simp [abs_mul] <;> ring
      _ ≤ 2 * |a| * (ε * u_norm) := by gcongr <;> exact hd_abs
      _ = ε * (2 * |a| * u_norm) := by ring
      _ ≤ ε * (a ^ 2 + u_norm ^ 2) := by gcongr <;> exact h_amgm
  have h_main : 2 * a * d + d ^ 2 ≤ 2 * ε * (u_norm ^ 2 + a ^ 2) := by
    calc
      2 * a * d + d ^ 2 ≤ ε * (a ^ 2 + u_norm ^ 2) + ε ^ 2 * u_norm ^ 2 := by
        linarith [h_ad, h_d2]
      _ ≤ ε * (a ^ 2 + u_norm ^ 2) + ε * u_norm ^ 2 := by
        have h11 : ε ^ 2 * u_norm ^ 2 ≤ ε * u_norm ^ 2 := by
          have h12 : ε ^ 2 ≤ ε := by nlinarith
          have h13 : 0 ≤ u_norm ^ 2 := by positivity
          nlinarith
        linarith
      _ ≤ 2 * ε * (u_norm ^ 2 + a ^ 2) := by
        have h14 : ε * a ^ 2 ≤ 2 * ε * a ^ 2 := by
          have h15 : 0 ≤ ε * a ^ 2 := by positivity
          linarith
        linarith
  have h_expand : b ^ 2 = a ^ 2 + 2 * a * d + d ^ 2 := by
    simp [hd_def] <;> ring
  rw [h_expand]
  linarith [h_main]

/-- If g is C¹ and ‖Dg(h) - Dg(h₀)‖ ≤ ε on a convex set A (0 ≤ ε ≤ 1),
then the graph map G is √(1+2ε)-bi-Lipschitz equivalent to the
affine graph map G₀(h) = (h, g(h₀) + Dg(h₀)(h - h₀)). -/
lemma graph_bilipschitz_comparison
    (g : E m → ℝ) (hg : ContDiff ℝ 1 g)
    (A : Set (E m)) (hA_conv : Convex ℝ A)
    (h₀ : E m) (ε : ℝ) (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1)
    (h_osc : ∀ h ∈ A, ‖fderiv ℝ g h - fderiv ℝ g h₀‖ ≤ ε) :
    ∀ (x y : E m), x ∈ A → y ∈ A →
      let G := graphMap g
      let a : E m →L[ℝ] ℝ := fderiv ℝ g h₀
      let G₀ := graphMap (fun z => g h₀ + a (z - h₀))
      ‖G x - G y‖ ≤ Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖ ∧
      ‖G₀ x - G₀ y‖ ≤ Real.sqrt (1 + 2 * ε) * ‖G x - G y‖ := by
  intro x y hx hy
  set a : E m →L[ℝ] ℝ := fderiv ℝ g h₀ with ha_def
  set u : E m := x - y with hu_def
  set b : ℝ := g x - g y with hb_def
  set a_u : ℝ := a u with hau_def
  set G := graphMap g with hG_def
  set G₀ := graphMap (fun z => g h₀ + a (z - h₀)) with hG0_def

  have h_diff : ∀ z ∈ A, DifferentiableAt ℝ g z := by
    intro z _
    exact (hg.differentiable (by norm_num)) z

  -- MVT: ‖g y - g x - a (y - x)‖ ≤ ε * ‖y - x‖
  have h_mvt : ‖g y - g x - a (y - x)‖ ≤ ε * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le' h_diff h_osc hA_conv hx hy

  have h_norm_eq : ‖y - x‖ = ‖u‖ := by
    have h : y - x = -(x - y) := by abel
    rw [h, hu_def, norm_neg]

  have h1 : |b - a_u| ≤ ε * ‖u‖ := by
    have h_eq : g y - g x - a (y - x) = -(b - a_u) := by
      simp [hb_def, hau_def, hu_def] <;> ring
    have h_mvt2 : ‖-(b - a_u)‖ ≤ ε * ‖y - x‖ := by
      rw [h_eq] at h_mvt
      exact h_mvt
    have h_norm1 : ‖-(b - a_u)‖ = ‖(b - a_u)‖ := by rw [norm_neg]
    have h_norm2 : ‖(b - a_u)‖ = |b - a_u| := by
      simpa using Real.norm_eq_abs (b - a_u)
    have h_mvt3 : |b - a_u| ≤ ε * ‖y - x‖ := by
      rw [h_norm1, h_norm2] at h_mvt2
      exact h_mvt2
    have h_final : |b - a_u| ≤ ε * ‖u‖ := by
      rw [h_norm_eq] at h_mvt3
      exact h_mvt3
    exact h_final

  -- Norm identities for graph maps
  have h_norm_G : ‖G x - G y‖ ^ 2 = ‖u‖ ^ 2 + b ^ 2 :=
    graphMap_norm_sq_diff g g x y

  have h_affine_diff : (fun z : E m => g h₀ + a (z - h₀)) x -
      (fun z : E m => g h₀ + a (z - h₀)) y = a_u := by
    have h_sub : a (x - h₀) - a (y - h₀) = a ((x - h₀) - (y - h₀)) := by
      rw [← map_sub a (x - h₀) (y - h₀)]
    have h : (g h₀ + a (x - h₀)) - (g h₀ + a (y - h₀)) = a (x - h₀) - a (y - h₀) := by simp
    rw [h, h_sub]
    have h2 : (x - h₀) - (y - h₀) = x - y := by abel
    rw [h2]
    <;> simp [hu_def, hau_def]

  have h_norm_G0 : ‖G₀ x - G₀ y‖ ^ 2 = ‖u‖ ^ 2 + a_u ^ 2 := by
    have h := graphMap_norm_sq_diff
      (fun z : E m => g h₀ + a (z - h₀))
      (fun z : E m => g h₀ + a (z - h₀)) x y
    rw [h, h_affine_diff]

  -- Forward bound
  have h2 : b ^ 2 ≤ a_u ^ 2 + 2 * ε * (‖u‖ ^ 2 + a_u ^ 2) :=
    sq_osc_bound a_u b ‖u‖ ε hε_nonneg hε_le_one h1

  have h3 : ‖u‖ ^ 2 + b ^ 2 ≤ (1 + 2 * ε) * (‖u‖ ^ 2 + a_u ^ 2) := by
    linarith [h2]

  have h4 : ‖G x - G y‖ ^ 2 ≤ (1 + 2 * ε) * ‖G₀ x - G₀ y‖ ^ 2 := by
    rw [h_norm_G, h_norm_G0]
    exact h3

  have h5 : ‖G x - G y‖ ≤ Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖ := by
    have h_sq : (Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖) ^ 2 =
        (1 + 2 * ε) * ‖G₀ x - G₀ y‖ ^ 2 := by
      calc
        (Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖) ^ 2
          = (Real.sqrt (1 + 2 * ε)) ^ 2 * ‖G₀ x - G₀ y‖ ^ 2 := by ring
        _ = (1 + 2 * ε) * ‖G₀ x - G₀ y‖ ^ 2 := by
          rw [Real.sq_sqrt (by linarith)] <;> ring
    by_contra h6
    have h7 : ‖G x - G y‖ > Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖ := by linarith
    have h8 : 0 ≤ Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖ := by positivity
    have h9 : ‖G x - G y‖ ^ 2 > (Real.sqrt (1 + 2 * ε) * ‖G₀ x - G₀ y‖) ^ 2 := by
      nlinarith [h7, h8]
    rw [h_sq] at h9
    linarith [h4]

  -- Reverse bound
  have h1' : |a_u - b| ≤ ε * ‖u‖ := by
    have h_comm : |a_u - b| = |b - a_u| := abs_sub_comm a_u b
    rw [h_comm]
    exact h1

  have h2' : a_u ^ 2 ≤ b ^ 2 + 2 * ε * (‖u‖ ^ 2 + b ^ 2) :=
    sq_osc_bound b a_u ‖u‖ ε hε_nonneg hε_le_one h1'

  have h3' : ‖u‖ ^ 2 + a_u ^ 2 ≤ (1 + 2 * ε) * (‖u‖ ^ 2 + b ^ 2) := by
    linarith [h2']

  have h4' : ‖G₀ x - G₀ y‖ ^ 2 ≤ (1 + 2 * ε) * ‖G x - G y‖ ^ 2 := by
    rw [h_norm_G0, h_norm_G]
    exact h3'

  have h5' : ‖G₀ x - G₀ y‖ ≤ Real.sqrt (1 + 2 * ε) * ‖G x - G y‖ := by
    have h_sq : (Real.sqrt (1 + 2 * ε) * ‖G x - G y‖) ^ 2 =
        (1 + 2 * ε) * ‖G x - G y‖ ^ 2 := by
      calc
        (Real.sqrt (1 + 2 * ε) * ‖G x - G y‖) ^ 2
          = (Real.sqrt (1 + 2 * ε)) ^ 2 * ‖G x - G y‖ ^ 2 := by ring
        _ = (1 + 2 * ε) * ‖G x - G y‖ ^ 2 := by
          rw [Real.sq_sqrt (by linarith)] <;> ring
    by_contra h6
    have h7 : ‖G₀ x - G₀ y‖ > Real.sqrt (1 + 2 * ε) * ‖G x - G y‖ := by linarith
    have h8 : 0 ≤ Real.sqrt (1 + 2 * ε) * ‖G x - G y‖ := by positivity
    have h9 : ‖G₀ x - G₀ y‖ ^ 2 > (Real.sqrt (1 + 2 * ε) * ‖G x - G y‖) ^ 2 := by
      nlinarith [h7, h8]
    rw [h_sq] at h9
    linarith [h4']

  exact ⟨h5, h5'⟩

end GraphAreaFormula
