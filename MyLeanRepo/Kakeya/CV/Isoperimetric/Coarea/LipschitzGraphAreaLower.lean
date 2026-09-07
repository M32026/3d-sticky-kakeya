import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Tactic

/-!
# Lipschitz Graph Area Lower Bound

Proves `lipschitz_graph_area_lower`:
`H^m(graph(g) ∩ cylinder(A)) ≥ ∫⁻ x in A, √(1+‖fderiv g x‖²) dx`

Proof route:
1. `almost_identity_surjective`: IVT-based surjectivity for almost-identity maps
2. `local_area_lower_bound`: at a differentiability point, area of graph over a ball
   is bounded below by `(1-ε)^m · √(1+‖a‖²) · volume(ball)`
3. Globalization via Besicovitch differentiation theorem (Radon-Nikodym derivative)

This avoids Brouwer's fixed point theorem, using only the 1D intermediate value theorem.
-/

open MeasureTheory Metric Set ENNReal LinearMap Filter
open scoped MeasureTheory Pointwise Classical
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

-- ============================================================================
-- Section 1: Almost identity surjectivity (1D IVT trick)
-- ============================================================================

/-- If `F(y) = y + e(y) • c` with `|e(y)| ≤ ε·‖y-x‖` and `‖c‖ ≤ 1/2`,
then `F(ball x r) ⊇ ball x ((1-ε)r)` for `0 < ε < 1`. -/
lemma almost_identity_surjective
    (e : E m → ℝ) (c : E m) (x : E m) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (hε_lt_one : ε < 1)
    (hc_norm : ‖c‖ ≤ 1 / 2)
    (e_cont : Continuous e)
    (he_bound : ∀ y ∈ closedBall x r, |e y| ≤ ε * ‖y - x‖) :
    ∀ (u : E m), u ∈ ball x ((1 - ε) * r) →
      ∃ (y : E m), y ∈ ball x r ∧ y + e y • c = u := by
  intro u hu
  have h_ux : dist u x < (1 - ε) * r := by simpa [mem_ball] using hu
  have h_u_lt : ‖u - x‖ < (1 - ε) * r := by
    have h : dist u x = ‖u - x‖ := by rw [dist_eq_norm]
    rw [h] at h_ux; exact h_ux
  let φ : ℝ → ℝ := fun t => e (u - t • c) - t
  have h_cont : Continuous φ := by fun_prop
  have h_norm_helper : ∀ (t : ℝ), |t| ≤ ε * r →
      ‖u - t • c - x‖ ≤ (1 - ε / 2) * r := by
    intro t ht
    have h1 : ‖u - t • c - x‖ ≤ ‖u - x‖ + ‖t • c‖ := by
      have h2 : u - t • c - x = (u - x) - t • c := by abel
      rw [h2]; exact norm_sub_le _ _
    have h2 : ‖t • c‖ = |t| * ‖c‖ := by rw [norm_smul] <;> rfl
    rw [h2] at h1
    have h3 : |t| * ‖c‖ ≤ ε * r / 2 := by
      have h4 : |t| ≤ ε * r := ht
      have h5 : |t| * ‖c‖ ≤ (ε * r) * ‖c‖ := by gcongr
      have h6 : (ε * r) * ‖c‖ ≤ (ε * r) * (1 / 2 : ℝ) := by
        gcongr
        <;> linarith
      linarith
    linarith
  have h_domain : ∀ (t : ℝ), |t| ≤ ε * r → u - t • c ∈ closedBall x r := by
    intro t ht
    have h1 : ‖u - t • c - x‖ ≤ (1 - ε / 2) * r := h_norm_helper t ht
    have h_pos2 : 0 < ε / 2 * r := by positivity
    have h2 : (1 - ε / 2) * r < r := by
      have h3 : (1 - ε / 2) * r = r - ε / 2 * r := by ring
      rw [h3]; linarith
    have h3 : ‖u - t • c - x‖ ≤ r := by linarith
    simpa [mem_closedBall, dist_eq_norm] using h3
  have h_abs_er : |-(ε * r)| = ε * r := by
    rw [abs_neg, abs_of_pos (mul_pos hε hr)]
  have h_abs_er2 : |ε * r| = ε * r := by
    rw [abs_of_pos (mul_pos hε hr)]
  have h_norm_bound := h_norm_helper
  have h_neg : φ (-(ε * r)) > 0 := by
    let z := u - (-(ε * r)) • c
    have h4 : z ∈ closedBall x r := h_domain (-(ε * r)) (by rw [h_abs_er])
    have h5 : |e z| ≤ ε * ‖z - x‖ := he_bound z h4
    have h6 : ‖z - x‖ ≤ (1 - ε / 2) * r := h_norm_bound (-(ε * r)) (by rw [h_abs_er])
    have h7 : |e z| ≤ ε * ((1 - ε / 2) * r) := by
      calc |e z| ≤ ε * ‖z - x‖ := h5
           _ ≤ ε * ((1 - ε / 2) * r) := by gcongr
    have h8 : -(ε * ((1 - ε / 2) * r)) ≤ e z := (abs_le.mp h7).1
    have h9 : e z + ε * r ≥ ε ^ 2 * r / 2 := by
      have h10 : -(ε * ((1 - ε / 2) * r)) + ε * r = ε ^ 2 * r / 2 := by ring
      linarith
    have h11 : 0 < ε ^ 2 * r / 2 := by positivity
    have h12 : e z + ε * r > 0 := by linarith
    have h13 : φ (-(ε * r)) = e z + ε * r := by
      simp [φ, z] <;> ring
    rw [h13]; exact h12
  have h_pos : φ (ε * r) < 0 := by
    let z := u - (ε * r) • c
    have h4 : z ∈ closedBall x r := h_domain (ε * r) (by rw [h_abs_er2])
    have h5 : |e z| ≤ ε * ‖z - x‖ := he_bound z h4
    have h6 : ‖z - x‖ ≤ (1 - ε / 2) * r := h_norm_bound (ε * r) (by rw [h_abs_er2])
    have h7 : |e z| ≤ ε * ((1 - ε / 2) * r) := by
      calc |e z| ≤ ε * ‖z - x‖ := h5
           _ ≤ ε * ((1 - ε / 2) * r) := by gcongr
    have h8 : e z ≤ ε * ((1 - ε / 2) * r) := (abs_le.mp h7).2
    have h9 : e z - ε * r ≤ -(ε ^ 2 * r / 2) := by
      have h10 : ε * ((1 - ε / 2) * r) - ε * r = -(ε ^ 2 * r / 2) := by ring
      linarith
    have h11 : 0 < ε ^ 2 * r / 2 := by positivity
    have h12 : e z - ε * r < 0 := by linarith
    have h13 : φ (ε * r) = e z - ε * r := by
      simp [φ, z] <;> ring
    rw [h13]; exact h12
  have h_er_pos : 0 < ε * r := mul_pos hε hr
  have h_Icc : (-(ε * r)) ≤ (ε * r) := by
    have h : -(ε * r) ≤ 0 := by linarith
    linarith
  let ψ : ℝ → ℝ := fun t => -φ t
  have hψ_cont : Continuous ψ := by fun_prop
  have hψ_neg : ψ (-(ε * r)) ≤ 0 := by
    simp [ψ, h_neg] <;> linarith
  have hψ_pos : 0 ≤ ψ (ε * r) := by
    simp [ψ, h_pos] <;> linarith
  have h_ivt : ∃ t ∈ Icc (-(ε * r)) (ε * r), ψ t = 0 :=
    intermediate_value_Icc h_Icc hψ_cont.continuousOn ⟨hψ_neg, hψ_pos⟩
  rcases h_ivt with ⟨t, ht_mem, hψ⟩
  have hφ : φ t = 0 := by
    have h1 : ψ t = -φ t := by simp [ψ]
    rw [h1] at hψ
    linarith
  have h_t_bound : |t| ≤ ε * r := by
    have h1 : -(ε * r) ≤ t := ht_mem.1
    have h2 : t ≤ ε * r := ht_mem.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let y := u - t • c
  have h_y_in_ball : y ∈ ball x r := by
    have h1 : ‖y - x‖ ≤ ‖u - x‖ + ‖t • c‖ := by
      have h2 : y - x = (u - x) - t • c := by simp [y] <;> abel
      rw [h2]; exact norm_sub_le _ _
    have h2 : ‖t • c‖ = |t| * ‖c‖ := by rw [norm_smul] <;> rfl
    rw [h2] at h1
    have h3 : |t| * ‖c‖ ≤ ε * r / 2 := by
      have h4 : |t| ≤ ε * r := h_t_bound
      have h5 : |t| * ‖c‖ ≤ (ε * r) * ‖c‖ := by gcongr
      have h6 : (ε * r) * ‖c‖ ≤ (ε * r) * (1 / 2 : ℝ) := by
        gcongr <;> linarith
      linarith
    have h5 : ‖y - x‖ < r := by
      have h_sum : ‖u - x‖ + |t| * ‖c‖ < (1 - ε) * r + ε * r / 2 := by
        exact add_lt_add_of_lt_of_le h_u_lt h3
      have h_eq : (1 - ε) * r + ε * r / 2 = (1 - ε / 2) * r := by ring
      rw [h_eq] at h_sum
      have h6 : (1 - ε / 2) * r < r := by
        have h7 : 0 < ε / 2 * r := by positivity
        linarith
      linarith
    have h6 : dist y x < r := by
      simpa [dist_eq_norm] using h5
    simpa [mem_ball] using h6
  have h_eq : e y = t := by
    have h1 : e y - t = 0 := by simpa [φ, y] using hφ
    exact sub_eq_zero.mp h1
  have h_main : y + e y • c = u := by
    rw [h_eq]
    <;> simp [y] <;> abel
  exact ⟨y, h_y_in_ball, h_main⟩

-- ============================================================================
-- Section 2: Local area lower bound
-- ============================================================================

/-- Local area lower bound: at a differentiability point,
`H^m(graph over ball x r) ≥ (1-ε)^m · √(1+‖a‖²) · volume(ball x r)`. -/
lemma local_area_lower_bound
    (g : E m → ℝ) (x : E m) (a : E m →L[ℝ] ℝ)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε_lt_one : ε < 1)
    (hg : Continuous g)
    (h_approx : ∀ y ∈ closedBall x r,
      |g y - (g x + a (y - x))| ≤ ε * ‖y - x‖) :
    μHE[m] (graphMap g '' ball x r) ≥
      ENNReal.ofReal ((1 - ε) ^ m) *
      ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) *
      volume (ball x r) := by
  let u : E m := rieszVector a
  have h_riesz : ∀ (v : E m), a v = inner ℝ u v := riesz_eq a
  have h_norm_u : ‖u‖ = ‖a‖ := riesz_norm a
  let c : E m := (1 / (1 + ‖a‖ ^ 2)) • u
  have hc_norm : ‖c‖ ≤ 1 / 2 := by
    have h1 : ‖c‖ = ‖a‖ / (1 + ‖a‖ ^ 2) := by
      have h2 : ‖c‖ = |(1 : ℝ) / (1 + ‖a‖ ^ 2)| * ‖u‖ := by
        have h21 : ‖c‖ = ‖(1 : ℝ) / (1 + ‖a‖ ^ 2)‖ * ‖u‖ := by
          rw [show c = ((1 / (1 + ‖a‖ ^ 2)) • u) from rfl, norm_smul]
        have h22 : ‖(1 : ℝ) / (1 + ‖a‖ ^ 2)‖ = |(1 : ℝ) / (1 + ‖a‖ ^ 2)| := by
          rw [Real.norm_eq_abs]
        rw [h21, h22]
      rw [h2]
      have h3 : |(1 : ℝ) / (1 + ‖a‖ ^ 2)| = 1 / (1 + ‖a‖ ^ 2) := by
        rw [abs_of_pos] <;> positivity
      rw [h3, h_norm_u] <;> ring
    rw [h1]
    have h4 : 0 ≤ ‖a‖ := by positivity
    have h5 : ‖a‖ ≤ (1 + ‖a‖ ^ 2) / 2 := by
      have h6 : (‖a‖ - 1) ^ 2 ≥ 0 := by positivity
      nlinarith
    have h7 : 0 < 1 + ‖a‖ ^ 2 := by positivity
    calc ‖a‖ / (1 + ‖a‖ ^ 2)
      ≤ ((1 + ‖a‖ ^ 2) / 2) / (1 + ‖a‖ ^ 2) := by gcongr
    _ = 1 / 2 := by
      field_simp [h7.ne'] <;> ring
  let e : E m → ℝ := fun y => g y - (g x + a (y - x))
  have he_cont : Continuous e := by fun_prop
  have he_bound : ∀ y ∈ closedBall x r, |e y| ≤ ε * ‖y - x‖ := h_approx
  let F : E m → E m := fun y => y + e y • c
  have hF_surj : ∀ (u0 : E m), u0 ∈ ball x ((1 - ε) * r) →
      ∃ (y : E m), y ∈ ball x r ∧ F y = u0 :=
    almost_identity_surjective e c x r ε hr hε hε_lt_one hc_norm he_cont he_bound

  -- Normal vector n = (-u, 1) in E(m+1)
  let n : E (m + 1) := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
    fun i : Fin (m + 1) => if h : i.val < m then -u ⟨i.val, h⟩ else 1
  have hn_last : n (Fin.last m) = 1 := by
    simp [n, EuclideanSpace.equiv] <;> split_ifs <;> omega
  have hn_cast : ∀ (j : Fin m), n (Fin.castSucc j) = -u j := by
    intro j; simp [n, EuclideanSpace.equiv] <;> split_ifs <;> omega
  have h_inner_n : ∀ (p : E (m + 1)), inner ℝ n p = p (Fin.last m) - a (GraphAreaFormula.proj p) := by
    intro p
    have h_sum : inner ℝ n p = ∑ i : Fin (m + 1), n i * p i := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      have h2 : inner ℝ (n i) (p i) = (p i) * (n i) := by simp
      have h3 : (p i) * (n i) = (n i) * (p i) := by ring
      rw [h2, h3]
    rw [h_sum]
    have h2 : ∑ i : Fin (m + 1), n i * p i =
        (∑ j : Fin m, n (Fin.castSucc j) * p (Fin.castSucc j)) + n (Fin.last m) * p (Fin.last m) := by
      rw [Fin.sum_univ_castSucc] <;> rfl
    rw [h2]
    have h3 : ∑ j : Fin m, n (Fin.castSucc j) * p (Fin.castSucc j) =
        ∑ j : Fin m, (-u j) * (GraphAreaFormula.proj p) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hn_cast, GraphAreaFormula.proj_apply] <;> ring
    rw [h3, hn_last]
    have h4 : inner ℝ u (GraphAreaFormula.proj p) = ∑ j : Fin m, u j * (GraphAreaFormula.proj p) j := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j _
      have h41 : inner ℝ (u j) ((GraphAreaFormula.proj p) j) = (u j) * ((GraphAreaFormula.proj p) j) := by
        exact Real.inner_apply (u j) ((GraphAreaFormula.proj p) j)
      exact h41
    have h5 : a (GraphAreaFormula.proj p) = inner ℝ u (GraphAreaFormula.proj p) := h_riesz (GraphAreaFormula.proj p)
    simp [h4, h5] <;> ring
  have h_norm_n_sq : ‖n‖ ^ 2 = 1 + ‖a‖ ^ 2 := by
    have h1 : ‖n‖ ^ 2 = ∑ i : Fin (m + 1), (n i) ^ 2 := EuclideanSpace.real_norm_sq_eq n
    rw [h1]
    have h2 : ∑ i : Fin (m + 1), (n i) ^ 2 =
        (∑ j : Fin m, (n (Fin.castSucc j)) ^ 2) + (n (Fin.last m)) ^ 2 := by
      rw [Fin.sum_univ_castSucc] <;> rfl
    rw [h2]
    have h3 : ∑ j : Fin m, (n (Fin.castSucc j)) ^ 2 = ∑ j : Fin m, (u j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hn_cast] <;> ring
    rw [h3, hn_last]
    have h4 : ‖u‖ ^ 2 = ∑ j : Fin m, (u j) ^ 2 := EuclideanSpace.real_norm_sq_eq u
    rw [←h4, h_norm_u] <;> ring
  let b : ℝ := g x - a x
  -- Orthogonal projection onto affine graph {p | inner n p = b}
  let P : E (m + 1) → E (m + 1) := fun p =>
    p - ((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) • n
  have hP_lipschitz : LipschitzWith 1 P := by
    have h1 : ∀ (p q : E (m + 1)), ‖P p - P q‖ ≤ ‖p - q‖ := by
      intro p q
      set v : E (m + 1) := p - q with hv_def
      set β : ℝ := inner ℝ n v / (1 + ‖a‖ ^ 2) with hβ_def
      have h_pos : 0 < 1 + ‖a‖ ^ 2 := by positivity
      have h_diff : P p - P q = v - β • n := by
        simp only [P]
        have h_id : ((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) -
            ((inner ℝ n q - b) / (1 + ‖a‖ ^ 2)) = β := by
          have h_sub_div : ((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) -
              ((inner ℝ n q - b) / (1 + ‖a‖ ^ 2)) =
              (((inner ℝ n p - b) - (inner ℝ n q - b)) / (1 + ‖a‖ ^ 2)) := by
            ring
          rw [h_sub_div]
          have h_inner_diff : (inner ℝ n p - b) - (inner ℝ n q - b) = inner ℝ n v := by
            have h1 : (inner ℝ n p - b) - (inner ℝ n q - b) = inner ℝ n p - inner ℝ n q := by ring
            rw [h1]
            have h2 : inner ℝ n p - inner ℝ n q = inner ℝ n (p - q) := by
              exact (inner_sub_right n p q).symm
            rw [h2, hv_def]
          rw [h_inner_diff, hβ_def]
        have h_main : (p - ((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) • n) -
            (q - ((inner ℝ n q - b) / (1 + ‖a‖ ^ 2)) • n) =
            v - β • n := by
          calc
            (p - ((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) • n) -
                (q - ((inner ℝ n q - b) / (1 + ‖a‖ ^ 2)) • n)
              = (p - q) - (((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) • n -
                  ((inner ℝ n q - b) / (1 + ‖a‖ ^ 2)) • n) := by abel
            _ = (p - q) - ((((inner ℝ n p - b) / (1 + ‖a‖ ^ 2)) -
                  ((inner ℝ n q - b) / (1 + ‖a‖ ^ 2))) • n) := by rw [←sub_smul]
            _ = v - β • n := by rw [h_id] <;> rfl
        exact h_main
      have h_norm2 : ‖v - β • n‖ ^ 2 = ‖v‖ ^ 2 - β ^ 2 * (1 + ‖a‖ ^ 2) := by
        have h_expand : ‖v - β • n‖ ^ 2 =
            ‖v‖ ^ 2 - 2 * β * inner ℝ v n + β ^ 2 * ‖n‖ ^ 2 := by
          rw [norm_sub_sq_real v (β • n)]
          have h1 : inner ℝ v (β • n) = β * inner ℝ v n := by
            simpa [inner_smul_right] using rfl
          have h2 : ‖β • n‖ ^ 2 = β ^ 2 * ‖n‖ ^ 2 := by
            have h21 : ‖β • n‖ = |β| * ‖n‖ := norm_smul β n
            calc
              ‖β • n‖ ^ 2 = (|β| * ‖n‖) ^ 2 := by rw [h21]
              _ = |β| ^ 2 * ‖n‖ ^ 2 := by rw [mul_pow]
              _ = β ^ 2 * ‖n‖ ^ 2 := by
                have h24 : |β| ^ 2 = β ^ 2 := by simp [sq_abs]
                exact h24 ▸ rfl
          rw [h1, h2] <;> ring
        have h_comm : inner ℝ v n = inner ℝ n v := (real_inner_comm v n).symm
        have h10 : inner ℝ n v = β * (1 + ‖a‖ ^ 2) := by
          rw [hβ_def]
          field_simp [h_pos.ne'] <;> ring
        calc
          ‖v - β • n‖ ^ 2
            = ‖v‖ ^ 2 - 2 * β * inner ℝ v n + β ^ 2 * ‖n‖ ^ 2 := h_expand
          _ = ‖v‖ ^ 2 - 2 * β * inner ℝ n v + β ^ 2 * ‖n‖ ^ 2 := by rw [h_comm]
          _ = ‖v‖ ^ 2 - 2 * β * (β * (1 + ‖a‖ ^ 2)) + β ^ 2 * (1 + ‖a‖ ^ 2) := by
            rw [h10, h_norm_n_sq]
          _ = ‖v‖ ^ 2 - β ^ 2 * (1 + ‖a‖ ^ 2) := by ring
      have h10 : ‖v - β • n‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        rw [h_norm2]
        have h_nonneg : 0 ≤ β ^ 2 * (1 + ‖a‖ ^ 2) := by positivity
        linarith
      have h11 : 0 ≤ ‖v - β • n‖ := by positivity
      have h12 : 0 ≤ ‖v‖ := by positivity
      have h_result : ‖v - β • n‖ ≤ ‖v‖ := by
        by_contra h
        have h' : ‖v‖ < ‖v - β • n‖ := by exact lt_of_not_ge h
        have h'' : ‖v‖ ^ 2 < ‖v - β • n‖ ^ 2 := by nlinarith
        linarith [h10]
      rw [h_diff]
      exact h_result
    exact LipschitzWith.of_dist_le_mul fun p q => by
      simpa [dist_eq_norm] using h1 p q

  -- Affine graph map T
  let g₀ : E m → ℝ := fun z => g x + a (z - x)
  let T : E m → E (m + 1) := graphMap g₀
  have hPT : ∀ (y : E m), P (graphMap g y) = T (F y) := by
    intro y
    have h_e : e y = g y - g₀ y := by
      simp [e, g₀] <;> ring
    have h_ac : a c = ‖a‖ ^ 2 / (1 + ‖a‖ ^ 2) := by
      have h1 : a c = (1 / (1 + ‖a‖ ^ 2)) * a u := by
        simp [c, map_smul] <;> ring
      rw [h1]
      have h2 : a u = inner ℝ u u := h_riesz u
      rw [h2]
      have h3 : inner ℝ u u = ‖u‖ ^ 2 := inner_self_eq_norm_sq_to_K u
      rw [h3, h_norm_u] <;> ring
    ext i
    by_cases h_i : i.val < m
    · let j : Fin m := ⟨i.val, h_i⟩
      have hi : i = Fin.castSucc j := by apply Fin.ext <;> simp [j]
      rw [hi]
      have h_goal : (P (graphMap g y)) (Fin.castSucc j) = (T (F y)) (Fin.castSucc j) := by
        have h1 : (P (graphMap g y)) (Fin.castSucc j) =
            (graphMap g y) (Fin.castSucc j) -
            ((inner ℝ n (graphMap g y) - b) / (1 + ‖a‖ ^ 2)) * n (Fin.castSucc j) := by
          simp [P]
        have h_inner : inner ℝ n (graphMap g y) - b = e y := by
          have h9 : inner ℝ n (graphMap g y) = (graphMap g y) (Fin.last m) - a (GraphAreaFormula.proj (graphMap g y)) := h_inner_n (graphMap g y)
          rw [h9, graphMap_apply_last, graphMap_proj, h_e]
          <;> simp [b, g₀] <;> ring
        rw [h1, h_inner, hn_cast, graphMap_apply_castSucc]
        have h2 : (T (F y)) (Fin.castSucc j) = (F y) j := by
          simp [T, graphMap_apply_castSucc]
        rw [h2]
        simp [F, c, h_e] <;> ring
      exact h_goal
    · have hi : i = Fin.last m := by
        apply Fin.ext; simp [h_i] <;> omega
      rw [hi]
      have h_goal : (P (graphMap g y)) (Fin.last m) = (T (F y)) (Fin.last m) := by
        have h1 : (P (graphMap g y)) (Fin.last m) =
            g y - (e y) / (1 + ‖a‖ ^ 2) := by
          have h_inner : inner ℝ n (graphMap g y) - b = e y := by
            have h9 : inner ℝ n (graphMap g y) = (graphMap g y) (Fin.last m) - a (GraphAreaFormula.proj (graphMap g y)) := h_inner_n (graphMap g y)
            rw [h9, graphMap_apply_last, graphMap_proj, h_e]
            <;> simp [b, g₀] <;> ring
          have hP_last : (P (graphMap g y)) (Fin.last m) =
              (graphMap g y) (Fin.last m) - ((inner ℝ n (graphMap g y) - b) / (1 + ‖a‖ ^ 2)) * n (Fin.last m) := by
            simp [P]
          rw [hP_last, h_inner, hn_last, graphMap_apply_last]
          <;> ring
        have h2 : (T (F y)) (Fin.last m) = g₀ (F y) := by
          simp [T, graphMap_apply_last]
        rw [h1, h2]
        have h3 : g₀ (F y) = g y - e y / (1 + ‖a‖ ^ 2) := by
          have h4 : g₀ (F y) = g x + a (F y - x) := by simp [g₀]
          rw [h4]
          have h5 : F y - x = (y - x) + e y • c := by
            simp [F] <;> abel
          rw [h5]
          have h6 : a ((y - x) + e y • c) = a (y - x) + e y * a c := by
            simp [map_add, map_smul] <;> ring
          rw [h6, h_ac]
          have h7 : g x + a (y - x) = g₀ y := by simp [g₀] <;> ring
          have h7' : g x + (a (y - x) + e y * (‖a‖ ^ 2 / (1 + ‖a‖ ^ 2))) =
              g₀ y + e y * (‖a‖ ^ 2 / (1 + ‖a‖ ^ 2)) := by
            have h_abel : g x + (a (y - x) + e y * (‖a‖ ^ 2 / (1 + ‖a‖ ^ 2))) =
                (g x + a (y - x)) + e y * (‖a‖ ^ 2 / (1 + ‖a‖ ^ 2)) := by abel
            rw [h_abel, h7]
          rw [h7']
          have h8 : g₀ y + e y * (‖a‖ ^ 2 / (1 + ‖a‖ ^ 2)) = g y - e y / (1 + ‖a‖ ^ 2) := by
            have h9 : g y = g₀ y + e y := by
              simp [h_e] <;> ring
            rw [h9]
            field_simp <;> ring
          exact h8
        exact h3.symm
      exact h_goal

  -- Main argument
  have h2 : P '' (graphMap g '' ball x r) = T '' F '' (ball x r) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨F y, ⟨y, hy, rfl⟩, (hPT y).symm⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨graphMap g y, ⟨y, hy, rfl⟩, hPT y⟩
  have h3 : T '' ball x ((1 - ε) * r) ⊆ T '' (F '' ball x r) := by
    have h4 : ball x ((1 - ε) * r) ⊆ F '' (ball x r) := by
      intro u0 hu
      exact hF_surj u0 hu
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact ⟨y, h4 hy, rfl⟩
  have hP_on : LipschitzOnWith 1 P (graphMap g '' ball x r) :=
    hP_lipschitz.lipschitzOnWith
  have h41 : μHE[m] (P '' (graphMap g '' ball x r)) ≤ (1 : ENNReal)^(m : ℝ) * μHE[m] (graphMap g '' ball x r) :=
    lipschitzOnWith_euclideanHausdorffMeasure_image_le hP_on
  have h42 : (1 : ENNReal)^(m : ℝ) = 1 := by simp
  have h4 : μHE[m] (graphMap g '' ball x r) ≥ μHE[m] (P '' (graphMap g '' ball x r)) := by
    rw [h42] at h41
    simpa using h41
  have h3' : T '' ball x ((1 - ε) * r) ⊆ P '' (graphMap g '' ball x r) := by
    simpa [h2] using h3
  have h5 : μHE[m] (P '' (graphMap g '' ball x r)) ≥ μHE[m] (T '' ball x ((1 - ε) * r)) :=
    measure_mono h3'
  let b' : ℝ := g x - a x
  have h_g₀_eq : g₀ = fun y : E m => a y + b' := by
    funext y
    simp [g₀, b'] <;> ring
  have h_img : T '' ball x ((1 - ε) * r) = graph g₀ ∩ cylinder (ball x ((1 - ε) * r)) :=
    (graph_cylinder_eq_image g₀ (ball x ((1 - ε) * r))).symm
  have h6 : μHE[m] (T '' ball x ((1 - ε) * r)) =
      ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume (ball x ((1 - ε) * r)) := by
    rw [h_img, h_g₀_eq]
    exact graph_area_affine (a := a) (b := b') (ball x ((1 - ε) * r)) (isOpen_ball.measurableSet)
  have h_pos : 0 < 1 - ε := by linarith
  have h7 : volume (ball x ((1 - ε) * r)) =
      ENNReal.ofReal ((1 - ε) ^ m) * volume (ball x r) := by
    have h_finrank : Module.finrank ℝ (E m) = m := by simp [E]
    have h_nonneg1 : 0 ≤ (1 - ε) * r := by positivity
    have h_nonneg2 : 0 ≤ r := by positivity
    have h1 : volume (ball x ((1 - ε) * r)) =
        ENNReal.ofReal (((1 - ε) * r) ^ Module.finrank ℝ (E m)) * volume (ball (0 : E m) 1) :=
      Measure.addHaar_ball volume x h_nonneg1
    have h2 : volume (ball x r) =
        ENNReal.ofReal (r ^ Module.finrank ℝ (E m)) * volume (ball (0 : E m) 1) :=
      Measure.addHaar_ball volume x h_nonneg2
    rw [h1, h2, h_finrank]
    have h3 : ((1 - ε) * r) ^ m = (1 - ε) ^ m * r ^ m := by rw [mul_pow]
    rw [h3]
    have h4 : ENNReal.ofReal ((1 - ε) ^ m * r ^ m) =
        ENNReal.ofReal ((1 - ε) ^ m) * ENNReal.ofReal (r ^ m) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> ring
    rw [h4] <;> ring
  have h_result : μHE[m] (graphMap g '' ball x r) ≥
      ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume (ball x r)) := by
    calc
      μHE[m] (graphMap g '' ball x r)
        ≥ μHE[m] (P '' (graphMap g '' ball x r)) := h4
      _ ≥ μHE[m] (T '' ball x ((1 - ε) * r)) := h5
      _ = ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume (ball x ((1 - ε) * r)) := h6
      _ = ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * (ENNReal.ofReal ((1 - ε) ^ m) * volume (ball x r)) := by rw [h7]
      _ = ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume (ball x r)) := by ring
  have h_final2 : ENNReal.ofReal ((1 - ε) ^ m) * ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume (ball x r) =
      ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume (ball x r)) := by ring
  rw [h_final2]
  exact h_result

-- ============================================================================
-- Global lower area formula via Besicovitch differentiation
-- ============================================================================

/-- `graphMap g` is Lipschitz with constant `√(1+L²)`. -/
lemma graphMap_lipschitz_global {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    LipschitzWith (⟨Real.sqrt (1 + (L : ℝ)^2), by positivity⟩ : NNReal) (graphMap g) := by
  have h_on : LipschitzOnWith L g Set.univ := hg.lipschitzOnWith
  have h' : LipschitzOnWith (⟨Real.sqrt (1 + (L : ℝ)^2), by positivity⟩) (graphMap g) Set.univ :=
    graphMap_lipschitzOnWith h_on
  exact lipschitzOnWith_univ.mp h'

/-- `graphAreaMeasure g` is locally finite for Lipschitz `g`. -/
lemma graphAreaMeasure_locallyFinite_lipschitz {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    IsLocallyFiniteMeasure (graphAreaMeasure g) := by
  refine' ⟨fun x => _⟩
  let B : Set (E m) := closedBall x 1
  have hB_bdd : Bornology.IsBounded B := isBounded_closedBall
  have hB_meas : MeasurableSet B := isClosed_closedBall.measurableSet
  have h1 : graphAreaMeasure g B = μHE[m] (graphMap g '' B) :=
    graphAreaMeasure_apply_image g hB_meas
  refine ⟨B, closedBall_mem_nhds x (by norm_num), ?_⟩
  rw [h1]
  let K' : NNReal := ⟨Real.sqrt (1 + (L : ℝ)^2), by positivity⟩
  have hK' : LipschitzWith K' (graphMap g) := graphMap_lipschitz_global hg
  have hK_on : LipschitzOnWith K' (graphMap g) B := hK'.lipschitzOnWith
  have h2 : μHE[m] (graphMap g '' B) ≤ (K' : ENNReal)^(m : ℝ) * μHE[m] B :=
    lipschitzOnWith_euclideanHausdorffMeasure_image_le hK_on
  have h3 : (μHE[m] : Measure (E m)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
  rw [h3] at h2
  have h4 : volume B < ⊤ := hB_bdd.measure_lt_top
  have h5 : (K' : ENNReal)^(m : ℝ) * volume B < ⊤ := mul_lt_top (by simp) h4
  exact lt_of_le_of_lt h2 h5

/-- `graphAreaMeasure g ≪ volume` for Lipschitz `g`. -/
lemma graphAreaMeasure_ac_lipschitz {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g) :
    (graphAreaMeasure g).AbsolutelyContinuous volume := by
  let K' : NNReal := ⟨Real.sqrt (1 + (L : ℝ)^2), by positivity⟩
  have hK' : LipschitzWith K' (graphMap g) := graphMap_lipschitz_global hg
  refine' Measure.AbsolutelyContinuous.mk fun S hS_meas hS_vol => _
  have h3 : graphAreaMeasure g S ≤ graphAreaMeasure g (toMeasurable volume S) :=
    measure_mono (subset_toMeasurable volume S)
  have h4 : graphAreaMeasure g (toMeasurable volume S) =
      μHE[m] (graphMap g '' (toMeasurable volume S)) :=
    graphAreaMeasure_apply_image g (measurableSet_toMeasurable volume S)
  rw [h4] at h3
  have hK_on : LipschitzOnWith K' (graphMap g) (toMeasurable volume S) := hK'.lipschitzOnWith
  have h5 : μHE[m] (graphMap g '' (toMeasurable volume S)) ≤
      (K' : ENNReal)^(m : ℝ) * μHE[m] (toMeasurable volume S) :=
    lipschitzOnWith_euclideanHausdorffMeasure_image_le hK_on
  have h6 : (μHE[m] : Measure (E m)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
  rw [h6] at h5
  have hvol : volume (toMeasurable volume S) = 0 := by
    rw [measure_toMeasurable] <;> exact hS_vol
  rw [hvol] at h5
  have h7 : (K' : ENNReal)^(m : ℝ) * 0 = 0 := by simp
  rw [h7] at h5
  exact le_zero_iff.mp (h3.trans h5)

/-- **Lower area formula for Lipschitz graphs.**

`μHE[m](graphMap g '' A) ≥ ∫⁻ x in A, ENNReal.ofReal (√(1 + ‖fderiv g x‖²))`.

Proof: Let ρ = graphAreaMeasure g. By Besicovitch differentiation,
ρ.rnDeriv volume(x) = lim_{r→0} ρ(closedBall x r)/volume(closedBall x r) a.e.
At each differentiability point, `local_area_lower_bound` gives liminf ≥ c(x).
Hence ρ.rnDeriv ≥ c a.e., and integrating gives the result. -/
lemma lipschitz_graph_area_lower
    {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    (A : Set (E m)) (hA : MeasurableSet A) :
    μHE[m] (graphMap g '' A) ≥
      ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)) := by
  let ρ : Measure (E m) := graphAreaMeasure g
  let c : E m → ENNReal := fun x => ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2))
  have hρ_locFin : IsLocallyFiniteMeasure ρ := graphAreaMeasure_locallyFinite_lipschitz hg
  have hρ_ac : ρ.AbsolutelyContinuous volume := graphAreaMeasure_ac_lipschitz hg
  have hg_diff : ∀ᵐ (x : E m) ∂volume, DifferentiableAt ℝ g x :=
    hg.ae_differentiableAt_of_real
  have h_main : ∀ᵐ (x : E m) ∂volume, ρ.rnDeriv volume x ≥ c x := by
    filter_upwards [hg_diff, Besicovitch.ae_tendsto_rnDeriv ρ volume] with x hx_diff hx_tendsto
    set a : E m →L[ℝ] ℝ := fderiv ℝ g x with ha_def
    have h_fd : HasFDerivAt g a x := hx_diff.hasFDerivAt
    have h_littleO : (fun y : E m => g y - g x - a (y - x)) =o[nhds x] (fun y : E m => y - x) :=
      hasFDerivAt_iff_isLittleO.mp h_fd
    have h_goal : ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
          ρ (closedBall x r) / volume (closedBall x r) ≥
            ENNReal.ofReal ((1 - ε) ^ m) * c x := by
      intro ε hε_pos hε_lt_one
      have h2 : ∀ᶠ (z : E m) in nhds x, ‖g z - g x - a (z - x)‖ ≤ ε * ‖z - x‖ :=
        h_littleO.def hε_pos
      rcases Metric.mem_nhds_iff.mp h2 with ⟨r, hr_pos, h3⟩
      have h_ev : ∀ᶠ (ρ' : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 < ρ' ∧ ρ' < r := by
        have h1 : Iio r ∈ nhds (0 : ℝ) := Iio_mem_nhds (by linarith)
        have h2 : Set.Ioi (0 : ℝ) ∩ Iio r ∈ nhdsWithin 0 (Set.Ioi (0 : ℝ)) :=
          inter_mem_nhdsWithin (Set.Ioi 0) h1
        filter_upwards [h2] with ρ' hρ'
        exact ⟨hρ'.1, hρ'.2⟩
      filter_upwards [h_ev] with ρ' hρ'
      have hρ'_pos : 0 < ρ' := hρ'.1
      have hρ'_lt_r : ρ' < r := hρ'.2
      have h_approx : ∀ y ∈ closedBall x ρ', |g y - (g x + a (y - x))| ≤ ε * ‖y - x‖ := by
        intro y hy
        have h_in_ball : y ∈ ball x r := by
          have h1 : dist y x ≤ ρ' := by simpa [mem_closedBall] using hy
          have h2 : dist y x < r := by linarith
          simpa [mem_ball] using h2
        have h4 : ‖g y - g x - a (y - x)‖ ≤ ε * ‖y - x‖ := h3 h_in_ball
        have h5 : g y - (g x + a (y - x)) = g y - g x - a (y - x) := by ring
        have h6 : |g y - (g x + a (y - x))| = ‖g y - g x - a (y - x)‖ := by
          rw [h5]; simp [Real.norm_eq_abs]
        rw [h6] <;> exact h4
      have h_ball_lower : μHE[m] (graphMap g '' ball x ρ') ≥
          ENNReal.ofReal ((1 - ε) ^ m) * c x * volume (ball x ρ') := by
        exact local_area_lower_bound g x a ρ' ε hρ'_pos hε_pos hε_lt_one
          hg.continuous h_approx
      have h_sub : ball x ρ' ⊆ closedBall x ρ' := ball_subset_closedBall
      have h9 : ρ (closedBall x ρ') ≥ ρ (ball x ρ') := measure_mono h_sub
      have h10 : ρ (ball x ρ') = μHE[m] (graphMap g '' ball x ρ') :=
        graphAreaMeasure_apply_image g (isOpen_ball.measurableSet)
      rw [h10] at h9
      have h_vol_eq : volume (ball x ρ') = volume (closedBall x ρ') := by
        have h_finrank : Module.finrank ℝ (E m) = m := by simp [E]
        have h1 : volume (ball x ρ') = ENNReal.ofReal (ρ' ^ Module.finrank ℝ (E m)) * volume (ball (0 : E m) 1) :=
          Measure.addHaar_ball volume x hρ'_pos.le
        have h2 : volume (closedBall x ρ') = ENNReal.ofReal (ρ' ^ Module.finrank ℝ (E m)) * volume (ball (0 : E m) 1) :=
          Measure.addHaar_closedBall volume x hρ'_pos.le
        rw [h1, h2]
      have h12 : volume (closedBall x ρ') ≠ 0 := by
        have h_open : IsOpen (ball x ρ') := isOpen_ball
        have h_nonempty : Nonempty (ball x ρ') := by
          refine ⟨x, by simp [hρ'_pos]⟩
        have h_pos_ball : 0 < volume (ball x ρ') :=
          Metric.measure_ball_pos volume x hρ'_pos
        have h_sub : ball x ρ' ⊆ closedBall x ρ' := ball_subset_closedBall
        have h : volume (ball x ρ') ≤ volume (closedBall x ρ') := measure_mono h_sub
        have h13 : 0 < volume (closedBall x ρ') := lt_of_lt_of_le h_pos_ball h
        exact h13.ne'
      have h14 : volume (closedBall x ρ') ≠ ⊤ := isBounded_closedBall.measure_lt_top.ne
      have h_goal2 : (ENNReal.ofReal ((1 - ε) ^ m) * c x * volume (closedBall x ρ')) / volume (closedBall x ρ') =
          ENNReal.ofReal ((1 - ε) ^ m) * c x := by
        let A := ENNReal.ofReal ((1 - ε) ^ m) * c x
        have h : (A * volume (closedBall x ρ')) / volume (closedBall x ρ') = A :=
          ENNReal.mul_div_cancel_right h12 h14
        simpa [A, mul_assoc] using h
      calc
        ρ (closedBall x ρ') / volume (closedBall x ρ')
          ≥ μHE[m] (graphMap g '' ball x ρ') / volume (closedBall x ρ') := by gcongr
        _ ≥ (ENNReal.ofReal ((1 - ε) ^ m) * c x * volume (ball x ρ')) / volume (closedBall x ρ') := by gcongr
        _ = (ENNReal.ofReal ((1 - ε) ^ m) * c x * volume (closedBall x ρ')) / volume (closedBall x ρ') := by
          rw [h_vol_eq]
        _ = ENNReal.ofReal ((1 - ε) ^ m) * c x := h_goal2
    have h_tendsto : Filter.Tendsto (fun r : ℝ => ρ (closedBall x r) / volume (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ρ.rnDeriv volume x)) := hx_tendsto
    have h_forall_eps : ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ENNReal.ofReal ((1 - ε) ^ m) * c x ≤ ρ.rnDeriv volume x := by
      intro ε hε_pos hε_lt_one
      have h_eventually := h_goal ε hε_pos hε_lt_one
      exact ge_of_tendsto h_tendsto h_eventually
    have h_cx_lt_top : c x ≠ ⊤ := ENNReal.ofReal_lt_top.ne
    have h_cont1 : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ m)) :=
      ENNReal.continuous_ofReal.comp (by continuity)
    have h_cont : Continuous (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ m) * c x) :=
      (ENNReal.continuous_mul_const h_cx_lt_top).comp h_cont1
    have h_tendsto2 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ m) * c x)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (c x)) := by
      have h_at0 : (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ m) * c x) 0 = c x := by simp
      have h_nhds : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ m) * c x)
          (nhds (0 : ℝ)) (nhds ((fun ε : ℝ => ENNReal.ofReal ((1 - ε) ^ m) * c x) 0)) :=
        h_cont.continuousAt.tendsto
      rw [h_at0] at h_nhds
      exact h_nhds.mono_left nhdsWithin_le_nhds
    have h_eventually2 : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ENNReal.ofReal ((1 - ε) ^ m) * c x ≤ ρ.rnDeriv volume x := by
      have h2 : Iio (1 : ℝ) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by norm_num)
      have h1 : Set.Ioi (0 : ℝ) ∩ Iio (1 : ℝ) ∈ nhdsWithin 0 (Set.Ioi (0 : ℝ)) :=
        inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) h2
      filter_upwards [h1] with ε hε
      exact h_forall_eps ε hε.1 hε.2
    exact le_of_tendsto h_tendsto2 h_eventually2
  have h1 : ρ A = ∫⁻ x in A, ρ.rnDeriv volume x :=
    (MeasureTheory.Measure.setLIntegral_rnDeriv' hρ_ac hA).symm
  have h_main' : ∀ᵐ (x : E m) ∂volume, x ∈ A → c x ≤ ρ.rnDeriv volume x :=
    h_main.mono (fun x hx _ => hx)
  have h2 : ∫⁻ x in A, c x ≤ ∫⁻ x in A, ρ.rnDeriv volume x :=
    MeasureTheory.setLIntegral_mono_ae' hA h_main'
  have hρA : ρ A = μHE[m] (graphMap g '' A) := graphAreaMeasure_apply_image g hA
  calc
    μHE[m] (graphMap g '' A) = ρ A := hρA.symm
    _ = ∫⁻ x in A, ρ.rnDeriv volume x := h1
    _ ≥ ∫⁻ x in A, c x := h2

end Geometry.Isoperimetric
