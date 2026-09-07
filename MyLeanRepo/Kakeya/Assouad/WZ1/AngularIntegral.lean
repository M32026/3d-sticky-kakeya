import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Algebra.Order.Field.GeomSum


/-!
# Angular integral bound for Frostman sets of directions

If Λ is a (δ, β, C)-Frostman set of unit vectors in ℝ², then for any unit
vector v and 0 < γ < β, the regularized angular sum
`Σ_{θ∈Λ} max(|⟨θ,v⟩|, δ)^(-γ)` is bounded by `K(β,γ) * C * |Λ|`.

This is a key ingredient in the Kaufman projection theorem.

## Proof sketch

Let w = v⊥. For unit θ, if |⟨θ,v⟩| ≤ r then θ lies within distance √2·r
of either w or -w. Thus Frostman's condition at radius √2·r bounds the
number of directions in any angular band.

1. Small band S = {|⟨θ,v⟩| ≤ δ}: bounded by Frostman at radius √2·δ,
   each term contributes δ^(-γ); total ≤ 2·C·(√2)^β·|Λ|.
2. Dyadic shells A_k = {2^(-k-1) < |⟨θ,v⟩| ≤ 2^(-k)}:
   - k=0: use Frostman around v, -v at radius 1
   - k≥1: use Frostman around w, -w at radius √2·2^(-k)
   Each term in A_k contributes ≤ 2^((k+1)γ).
3. Geometric series with ratio 2^(-(β-γ)) < 1.

NOTE: The regularization `max(|⟨θ,v⟩|, δ)` is necessary because without
it, a single direction nearly perpendicular to v can make the sum
arbitrarily large.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

/-- Expand the inner product on `Point2` as a coordinate dot product. -/
lemma point2_inner_eq (a b : Point2) :
    inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  have h1 : inner ℝ a b = ∑ i : Fin 2, inner ℝ (a i) (b i) :=
    PiLp.inner_apply a b
  rw [h1]
  have h2 : ∑ i : Fin 2, inner ℝ (a i) (b i) = a 0 * b 0 + a 1 * b 1 := by
    rw [Fin.sum_univ_two]
    <;> simp
    <;> ring
  exact h2

/-- Distance squared between two unit vectors in `Point2`. -/
lemma dist_unit_sq {a b : Point2} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    dist a b ^ 2 = 2 - 2 * inner ℝ a b := by
  have h1 : dist a b ^ 2 = ‖a - b‖ ^ 2 := by rfl
  rw [h1]
  have h2 : ‖a - b‖ ^ 2 = inner ℝ (a - b) (a - b) := by
    rw [←real_inner_self_eq_norm_sq (a - b)]
  rw [h2]
  have h31 : inner ℝ (a - b) (a - b) = inner ℝ a (a - b) - inner ℝ b (a - b) := by
    rw [inner_sub_left]
  have h32 : inner ℝ a (a - b) = inner ℝ a a - inner ℝ a b := by
    rw [inner_sub_right]
  have h33 : inner ℝ b (a - b) = inner ℝ b a - inner ℝ b b := by
    rw [inner_sub_right]
  have h34 : inner ℝ b a = inner ℝ a b := Eq.symm (real_inner_comm b a)
  have h3 : inner ℝ (a - b) (a - b) = inner ℝ a a - 2 * inner ℝ a b + inner ℝ b b := by
    rw [h31, h32, h33, h34] <;> ring
  rw [h3]
  have h4 : inner ℝ a a = ‖a‖^2 := real_inner_self_eq_norm_sq a
  have h5 : inner ℝ b b = ‖b‖^2 := real_inner_self_eq_norm_sq b
  rw [h4, h5, ha, hb]
  <;> ring

/-- Pythagorean identity: for ‖v‖=1, `inner θ v` and `inner θ (v⊥)` are
orthogonal components summing in square to `‖θ‖²`. -/
lemma pythagorean_perp2 {θ v : Point2} (hv : ‖v‖ = 1) :
    (inner ℝ θ v)^2 + (inner ℝ θ (wz1Perp2 v))^2 = ‖θ‖^2 := by
  have h1 : inner ℝ θ v = θ 0 * v 0 + θ 1 * v 1 := point2_inner_eq θ v
  have h_w0 : (wz1Perp2 v) 0 = -v 1 := by
    simp [wz1Perp2, EuclideanSpace.single_apply] <;> ring
  have h_w1 : (wz1Perp2 v) 1 = v 0 := by
    simp [wz1Perp2, EuclideanSpace.single_apply] <;> ring
  have h2 : inner ℝ θ (wz1Perp2 v) = -θ 0 * v 1 + θ 1 * v 0 := by
    rw [point2_inner_eq θ (wz1Perp2 v), h_w0, h_w1] <;> ring
  have h3 : ‖v‖^2 = (v 0)^2 + (v 1)^2 := by
    have h4 : inner ℝ v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
    have h5 : inner ℝ v v = (v 0)^2 + (v 1)^2 := by
      rw [point2_inner_eq v v] <;> ring
    linarith
  have h6 : ‖θ‖^2 = (θ 0)^2 + (θ 1)^2 := by
    have h7 : inner ℝ θ θ = ‖θ‖^2 := real_inner_self_eq_norm_sq θ
    have h8 : inner ℝ θ θ = (θ 0)^2 + (θ 1)^2 := by
      rw [point2_inner_eq θ θ] <;> ring
    linarith
  rw [h1, h2, h6]
  have h9 : (v 0)^2 + (v 1)^2 = 1 := by
    rw [←h3, hv] <;> norm_num
  nlinarith

/-- Key inequality: for |x| ≤ 1, `sqrt(1 - x^2) ≥ 1 - x^2`. -/
private lemma sqrt_one_minus_sq_ge (x : ℝ) (hx : |x| ≤ 1) :
    Real.sqrt (1 - x^2) ≥ 1 - x^2 := by
  have h1 : 0 ≤ 1 - x^2 := by nlinarith [abs_le.mp hx]
  have h2 : (1 - x^2)^2 ≤ 1 - x^2 := by nlinarith [abs_le.mp hx]
  have h3 : Real.sqrt ((1 - x^2)^2) ≤ Real.sqrt (1 - x^2) := Real.sqrt_le_sqrt h2
  have h4 : Real.sqrt ((1 - x^2)^2) = 1 - x^2 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h1]
  linarith

/-- Geometric lemma: for unit θ,v, if |inner θ v| ≤ r then θ is within
distance √2·r of either v⊥ or -v⊥. -/
lemma dist_to_perp_or_neg {θ v : Point2} (hθ : ‖θ‖ = 1) (hv : ‖v‖ = 1)
    {r : ℝ} (hr : 0 ≤ r) (h : |inner ℝ θ v| ≤ r) :
    dist θ (wz1Perp2 v) ≤ Real.sqrt 2 * r ∨
    dist θ (-(wz1Perp2 v)) ≤ Real.sqrt 2 * r := by
  set w : Point2 := wz1Perp2 v with hw_def
  have h_pyth : (inner ℝ θ v)^2 + (inner ℝ θ w)^2 = 1 := by
    rw [pythagorean_perp2 hv, hθ] <;> norm_num
  have h_abs_le : (inner ℝ θ v)^2 ≤ r^2 := by
    have h5 : (inner ℝ θ v)^2 = |inner ℝ θ v|^2 := by rw [sq_abs]
    rw [h5]; gcongr
  have h_inner_bound : |inner ℝ θ v| ≤ 1 := by
    calc |inner ℝ θ v| ≤ ‖θ‖ * ‖v‖ := abs_real_inner_le_norm θ v
      _ = 1 := by rw [hθ, hv] <;> ring
  have h_norm_w : ‖w‖ = 1 := by
    have h1 : w 0 = -v 1 := by simp [w, wz1Perp2] <;> rfl
    have h2 : w 1 = v 0 := by simp [w, wz1Perp2] <;> rfl
    have h3 : ‖w‖^2 = (w 0)^2 + (w 1)^2 := by
      have h4 : inner ℝ w w = ‖w‖^2 := real_inner_self_eq_norm_sq w
      have h5 : inner ℝ w w = (w 0)^2 + (w 1)^2 := by
        rw [point2_inner_eq w w] <;> ring
      linarith
    have h6 : (w 0)^2 + (w 1)^2 = (v 0)^2 + (v 1)^2 := by
      rw [h1, h2] <;> ring
    have h7 : (v 0)^2 + (v 1)^2 = 1 := by
      have h8 : ‖v‖^2 = (v 0)^2 + (v 1)^2 := by
        have h9 : inner ℝ v v = ‖v‖^2 := real_inner_self_eq_norm_sq v
        have h10 : inner ℝ v v = (v 0)^2 + (v 1)^2 := by
          rw [point2_inner_eq v v] <;> ring
        linarith
      rw [←h8, hv] <;> norm_num
    have h9 : ‖w‖^2 = 1 := by linarith
    have h10 : 0 ≤ ‖w‖ := by positivity
    nlinarith
  by_cases h7 : 0 ≤ inner ℝ θ w
  · left
    have h9 : (inner ℝ θ w)^2 = 1 - (inner ℝ θ v)^2 := by linarith
    have h10 : inner ℝ θ w = Real.sqrt (1 - (inner ℝ θ v)^2) := by
      rw [←Real.sqrt_sq h7, h9]
    have h11 : inner ℝ θ w ≥ 1 - (inner ℝ θ v)^2 := by
      rw [h10]; exact sqrt_one_minus_sq_ge (inner ℝ θ v) h_inner_bound
    have h12 : dist θ w ^ 2 ≤ 2 * (inner ℝ θ v)^2 := by
      have h13 := dist_unit_sq hθ h_norm_w
      rw [h13]; linarith
    have h14 : dist θ w ^ 2 ≤ 2 * r^2 := by
      calc dist θ w ^ 2 ≤ 2 * (inner ℝ θ v)^2 := h12
        _ ≤ 2 * r^2 := by gcongr
    have h15 : 0 ≤ Real.sqrt 2 * r := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · right
    have h7' : 0 ≤ inner ℝ θ (-w) := by
      simpa [inner_neg_right] using le_of_lt (not_le.mp h7)
    have h91 : inner ℝ θ (-w) = -inner ℝ θ w := by rw [inner_neg_right]
    have h9 : (inner ℝ θ (-w))^2 = (inner ℝ θ w)^2 := by rw [h91, neg_sq]
    have h92 : (inner ℝ θ (-w))^2 = 1 - (inner ℝ θ v)^2 := by
      rw [h9]; linarith [h_pyth]
    have h10 : inner ℝ θ (-w) = Real.sqrt (1 - (inner ℝ θ v)^2) := by
      rw [←Real.sqrt_sq h7', h92]
    have h11 : inner ℝ θ (-w) ≥ 1 - (inner ℝ θ v)^2 := by
      rw [h10]; exact sqrt_one_minus_sq_ge (inner ℝ θ v) h_inner_bound
    have h_norm_negw : ‖(-w)‖ = 1 := by rw [norm_neg] <;> exact h_norm_w
    have h13 : dist θ (-w) ^ 2 ≤ 2 * (inner ℝ θ v)^2 := by
      have h14 := dist_unit_sq hθ h_norm_negw
      rw [h14]; linarith
    have h15 : dist θ (-w) ^ 2 ≤ 2 * r^2 := by
      calc dist θ (-w) ^ 2 ≤ 2 * (inner ℝ θ v)^2 := h13
        _ ≤ 2 * r^2 := by gcongr
    have h16 : 0 ≤ Real.sqrt 2 * r := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Pure real-number helper: if `x > 2^(-(k+1))` and `x > δ > 0`, then
`max(x, δ)^(-γ) ≤ 2^((k+1)*γ)`. -/
private lemma regularized_bound (k : ℕ) (δ γ x : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hx_pos : 0 < x) (hx1 : (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < x) (hxδ : δ ≤ x) :
    (max x δ)^(-γ) ≤ (2 : ℝ)^(((k + 1 : ℕ) : ℝ) * γ) := by
  have h6 : max x δ = x := by rw [max_eq_left] <;> linarith
  rw [h6]
  set a : ℝ := (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) with ha_def
  have ha_pos : 0 < a := by positivity
  have h9 : a^γ < x^γ := Real.rpow_lt_rpow ha_pos.le hx1 hγ
  have h10 : x^(-γ) ≤ a^(-γ) := by
    have h10a : x^(-γ) = 1 / x^γ := by
      rw [Real.rpow_neg hx_pos.le] <;> field_simp
    have h10b : a^(-γ) = 1 / a^γ := by
      rw [Real.rpow_neg ha_pos.le] <;> field_simp
    rw [h10a, h10b]
    exact one_div_le_one_div_of_le (by positivity) h9.le
  have h11 : a^(-γ) = (2 : ℝ)^(((k + 1 : ℕ) : ℝ) * γ) := by
    simp only [ha_def]
    rw [←Real.rpow_mul (by norm_num)] <;> ring_nf
  rw [h11] at h10
  exact h10

private lemma dyadic_geometric_sum_bound (K : ℕ) (β γ : ℝ) (hγ_lt_beta : γ < β) :
    ∑ k ∈ Finset.range K, (2 : ℝ)^(-(k : ℝ) * (β - γ)) ≤
      1 / (1 - (2 : ℝ)^(-(β - γ))) := by
  let r : ℝ := (2 : ℝ)^(-(β - γ))
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_lt_one : r < 1 := by
    have hgap : 0 < β - γ := sub_pos.mpr hγ_lt_beta
    have hr_eq : r = ((2 : ℝ)^(β - γ))⁻¹ := by
      exact Real.rpow_neg (by norm_num) (β - γ)
    rw [hr_eq]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hgap)
  have hterm (k : ℕ) :
      (2 : ℝ)^(-(k : ℝ) * (β - γ)) = r ^ k := by
    rw [show -(k : ℝ) * (β - γ) = -(β - γ) * (k : ℝ) by ring]
    exact Real.rpow_mul_natCast (by norm_num) (-(β - γ)) k
  calc
    ∑ k ∈ Finset.range K, (2 : ℝ)^(-(k : ℝ) * (β - γ)) =
        ∑ k ∈ Finset.Ico 0 K, r ^ k := by
          simp_rw [hterm]
          rw [← Finset.range_eq_Ico]
    _ ≤ r ^ (0 : ℕ) / (1 - r) := geom_sum_Ico_le_of_lt_one hr_nonneg hr_lt_one
    _ = 1 / (1 - (2 : ℝ)^(-(β - γ))) := by simp [r]

private lemma sum_le_of_shell_bounds
    (K : ℕ) (total small A B N D result : ℝ) (shell term : ℕ → ℝ)
    (hmain : total = small + ∑ k ∈ Finset.range K, shell k)
    (hsmall : small ≤ A)
    (hshell : ∀ k ∈ Finset.range K, shell k ≤ B * term k * N)
    (hterm : ∑ k ∈ Finset.range K, term k ≤ D)
    (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hresult : A + B * N * D = result) :
    total ≤ result := by
  rw [hmain]
  calc
    small + ∑ k ∈ Finset.range K, shell k ≤
        A + ∑ k ∈ Finset.range K, B * term k * N := by
          exact add_le_add hsmall (Finset.sum_le_sum hshell)
    _ = A + B * N * ∑ k ∈ Finset.range K, term k := by
      congr 1
      calc
        ∑ k ∈ Finset.range K, B * term k * N =
            ∑ k ∈ Finset.range K, (B * N) * term k := by
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = B * N * ∑ k ∈ Finset.range K, term k := by rw [Finset.mul_sum]
    _ ≤ A + B * N * D := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hterm (mul_nonneg hB hN))
    _ = result := hresult

private lemma angular_bound_constant_identity (β γ C N : ℝ) :
    2 * C * (Real.sqrt 2)^β * N +
        (2 * C * (Real.sqrt 2)^β * (2 : ℝ)^γ) * N *
          (1 / (1 - (2 : ℝ)^(-(β - γ)))) =
      (2 * (Real.sqrt 2)^β +
          2 * (Real.sqrt 2)^β * (2 : ℝ)^γ /
            (1 - (2 : ℝ)^(-(β - γ)))) * C * N := by
  ring

/--
Angular integral bound for a Frostman set of unit directions.
-/
lemma angular_integral_bound
    {Λ : DiscreteSet 2} {δ C β γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hβ : 0 < β) (hγ : 0 < γ) (hγ_lt_beta : γ < β)
    (hC : 0 ≤ C)
    (hFrost : Λ.IsFrostman δ β (ENNReal.ofReal C))
    (hunit : ∀ θ ∈ Λ, ‖θ‖ = 1)
    (v : Point2) (hv : ‖v‖ = 1) :
    ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) ≤
    (2 * (Real.sqrt 2)^β + 2 * (Real.sqrt 2)^β * (2 : ℝ)^γ / (1 - (2 : ℝ)^(-(β-γ)))) * C * (Λ.card : ℝ) := by
  classical
  set w : Point2 := wz1Perp2 v with hw_def
  set K_const : ℝ := (2 * (Real.sqrt 2)^β + 2 * (Real.sqrt 2)^β * (2 : ℝ)^γ / (1 - (2 : ℝ)^(-(β-γ)))) with hK_def
  set r_geo : ℝ := (2 : ℝ)^(-(β - γ)) with hr_geo_def

  have h_sqrt2_ge_one : 1 ≤ Real.sqrt 2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num

  -- Empty set case
  by_cases h_empty : Λ = ∅
  · rw [h_empty]; simp
  · have hne : Λ.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty

    -- Frostman implies C ≥ 1 when Λ nonempty
    have hC_ge_one : 1 ≤ C := by
      have h1 : Λ.ballCount 0 1 ≤ ENNReal.ofReal C * Kakeya.realRpowENN 1 β * Λ.enncard :=
        hFrost 0 1 (by linarith) (by norm_num)
      have h2 : ∀ x ∈ Λ, dist x 0 ≤ 1 := by
        intro x hx
        have h3 : ‖x‖ = 1 := hunit x hx
        simpa [dist_eq_norm] using h3.le
      have h4 : Λ.filter (fun y => dist y 0 ≤ 1) = Λ := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, _⟩; exact hx
        · intro hx; exact ⟨hx, h2 x hx⟩
      have h5 : Λ.ballCount 0 1 = (Λ.card : ENNReal) := by
        unfold DiscreteSet.ballCount
        rw [h4] <;> simp
      rw [h5] at h1
      have h6 : Kakeya.realRpowENN 1 β = 1 := by simp [Kakeya.realRpowENN]
      rw [h6] at h1
      have h7 : (Λ.card : ENNReal) ≤ ENNReal.ofReal C * (Λ.card : ENNReal) := by
        simpa [DiscreteSet.enncard] using h1
      have h_card_pos : 0 < (Λ.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
      have h8 : (Λ.card : ENNReal) = ENNReal.ofReal ((Λ.card : ℝ)) := by
        simp [DiscreteSet.enncard] <;> norm_cast
      rw [h8] at h7
      have h9 : ENNReal.ofReal C * ENNReal.ofReal ((Λ.card : ℝ)) =
          ENNReal.ofReal (C * (Λ.card : ℝ)) := by
        rw [←ENNReal.ofReal_mul hC] <;> ring
      rw [h9] at h7
      have h_pos : 0 ≤ C * (Λ.card : ℝ) := by positivity
      have h10 : (Λ.card : ℝ) ≤ C * (Λ.card : ℝ) :=
        (ENNReal.ofReal_le_ofReal_iff h_pos).mp h7
      by_contra h11
      have h12 : C < 1 := by linarith
      nlinarith

    -- Frostman real-bound helper
    have hfrost' : ∀ (x : Point2) (r : ℝ), δ ≤ r → r ≤ 1 →
        ((Λ.filter (fun y => dist y x ≤ r)).card : ℝ) ≤ C * r^β * (Λ.card : ℝ) := by
      intro x r hδr hr1
      have h8 : Λ.ballCount x r ≤
          ENNReal.ofReal C * Kakeya.realRpowENN r β * Λ.enncard := hFrost x r hδr hr1
      have h10 : Kakeya.realRpowENN r β = ENNReal.ofReal (r^β) := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h11 : Λ.enncard = (Λ.card : ENNReal) := by simp [DiscreteSet.enncard]
      rw [h10, h11] at h8
      have h_posr : 0 < r := by linarith
      have h_posra : 0 ≤ r^β := by positivity
      have h_nonneg : 0 ≤ C * r^β * (Λ.card : ℝ) := by positivity
      have h121 : ENNReal.ofReal C * ENNReal.ofReal (r^β) = ENNReal.ofReal (C * r^β) := by
        rw [←ENNReal.ofReal_mul hC]
      have h122 : (Λ.card : ENNReal) = ENNReal.ofReal ((Λ.card : ℝ)) := by
        simp [DiscreteSet.enncard] <;> norm_cast
      have h12 : (ENNReal.ofReal C * ENNReal.ofReal (r^β) * (Λ.card : ENNReal)) =
          ENNReal.ofReal (C * r^β * (Λ.card : ℝ)) := by
        rw [h121, h122]
        rw [←ENNReal.ofReal_mul (mul_nonneg hC h_posra)] <;> ring
      rw [h12] at h8
      set B : Finset Point2 := Λ.filter (fun y => dist y x ≤ r) with hB
      have h_posB : 0 ≤ (B.card : ℝ) := by positivity
      have h19 : (B.card : ENNReal) = ENNReal.ofReal ((B.card : ℝ)) := by
        simp [hB] <;> norm_cast
      have h20 : ENNReal.ofReal ((B.card : ℝ)) ≤ ENNReal.ofReal (C * r^β * (Λ.card : ℝ)) := by
        rw [←h19]; exact h8
      have h21 : (B.card : ℝ) ≤ C * r^β * (Λ.card : ℝ) :=
        (ENNReal.ofReal_le_ofReal_iff h_nonneg).mp h20
      simpa [hB] using h21

    -- Count in angular band {|inner θ v| ≤ r} for δ/√2 ≤ r ≤ 1/√2
    have h_count_band : ∀ (r : ℝ), δ / Real.sqrt 2 ≤ r → r ≤ 1 / Real.sqrt 2 →
        ((Λ.filter (fun θ => |inner ℝ θ v| ≤ r)).card : ℝ) ≤
        2 * C * (Real.sqrt 2 * r)^β * (Λ.card : ℝ) := by
      intro r hr_lower hr_upper
      have h_rpos : 0 < r := by
        have h_pos : 0 < δ / Real.sqrt 2 := by positivity
        linarith
      have h_ball1 : Λ.filter (fun θ => |inner ℝ θ v| ≤ r) ⊆
          (Λ.filter (fun θ => dist θ w ≤ Real.sqrt 2 * r)) ∪
          (Λ.filter (fun θ => dist θ (-w) ≤ Real.sqrt 2 * r)) := by
        intro θ hθ
        have hθin : θ ∈ Λ := (Finset.mem_filter.mp hθ).1
        have hle : |inner ℝ θ v| ≤ r := (Finset.mem_filter.mp hθ).2
        have hθunit : ‖θ‖ = 1 := hunit θ hθin
        have hgeom := dist_to_perp_or_neg hθunit hv (by linarith) hle
        rcases hgeom with (h_left | h_right)
        · have h_in : θ ∈ Λ.filter (fun θ => dist θ w ≤ Real.sqrt 2 * r) := by
            simpa [Finset.mem_filter] using ⟨hθin, h_left⟩
          exact Finset.mem_union_left _ h_in
        · have h_in : θ ∈ Λ.filter (fun θ => dist θ (-w) ≤ Real.sqrt 2 * r) := by
            simpa [Finset.mem_filter] using ⟨hθin, h_right⟩
          exact Finset.mem_union_right _ h_in
      have h4 : δ ≤ Real.sqrt 2 * r := by
        have h5 : 0 < Real.sqrt 2 := by positivity
        calc δ = (δ / Real.sqrt 2) * Real.sqrt 2 := by field_simp [h5.ne'] <;> ring
          _ ≤ r * Real.sqrt 2 := by gcongr
          _ = Real.sqrt 2 * r := by ring
      have h5 : Real.sqrt 2 * r ≤ 1 := by
        calc Real.sqrt 2 * r ≤ Real.sqrt 2 * (1 / Real.sqrt 2) := by gcongr
          _ = 1 := by field_simp <;> ring
      have h6 := hfrost' w (Real.sqrt 2 * r) h4 h5
      have h7 := hfrost' (-w) (Real.sqrt 2 * r) h4 h5
      have h_card : (Λ.filter (fun θ => |inner ℝ θ v| ≤ r)).card ≤
          (Λ.filter (fun θ => dist θ w ≤ Real.sqrt 2 * r)).card +
          (Λ.filter (fun θ => dist θ (-w) ≤ Real.sqrt 2 * r)).card := by
        calc _ ≤ ((Λ.filter (fun θ => dist θ w ≤ Real.sqrt 2 * r)) ∪
            (Λ.filter (fun θ => dist θ (-w) ≤ Real.sqrt 2 * r))).card :=
            Finset.card_le_card h_ball1
          _ ≤ _ := Finset.card_union_le _ _
      have h_card' : ((Λ.filter (fun θ => |inner ℝ θ v| ≤ r)).card : ℝ) ≤
          ((Λ.filter (fun θ => dist θ w ≤ Real.sqrt 2 * r)).card : ℝ) +
          ((Λ.filter (fun θ => dist θ (-w) ≤ Real.sqrt 2 * r)).card : ℝ) := by
        exact_mod_cast h_card
      linarith

    -- Small set S = {θ : |inner θ v| ≤ δ}
    let S : Finset Point2 := Λ.filter (fun θ => |inner ℝ θ v| ≤ δ)

    -- Bound |S| with δ^β factor (when δ ≤ 1/√2)
    have hS_card_delta : δ ≤ 1 / Real.sqrt 2 →
        (S.card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * δ^β * (Λ.card : ℝ) := by
      intro h_case
      have hδ2 : δ / Real.sqrt 2 ≤ δ := by
        have hδpos : 0 ≤ δ := hδ.le
        exact div_le_self hδpos h_sqrt2_ge_one
      have h9 : ((Λ.filter (fun θ => |inner ℝ θ v| ≤ δ)).card : ℝ) ≤
          2 * C * (Real.sqrt 2 * δ)^β * (Λ.card : ℝ) := h_count_band δ hδ2 h_case
      have h10 : (Real.sqrt 2 * δ)^β = (Real.sqrt 2)^β * δ^β :=
        Real.mul_rpow (by positivity) (by positivity)
      have h13 : (S.card : ℝ) = ((Λ.filter (fun θ => |inner ℝ θ v| ≤ δ)).card : ℝ) := by
        simp [S]
      rw [h13]
      calc _ ≤ 2 * C * (Real.sqrt 2 * δ)^β * (Λ.card : ℝ) := h9
        _ = 2 * C * (Real.sqrt 2)^β * δ^β * (Λ.card : ℝ) := by rw [h10] <;> ring

    -- Bound |S| (without δ^β factor)
    have hS_card : (S.card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by
      by_cases h_case : δ ≤ 1 / Real.sqrt 2
      · have h11 : δ^β ≤ 1 := Real.rpow_le_one (by linarith) hδ_le_one (le_of_lt hβ)
        have h12 : 0 ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by positivity
        have h13 := hS_card_delta h_case
        nlinarith
      · have h10 : (S.card : ℝ) ≤ (Λ.card : ℝ) := by
          have h : S.card ≤ Λ.card := Finset.card_le_card (Finset.filter_subset _ _)
          exact Nat.cast_le.mpr h
        have h11 : (Λ.card : ℝ) ≤ C * (Λ.card : ℝ) := by
          have h12 : 1 ≤ C := hC_ge_one
          have h13 : 0 ≤ (Λ.card : ℝ) := by positivity
          nlinarith
        have h14 : 1 ≤ (Real.sqrt 2)^β := Real.one_le_rpow h_sqrt2_ge_one (le_of_lt hβ)
        have h15 : C * (Λ.card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by
          have h16 : 0 ≤ (Λ.card : ℝ) := by positivity
          have h17 : 1 ≤ 2 * (Real.sqrt 2)^β := by linarith [h14]
          nlinarith
        linarith

    -- Small set contribution
    have hS_contrib : ∑ θ ∈ S, (max (|inner ℝ θ v|) δ)^(-γ) ≤
        2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by
      have h1 : ∀ θ ∈ S, (max (|inner ℝ θ v|) δ)^(-γ) = δ^(-γ) := by
        intro θ hθ
        have h2 : |inner ℝ θ v| ≤ δ := (Finset.mem_filter.mp hθ).2
        have h3 : max (|inner ℝ θ v|) δ = δ := by rw [max_eq_right] <;> linarith
        rw [h3]
      have h4 : ∑ θ ∈ S, (max (|inner ℝ θ v|) δ)^(-γ) = (S.card : ℝ) * δ^(-γ) := by
        rw [Finset.sum_congr rfl h1]
        simp [mul_comm] <;> ring
      rw [h4]
      by_cases h_case : δ ≤ 1 / Real.sqrt 2
      · -- Use Frostman bound with δ^β factor
        have h5 : δ^(β - γ) ≤ 1 := by
          have h6 : 0 ≤ β - γ := by linarith
          exact Real.rpow_le_one (by linarith) hδ_le_one h6
        have h7 : 0 ≤ (S.card : ℝ) := by positivity
        have h8 : (S.card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * δ^β * (Λ.card : ℝ) :=
          hS_card_delta h_case
        have h9 : δ^(-γ) = δ^(β - γ) * δ^(-β) := by
          rw [←Real.rpow_add (by linarith)] <;> ring_nf
        have h10 : 0 ≤ δ^(-β) := by positivity
        calc
          (S.card : ℝ) * δ^(-γ)
            = (S.card : ℝ) * (δ^(β - γ) * δ^(-β)) := by rw [h9]
          _ ≤ (2 * C * (Real.sqrt 2)^β * δ^β * (Λ.card : ℝ)) * (δ^(β - γ) * δ^(-β)) := by
            gcongr
          _ = 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) * δ^(β - γ) := by
            have h12 : δ^β * δ^(-β) = 1 := by
              have h_pos : 0 < δ := hδ
              have h : δ^β * δ^(-β) = δ^(β + (-β)) := by
                rw [←Real.rpow_add (by linarith)] <;> ring
              rw [h]
              have h2 : β + (-β) = 0 := by ring
              rw [h2]
              simp
            have h11 : δ^β * (δ^(β - γ) * δ^(-β)) = δ^(β - γ) := by
              calc δ^β * (δ^(β - γ) * δ^(-β))
                = δ^(β - γ) * (δ^β * δ^(-β)) := by ring
              _ = δ^(β - γ) * 1 := by rw [h12]
              _ = δ^(β - γ) := by ring
            have h_full : (2 * C * (Real.sqrt 2)^β * δ^β * (Λ.card : ℝ)) * (δ^(β - γ) * δ^(-β)) =
                2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) * δ^(β - γ) := by
              calc (2 * C * (Real.sqrt 2)^β * δ^β * (Λ.card : ℝ)) * (δ^(β - γ) * δ^(-β))
                = 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) * (δ^β * (δ^(β - γ) * δ^(-β))) := by ring
              _ = 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) * δ^(β - γ) := by rw [h11]
            exact h_full
          _ ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by
            have h12 : 0 ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by positivity
            nlinarith [h5]
      · -- δ > 1/√2: use |S| ≤ |Λ| and δ^(-γ) ≤ 2^(γ/2) ≤ 2·√2^β
        have hδ_gt : 1 / Real.sqrt 2 < δ := by linarith
        have h10 : (S.card : ℝ) ≤ (Λ.card : ℝ) := by
          have h : S.card ≤ Λ.card := Finset.card_le_card (Finset.filter_subset _ _)
          exact Nat.cast_le.mpr h
        have h_sqrt2_rpow : (Real.sqrt 2)^γ = (2 : ℝ)^(γ / 2) := by
          rw [Real.sqrt_eq_rpow, ←Real.rpow_mul (by norm_num)] <;> ring_nf
        have h11 : δ^(-γ) ≤ (Real.sqrt 2)^γ := by
          have h12 : 1 / Real.sqrt 2 < δ := hδ_gt
          have h13 : 0 < γ := hγ
          have h14 : (1 / Real.sqrt 2)^γ < δ^γ := Real.rpow_lt_rpow (by positivity) h12 h13
          have h15 : δ^(-γ) = 1 / δ^γ := by
            rw [Real.rpow_neg (by positivity)] <;> field_simp
          have h17 : (1 / Real.sqrt 2)^γ * (Real.sqrt 2)^γ = 1 := by
            rw [←Real.mul_rpow (by positivity) (by positivity)]
            have h18 : (1 / Real.sqrt 2) * Real.sqrt 2 = 1 := by field_simp <;> ring
            rw [h18] <;> simp
          have h16 : (Real.sqrt 2)^γ = 1 / (1 / Real.sqrt 2)^γ := by
            have h_ne : (1 / Real.sqrt 2)^γ ≠ 0 := by positivity
            have h : (1 / Real.sqrt 2)^γ * (Real.sqrt 2)^γ = (1 / Real.sqrt 2)^γ * (1 / (1 / Real.sqrt 2)^γ) := by
              rw [h17]
              have h2 : (1 / Real.sqrt 2)^γ * (1 / (1 / Real.sqrt 2)^γ) = 1 := by
                field_simp [h_ne] <;> ring
              rw [h2]
            exact (mul_right_inj' h_ne).mp h
          rw [h15, h16]
          apply one_div_le_one_div_of_le
          · positivity
          · exact h14.le
        have h16 : (Real.sqrt 2)^γ ≤ 2 * (Real.sqrt 2)^β := by
          have h17 : γ < β := hγ_lt_beta
          have h18 : (Real.sqrt 2)^γ ≤ (Real.sqrt 2)^β := by
            have h19 : 1 ≤ Real.sqrt 2 := h_sqrt2_ge_one
            gcongr
            <;> linarith
          have h19 : 0 ≤ (Real.sqrt 2)^β := by positivity
          linarith
        have h20 : (S.card : ℝ) * δ^(-γ) ≤ (Λ.card : ℝ) * (2 * (Real.sqrt 2)^β) := by
          have h21 : 0 ≤ δ^(-γ) := by positivity
          calc (S.card : ℝ) * δ^(-γ)
              ≤ (S.card : ℝ) * (Real.sqrt 2)^γ := by gcongr
            _ ≤ (Λ.card : ℝ) * (Real.sqrt 2)^γ := by gcongr
            _ ≤ (Λ.card : ℝ) * (2 * (Real.sqrt 2)^β) := by gcongr
        have h22 : (Λ.card : ℝ) * (2 * (Real.sqrt 2)^β) ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by
          have h23 : 1 ≤ C := hC_ge_one
          have h24 : 0 ≤ (Λ.card : ℝ) := by positivity
          nlinarith
        linarith

    -- Dyadic shells
    let shell (k : ℕ) : Finset Point2 :=
      Λ.filter (fun θ => (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < |inner ℝ θ v| ∧ |inner ℝ θ v| ≤ (2 : ℝ)^(-(k : ℝ)))
    let shell' (k : ℕ) : Finset Point2 := shell k \ S

    -- Find K such that 2^K > 1/δ
    obtain ⟨K, hK_gt⟩ := exists_nat_gt (1 / δ)
    have h_nat_le : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ)^n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have h4 : (1 : ℝ) ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
        calc (n.succ : ℝ) = (n : ℝ) + 1 := by simp
          _ ≤ (2 : ℝ)^n + 1 := by linarith
          _ ≤ (2 : ℝ)^n + (2 : ℝ)^n := by linarith [h4]
          _ = (2 : ℝ)^(n + 1) := by rw [pow_succ] <;> ring
    have hK2 : (2 : ℝ)^(K : ℝ) > 1 / δ := by
      have h7 : (K : ℝ) ≤ (2 : ℝ)^K := h_nat_le K
      have h8 : (2 : ℝ)^K = (2 : ℝ)^(K : ℝ) := by norm_cast
      have h9 : (K : ℝ) > 1 / δ := hK_gt
      linarith [h7, h8, h9]
    have hK3 : (2 : ℝ)^(-(K : ℝ)) < δ := by
      have h4 : (2 : ℝ)^(-(K : ℝ)) = 1 / (2 : ℝ)^(K : ℝ) := by
        rw [Real.rpow_neg (by norm_num)] <;> field_simp
      rw [h4]
      have h5 : 0 < (2 : ℝ)^(K : ℝ) := by positivity
      have h6 : 1 < δ * (2 : ℝ)^(K : ℝ) := by
        have h7 : 0 < δ := hδ
        calc 1 = δ * (1 / δ) := by field_simp [h7.ne'] <;> ring
          _ < δ * (2 : ℝ)^(K : ℝ) := by exact mul_lt_mul_of_pos_left hK2 h7
      have h8 : 1 / (2 : ℝ)^(K : ℝ) < δ := by
        calc 1 / (2 : ℝ)^(K : ℝ)
            < (δ * (2 : ℝ)^(K : ℝ)) / (2 : ℝ)^(K : ℝ) := by gcongr
          _ = δ := by field_simp [h5.ne'] <;> ring
      exact h8
    have hK_pos : 0 < K := by
      by_contra h
      have h' : K = 0 := by omega
      have h9 : (2 : ℝ)^(K : ℝ) > 1 / δ := hK2
      rw [h'] at h9
      have h10 : (1 : ℝ) > 1 / δ := by simpa using h9
      have h11 : 1 / δ < 1 := by linarith
      have h12 : δ > 1 := by
        have h13 : 0 < δ := hδ
        calc 1 = δ * (1 / δ) := by field_simp [h13.ne'] <;> ring
          _ < δ * 1 := by gcongr
          _ = δ := by ring
      linarith [hδ_le_one]

    -- Existence of shell index for t ∈ (2^(-K), 1]
    have h_exists_shell : ∀ (t : ℝ), (2 : ℝ)^(-(K : ℝ)) < t → t ≤ 1 →
        ∃ k ∈ Finset.range K, (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < t ∧ t ≤ (2 : ℝ)^(-(k : ℝ)) := by
      intro t ht_lower ht_upper
      let P : ℕ → Prop := fun n => (2 : ℝ)^(-(n + 1 : ℕ) : ℝ) < t
      have hP_K1 : P (K - 1) := by
        have hK1 : 0 < K := hK_pos
        have h_cast : (( (K - 1 : ℕ) : ℝ) + 1) = (K : ℝ) := by
          simp [Nat.cast_add, hK1] <;> omega
        have h_goal : (2 : ℝ)^(-(( (K - 1 : ℕ) : ℝ) + 1)) < t := by
          rw [h_cast]
          exact ht_lower
        simpa [P] using h_goal
      have hP_nonempty : ∃ n, P n := ⟨K - 1, hP_K1⟩
      let k := Nat.find hP_nonempty
      have hk1 : P k := Nat.find_spec hP_nonempty
      have hk2 : ∀ n < k, ¬P n := fun n hn => Nat.find_min hP_nonempty hn
      have hk_lt_K : k < K := by
        have h5 : k ≤ K - 1 := Nat.find_min' hP_nonempty hP_K1
        omega
      have hk_upper : t ≤ (2 : ℝ)^(-(k : ℝ)) := by
        by_cases h_k0 : k = 0
        · have h_k_eq : k = 0 := h_k0
          rw [h_k_eq]
          simpa using ht_upper
        · have hk_pos : 0 < k := Nat.pos_of_ne_zero h_k0
          have h4 : ¬P (k - 1) := hk2 (k - 1) (by omega)
          have h5 : (( (k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
            simp [Nat.cast_add, hk_pos] <;> omega
          have h6 : ¬((2 : ℝ)^(-(( (k - 1 : ℕ) : ℝ) + 1)) < t) := by
            simpa [P] using h4
          rw [h5] at h6
          exact le_of_not_gt h6
      exact ⟨k, Finset.mem_range.mpr hk_lt_K, hk1, hk_upper⟩

    -- Shell count bound for k ∈ range K, assuming δ ≤ 2^(-k)
    have h_shell_count : ∀ k ∈ Finset.range K, δ ≤ (2 : ℝ)^(-(k : ℝ)) →
        (shell k).card ≤ 2 * C * (Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β) * (Λ.card : ℝ) := by
      intro k hk hδ_le2k
      by_cases h_k0 : k = 0
      · subst h_k0
        have h_sub : shell 0 ⊆ Λ := Finset.filter_subset _ _
        have h_card : (shell 0).card ≤ Λ.card := Finset.card_le_card h_sub
        have h9 : (2 : ℝ)^(-(0 : ℝ) * β) = 1 := by simp
        have h_goal : (shell 0).card ≤ 2 * C * (Real.sqrt 2)^β * (2 : ℝ)^(-(0 : ℝ) * β) * (Λ.card : ℝ) := by
          rw [h9]
          have h10 : 1 ≤ (Real.sqrt 2)^β := Real.one_le_rpow h_sqrt2_ge_one (le_of_lt hβ)
          have h11 : 1 ≤ C := hC_ge_one
          have h12 : 0 ≤ (Λ.card : ℝ) := by positivity
          have h13 : ((shell 0).card : ℝ) ≤ (Λ.card : ℝ) := by exact_mod_cast h_card
          have h14 : (Λ.card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by
            have h15 : 1 ≤ 2 * C * (Real.sqrt 2)^β := by
              have h16 : 0 < C := by linarith
              nlinarith [h10, h11]
            nlinarith
          have h17 : ((shell 0).card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by linarith
          have h18 : ((shell 0).card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * 1 * (Λ.card : ℝ) := by
            have h19 : 2 * C * (Real.sqrt 2)^β * 1 * (Λ.card : ℝ) = 2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ) := by ring
            rw [h19]
            exact h17
          exact_mod_cast h18
        simpa using h_goal
      · have h_kpos : 0 < k := Nat.pos_of_ne_zero h_k0
        have h_r_upper : (2 : ℝ)^(-(k : ℝ)) ≤ 1 / Real.sqrt 2 := by
          have h1 : (k : ℝ) ≥ 1 := by exact_mod_cast h_kpos
          have h2 : (2 : ℝ)^(-(k : ℝ)) ≤ (2 : ℝ)^(-1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le
            <;> norm_num <;> linarith
          have h3 : (2 : ℝ)^(-1 : ℝ) = 1 / 2 := by norm_num
          rw [h3] at h2
          have h4 : 1 / 2 ≤ 1 / Real.sqrt 2 := by
            have h5 : Real.sqrt 2 ≤ 2 := by
              have h : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
              nlinarith [Real.sqrt_nonneg 2]
            have h6 : 0 < Real.sqrt 2 := by positivity
            exact one_div_le_one_div_of_le (by positivity) h5
          linarith
        have h_r_lower : δ / Real.sqrt 2 ≤ (2 : ℝ)^(-(k : ℝ)) := by
          have h4 : δ / Real.sqrt 2 ≤ δ := by
            exact div_le_self (by linarith) h_sqrt2_ge_one
          linarith [hδ_le2k]
        have h9 := h_count_band ((2 : ℝ)^(-(k : ℝ))) h_r_lower h_r_upper
        have h10 : shell k ⊆ Λ.filter (fun θ => |inner ℝ θ v| ≤ (2 : ℝ)^(-(k : ℝ))) := by
          intro θ hθ
          have h11 := (Finset.mem_filter.mp hθ).2
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hθ).1, h11.2⟩
        have h11 : (shell k).card ≤ (Λ.filter (fun θ => |inner ℝ θ v| ≤ (2 : ℝ)^(-(k : ℝ)))).card :=
          Finset.card_le_card h10
        have h12 : ((shell k).card : ℝ) ≤ 2 * C * (Real.sqrt 2 * (2 : ℝ)^(-(k : ℝ)))^β * (Λ.card : ℝ) := by
          calc ((shell k).card : ℝ) ≤ _ := by exact Nat.cast_le.mpr h11
            _ ≤ 2 * C * (Real.sqrt 2 * (2 : ℝ)^(-(k : ℝ)))^β * (Λ.card : ℝ) := h9
        have h13 : (Real.sqrt 2 * (2 : ℝ)^(-(k : ℝ)))^β =
            (Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          <;> rw [←Real.rpow_mul (by positivity)] <;> ring
        rw [h13] at h12
        have h14 : ((shell k).card : ℝ) ≤ 2 * C * (Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β) * (Λ.card : ℝ) := by
          have h15 : 2 * C * ((Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β)) * (Λ.card : ℝ) =
              2 * C * (Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β) * (Λ.card : ℝ) := by ring
          rw [h15] at h12
          exact h12
        exact_mod_cast h14

    -- Shells are disjoint
    have h_shell_disj : ∀ k1 ∈ Finset.range K, ∀ k2 ∈ Finset.range K, k1 ≠ k2 →
        Disjoint (shell k1) (shell k2) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro θ h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      by_cases h : k1 < k2
      · have h5 : (2 : ℝ)^(-(k2 : ℝ)) ≤ (2 : ℝ)^(-(k1 + 1 : ℕ) : ℝ) := by
          have h6 : (k1 + 1 : ℕ) ≤ k2 := by omega
          have h7 : -((k1 + 1 : ℕ) : ℝ) ≥ -(k2 : ℝ) := by exact_mod_cast (by omega)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h7
        have h8 : (2 : ℝ)^(-(k2 : ℝ)) < |inner ℝ θ v| := by
          calc (2 : ℝ)^(-(k2 : ℝ)) ≤ (2 : ℝ)^(-(k1 + 1 : ℕ) : ℝ) := h5
            _ < |inner ℝ θ v| := h1'.1
        have h9 : |inner ℝ θ v| ≤ (2 : ℝ)^(-(k2 : ℝ)) := h2'.2
        linarith
      · have h6 : k2 < k1 := by omega
        have h7 : (2 : ℝ)^(-(k1 : ℝ)) ≤ (2 : ℝ)^(-(k2 + 1 : ℕ) : ℝ) := by
          have h8 : (k2 + 1 : ℕ) ≤ k1 := by omega
          have h9 : -((k2 + 1 : ℕ) : ℝ) ≥ -(k1 : ℝ) := by exact_mod_cast (by omega)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h9
        have h10 : (2 : ℝ)^(-(k1 : ℝ)) < |inner ℝ θ v| := by
          calc (2 : ℝ)^(-(k1 : ℝ)) ≤ (2 : ℝ)^(-(k2 + 1 : ℕ) : ℝ) := h7
            _ < |inner ℝ θ v| := h2'.1
        have h11 : |inner ℝ θ v| ≤ (2 : ℝ)^(-(k1 : ℝ)) := h1'.2
        linarith

    -- shell' are disjoint
    have h_shell'_disj : ∀ k1 ∈ Finset.range K, ∀ k2 ∈ Finset.range K, k1 ≠ k2 →
        Disjoint (shell' k1) (shell' k2) := by
      intro k1 hk1 k2 hk2 hne
      have h1 : shell' k1 ⊆ shell k1 := Finset.sdiff_subset
      have h2 : shell' k2 ⊆ shell k2 := Finset.sdiff_subset
      exact (h_shell_disj k1 hk1 k2 hk2 hne).mono h1 h2

    -- Partition: Λ \ S = biUnion of shell' k
    have h_partition : Λ \ S = Finset.biUnion (Finset.range K) shell' := by
      ext θ
      simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨hθΛ, hnotinS⟩
        have h_t_gt : δ < |inner ℝ θ v| := by
          by_contra h
          have h' : |inner ℝ θ v| ≤ δ := by linarith
          have h_inS : θ ∈ S := Finset.mem_filter.mpr ⟨hθΛ, h'⟩
          exact hnotinS h_inS
        have h_t_le_one : |inner ℝ θ v| ≤ 1 := by
          calc |inner ℝ θ v| ≤ ‖θ‖ * ‖v‖ := abs_real_inner_le_norm θ v
            _ = 1 := by rw [hunit θ hθΛ, hv] <;> ring
        have h_t_gt_K : (2 : ℝ)^(-(K : ℝ)) < |inner ℝ θ v| := by linarith
        obtain ⟨k, hkK, hk1, hk2⟩ := h_exists_shell (|inner ℝ θ v|) h_t_gt_K h_t_le_one
        have hkK' : k < K := Finset.mem_range.mp hkK
        have hθin_shell : θ ∈ shell k := Finset.mem_filter.mpr ⟨hθΛ, ⟨hk1, hk2⟩⟩
        exact ⟨k, hkK', Finset.mem_sdiff.mpr ⟨hθin_shell, hnotinS⟩⟩
      · rintro ⟨k, _, hθin⟩
        have h1 : θ ∈ shell k := (Finset.mem_sdiff.mp hθin).1
        have h2 : θ ∉ S := (Finset.mem_sdiff.mp hθin).2
        have h3 : θ ∈ Λ := (Finset.mem_filter.mp h1).1
        exact ⟨h3, h2⟩

    -- Shell' contribution bound
    have h_shell'_contrib : ∀ k ∈ Finset.range K,
        ∑ θ ∈ shell' k, (max (|inner ℝ θ v|) δ)^(-γ) ≤
        2 * C * (Real.sqrt 2)^β * (2 : ℝ)^γ * (2 : ℝ)^(-(k : ℝ) * (β - γ)) * (Λ.card : ℝ) := by
      intro k hk
      by_cases h_empty : shell' k = ∅
      · rw [h_empty]
        simp only [Finset.sum_empty]
        <;> positivity
      · have h_nonempty : (shell' k).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
        obtain ⟨θ, hθ⟩ := h_nonempty
        have h2 : θ ∈ shell k := (Finset.mem_sdiff.mp hθ).1
        have h3 : θ ∉ S := (Finset.mem_sdiff.mp hθ).2
        have hθinΛ : θ ∈ Λ := (Finset.mem_filter.mp h2).1
        have h5 : δ < |inner ℝ θ v| := by
          by_contra h
          have h' : |inner ℝ θ v| ≤ δ := by linarith
          have h_inS : θ ∈ S := Finset.mem_filter.mpr ⟨hθinΛ, h'⟩
          exact h3 h_inS
        have h6 : |inner ℝ θ v| ≤ (2 : ℝ)^(-(k : ℝ)) := (Finset.mem_filter.mp h2).2.2
        have hδ_le2k : δ ≤ (2 : ℝ)^(-(k : ℝ)) := by linarith
        have h_count := h_shell_count k hk hδ_le2k
        let bval : ℝ := (2 : ℝ)^(((k + 1 : ℕ) : ℝ) * γ)
        have h1 : ∀ (φ : Point2), φ ∈ shell' k → (max (|inner ℝ φ v|) δ)^(-γ) ≤ bval := by
          intro φ hφ
          have h2 : φ ∈ shell k := (Finset.mem_sdiff.mp hφ).1
          have h3 : φ ∉ S := (Finset.mem_sdiff.mp hφ).2
          have h2in : φ ∈ Λ := (Finset.mem_filter.mp h2).1
          have h2cond := (Finset.mem_filter.mp h2).2
          have h4 : (2 : ℝ)^(-(k + 1 : ℕ) : ℝ) < |inner ℝ φ v| := h2cond.1
          have h5 : δ < |inner ℝ φ v| := by
            have hS_iff : φ ∈ S ↔ |inner ℝ φ v| ≤ δ := by
              simp [S, Finset.mem_filter, h2in] <;> tauto
            have h_not : ¬(|inner ℝ φ v| ≤ δ) := by
              intro hle; exact h3 (hS_iff.mpr hle)
            exact not_le.mp h_not
          have h7 : 0 < |inner ℝ φ v| := lt_trans hδ h5
          exact regularized_bound k δ γ (|inner ℝ φ v|) hδ hγ h7 h4 h5.le
        have h21 : ∑ θ ∈ shell' k, (max (|inner ℝ θ v|) δ)^(-γ) ≤
            ∑ θ ∈ shell' k, bval :=
          Finset.sum_le_sum (fun θ hθ => h1 θ hθ)
        have h22 : ∑ θ ∈ shell' k, bval =
            (shell' k).card * bval := by
          simp [mul_comm] <;> ring
        have h23 : ∑ θ ∈ shell' k, (max (|inner ℝ θ v|) δ)^(-γ) ≤
            (shell' k).card * bval := by
          calc _ ≤ _ := h21
             _ = _ := h22
        have h3 : (shell' k).card ≤ (shell k).card := Finset.card_le_card Finset.sdiff_subset
        have h_bval_eq : bval = (2 : ℝ)^(((k + 1 : ℕ) : ℝ) * γ) := by rfl
        calc
          _ ≤ (shell' k).card * bval := h23
          _ ≤ (shell k).card * bval := by gcongr
          _ ≤ (2 * C * (Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β) * (Λ.card : ℝ)) * bval := by gcongr <;> linarith
          _ = 2 * C * (Real.sqrt 2)^β * (2 : ℝ)^γ * (2 : ℝ)^(-(k : ℝ) * (β - γ)) * (Λ.card : ℝ) := by
            have h_bval_expand : bval = (2 : ℝ)^(γ + (k : ℝ) * γ) := by
              simp only [bval]
              have h6 : ((k + 1 : ℕ) : ℝ) * γ = γ + (k : ℝ) * γ := by simp [Nat.cast_add] <;> ring
              rw [h6]
            rw [h_bval_expand]
            have h_rearrange : (2 * C * (Real.sqrt 2)^β * (2 : ℝ)^(-(k : ℝ) * β) * (Λ.card : ℝ)) * (2 : ℝ)^(γ + (k : ℝ) * γ) =
                (2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ)) * ((2 : ℝ)^(-(k : ℝ) * β) * (2 : ℝ)^(γ + (k : ℝ) * γ)) := by ring
            rw [h_rearrange]
            have h7 : (2 : ℝ)^(-(k : ℝ) * β) * (2 : ℝ)^(γ + (k : ℝ) * γ) =
                (2 : ℝ)^γ * (2 : ℝ)^(-(k : ℝ) * (β - γ)) := by
              have h8 : -(k : ℝ) * β + (γ + (k : ℝ) * γ) = γ + (-(k : ℝ) * (β - γ)) := by ring
              rw [←Real.rpow_add (by norm_num), h8]
              have h9 : γ + (-(k : ℝ) * (β - γ)) = γ + (k : ℝ) * (γ - β) := by ring
              rw [h9]
              rw [←Real.rpow_add (by norm_num)] <;> ring_nf
            rw [h7] <;> ring

    -- Main decomposition
    have h_main : ∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ) =
        (∑ θ ∈ S, (max (|inner ℝ θ v|) δ)^(-γ)) +
        ∑ k ∈ Finset.range K, ∑ θ ∈ shell' k, (max (|inner ℝ θ v|) δ)^(-γ) := by
      have h1 : S ∪ (Λ \ S) = Λ := by
        have h2 : (Λ \ S) ∪ S = Λ := Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
        rw [Finset.union_comm] at h2
        exact h2
      have h1' : Λ = S ∪ (Λ \ S) := h1.symm
      have h_disj' : Disjoint S (Λ \ S) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx2).2 hx1
      rw [h1', Finset.sum_union h_disj']
      rw [h_partition, Finset.sum_biUnion h_shell'_disj]

    -- Final calculation
    have h_sum_rpow : ∑ k ∈ Finset.range K, (2 : ℝ)^(-(k : ℝ) * (β - γ)) ≤ 1 / (1 - r_geo) := by
      simpa only [r_geo] using dyadic_geometric_sum_bound K β γ hγ_lt_beta
    apply sum_le_of_shell_bounds K
      (∑ θ ∈ Λ, (max (|inner ℝ θ v|) δ)^(-γ))
      (∑ θ ∈ S, (max (|inner ℝ θ v|) δ)^(-γ))
      (2 * C * (Real.sqrt 2)^β * (Λ.card : ℝ))
      (2 * C * (Real.sqrt 2)^β * (2 : ℝ)^γ)
      (Λ.card : ℝ)
      (1 / (1 - r_geo))
      (K_const * C * (Λ.card : ℝ))
      (fun k => ∑ θ ∈ shell' k, (max (|inner ℝ θ v|) δ)^(-γ))
      (fun k => (2 : ℝ)^(-(k : ℝ) * (β - γ)))
    · exact h_main
    · exact hS_contrib
    · exact h_shell'_contrib
    · exact h_sum_rpow
    · positivity
    · positivity
    · simpa only [r_geo, K_const] using
        angular_bound_constant_identity β γ C (Λ.card : ℝ)

end Kakeya.Assouad
