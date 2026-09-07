import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44BadPairStatements
import Mathlib.Algebra.Order.Chebyshev

/-!
# WZ1 Lemma 44: heavy line packing estimate

Proof route:
1. **Geometric multiplicity bound** (`at_most_5_thickenings`): for fixed
   `p ∈ G₂`, at most 5 selected lines have `p` in their `r`-thickening.
   Unit normals are oriented so their cross product with `u = (p-base)/‖p-base‖`
   is positive; their inner products with `u` lie in `[-2r,2r]` and are pairwise
   separated by `5r/6`, so at most 5 fit in the interval.
2. **Combinatorial double counting** (`heavy_line_packing_from_multiplicity`):
   incidence sum and sum of squares bounded by `20·N²`; Cauchy–Schwarz plus
   heaviness gives `L ≤ 20/(K²·r^{1/2})`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-! ### Geometric packing helpers -/

/-- Span of a spaced real finset: max - min ≥ d * (card - 1). -/
lemma finset_span_of_spaced {s : Finset ℝ} {d : ℝ} (hd : 0 < d)
    (h_dist : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ |x - y|)
    (hne : s.Nonempty) :
    s.max' hne - s.min' hne ≥ d * (s.card - 1 : ℝ) := by
  classical
  have h_main : ∀ (t : Finset ℝ),
      (∀ x ∈ t, ∀ y ∈ t, x ≠ y → d ≤ |x - y|) →
      ∀ (hne' : t.Nonempty), t.max' hne' - t.min' hne' ≥ d * (t.card - 1 : ℝ) := by
    intro t
    induction t using Finset.strongInduction with
    | H t ih =>
      intro h_dist hne
      by_cases h1 : t.card ≤ 1
      · have h_card_pos : 0 < t.card := Finset.Nonempty.card_pos hne
        have h_card1 : t.card = 1 := by omega
        have h_singleton : ∃ (x : ℝ), t = {x} := Finset.card_eq_one.mp h_card1
        rcases h_singleton with ⟨x, rfl⟩
        simp [Nat.cast] <;> norm_num
      · have h2 : 2 ≤ t.card := by omega
        let x := t.min' hne
        have hx_mem : x ∈ t := Finset.min'_mem t hne
        let t' := t.erase x
        have hss : t' ⊂ t := Finset.erase_ssubset hx_mem
        have h_card' : t'.card = t.card - 1 := by
          simp [t', Finset.card_erase_of_mem hx_mem] <;> omega
        have hne' : t'.Nonempty := by
          have h_pos : 0 < t'.card := by rw [h_card']; omega
          exact Finset.card_pos.mp h_pos
        let y := t'.min' hne'
        have hy_mem_t : y ∈ t := Finset.mem_of_mem_erase (Finset.min'_mem t' hne')
        have hxy_ne : x ≠ y := by
          intro h_eq
          have h' : y ∈ t' := Finset.min'_mem t' hne'
          have h'' : x ∈ t' := by exact h_eq.symm ▸ h'
          have h_contra : x ∉ t' := by simp [t', hx_mem]
          exact h_contra h''
        have hxy_le : x ≤ y := Finset.min'_le t y hy_mem_t
        have hxy_lt : x < y := lt_of_le_of_ne hxy_le hxy_ne
        have h_dist_xy : d ≤ y - x := by
          have h : d ≤ |x - y| := h_dist x hx_mem y hy_mem_t hxy_ne
          have h_neg : x - y < 0 := by linarith
          have h_abs : |x - y| = y - x := by
            rw [abs_of_neg h_neg] <;> linarith
          rw [h_abs] at h
          exact h
        have h_ih := ih t' hss
          (fun a ha b hb => h_dist a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)) hne'
        have h_max_in_t' : t.max' hne ∈ t' := by
          have h_ne_max : t.max' hne ≠ x := by
            intro h_eq
            have h_all : ∀ z ∈ t, z = x := by
              intro z hz
              have hle1 : x ≤ z := Finset.min'_le t z hz
              have hle2 : z ≤ t.max' hne := Finset.le_max' t z hz
              rw [h_eq] at hle2
              exact le_antisymm hle2 hle1
            have h_card1 : t.card = 1 := by
              have h : t = {x} := by
                ext z; simp only [Finset.mem_singleton]
                constructor
                · exact h_all z
                · intro hz; rw [hz]; exact hx_mem
              rw [h]; simp
            have h_contra : 2 ≤ t.card := h2
            rw [h_card1] at h_contra
            contradiction
          exact Finset.mem_erase.mpr ⟨h_ne_max, Finset.max'_mem t hne⟩
        have h_max_le : t'.max' hne' ≤ t.max' hne := Finset.le_max' t (t'.max' hne') (Finset.mem_of_mem_erase (Finset.max'_mem t' hne'))
        have h_max_ge : t.max' hne ≤ t'.max' hne' := Finset.le_max' t' (t.max' hne) h_max_in_t'
        have h_max_eq : t'.max' hne' = t.max' hne := by linarith
        have h_card_nat : t'.card = t.card - 1 := by
          rw [Finset.card_erase_of_mem hx_mem] <;> omega
        have h_card : (t'.card : ℝ) = (t.card : ℝ) - 1 := by
          rw [h_card_nat]
          rw [Nat.cast_sub (show 1 ≤ t.card by omega)]
          <;> norm_cast
        have h_y_eq : t'.min' hne' = y := rfl
        rw [h_max_eq, h_y_eq, h_card] at h_ih
        have h_ih2 : t.max' hne - y ≥ d * ((t.card : ℝ) - 2) := by
          have h_eq : (t.card : ℝ) - 1 - 1 = (t.card : ℝ) - 2 := by ring
          rw [h_eq] at h_ih
          exact h_ih
        have h_final : t.max' hne - x ≥ d * ((t.card : ℝ) - 1) := by
          calc t.max' hne - x
            = (t.max' hne - y) + (y - x) := by ring
          _ ≥ d * ((t.card : ℝ) - 2) + d := by
            exact add_le_add h_ih2 h_dist_xy
          _ = d * ((t.card : ℝ) - 1) := by ring
        exact h_final
  exact h_main s h_dist hne

/-- Packing: at most 5 points in [-W/2,W/2] with pairwise distance ≥ d when 5d > W. -/
lemma real_packing_5 {s : Finset ℝ} {W d : ℝ} (hW : 0 < W) (hd : 0 < d)
    (hfive : 5 * d > W)
    (h1 : ∀ x ∈ s, -W / 2 ≤ x ∧ x ≤ W / 2)
    (h2 : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ |x - y|) :
    s.card ≤ 5 := by
  by_contra h
  have h6 : 6 ≤ s.card := by omega
  have hne : s.Nonempty := by
    have h_pos : 0 < s.card := by omega
    exact Finset.card_pos.mp h_pos
  have h_span := finset_span_of_spaced hd h2 hne
  have h_min_bound : -W / 2 ≤ s.min' hne := (h1 (s.min' hne) (Finset.min'_mem s hne)).1
  have h_max_bound : s.max' hne ≤ W / 2 := (h1 (s.max' hne) (Finset.max'_mem s hne)).2
  have h_span' : s.max' hne - s.min' hne ≤ W := by linarith
  have h10 : (s.card : ℝ) - 1 ≥ 5 := by
    have h11 : (s.card : ℝ) ≥ 6 := by exact_mod_cast h6
    linarith
  have h9 : d * ((s.card : ℝ) - 1) ≥ 5 * d := by
    calc d * ((s.card : ℝ) - 1) ≥ d * 5 := by gcongr
      _ = 5 * d := by ring
  have h_contra : 5 * d ≤ W := by
    calc 5 * d ≤ d * ((s.card : ℝ) - 1) := h9
      _ ≤ s.max' hne - s.min' hne := h_span
      _ ≤ W := h_span'
  linarith [hfive]

/-- Algebraic separation bound: if a1^2+b1^2=1, a2^2+b2^2=1, a1,a2>0,
|b1|,|b2| ≤ 2r, r ≤ 1/4, and (b1-b2)^2+(a1-a2)^2 ≥ r^2, then |b1-b2| ≥ 5r/6. -/
lemma algebraic_separation_bound {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {a1 b1 a2 b2 : ℝ} (ha1_pos : 0 < a1) (ha2_pos : 0 < a2)
    (hab1 : a1 ^ 2 + b1 ^ 2 = 1) (hab2 : a2 ^ 2 + b2 ^ 2 = 1)
    (hb1_bound : |b1| ≤ 2 * r) (hb2_bound : |b2| ≤ 2 * r)
    (h_norm2 : (b1 - b2) ^ 2 + (a1 - a2) ^ 2 ≥ r ^ 2) :
    (5 / 6 : ℝ) * r ≤ |b1 - b2| := by
  have hb1_sq : b1 ^ 2 ≤ 1 / 4 := by
    have h : b1 ^ 2 ≤ (2 * r) ^ 2 := (sq_le_sq).mpr (by simpa [abs_of_pos hr] using hb1_bound)
    have h' : (2 * r) ^ 2 ≤ 1 / 4 := by
      have h'' : 0 ≤ 2 * r := by positivity
      have h''' : 2 * r ≤ 1 / 2 := by linarith
      nlinarith
    linarith
  have hb2_sq : b2 ^ 2 ≤ 1 / 4 := by
    have h : b2 ^ 2 ≤ (2 * r) ^ 2 := (sq_le_sq).mpr (by simpa [abs_of_pos hr] using hb2_bound)
    have h' : (2 * r) ^ 2 ≤ 1 / 4 := by
      have h'' : 0 ≤ 2 * r := by positivity
      have h''' : 2 * r ≤ 1 / 2 := by linarith
      nlinarith
    linarith
  have h_main_ineq : 3 * (a1 - a2) ^ 2 ≤ (b1 - b2) ^ 2 := by
    have ha1_2 : a1 ^ 2 ≥ 3 / 4 := by linarith [hab1, hb1_sq]
    have ha2_2 : a2 ^ 2 ≥ 3 / 4 := by linarith [hab2, hb2_sq]
    have h_asum2 : (a1 + a2) ^ 2 ≥ 3 := by
      have h1 : a1 * a2 ≥ 0 := by positivity
      nlinarith
    have h_bsum2 : (b1 + b2) ^ 2 ≤ 1 := by
      have h_tri : |b1 + b2| ≤ |b1| + |b2| := by
        have h : ‖b1 + b2‖ ≤ ‖b1‖ + ‖b2‖ := norm_add_le b1 b2
        simpa [Real.norm_eq_abs] using h
      have h1 : |b1 + b2| ≤ 4 * r := by
        calc |b1 + b2| ≤ |b1| + |b2| := h_tri
          _ ≤ 2 * r + 2 * r := by gcongr <;> linarith
          _ = 4 * r := by ring
      have h2 : |b1 + b2| ≤ 1 := by linarith [hr4]
      have h3 : (b1 + b2) ^ 2 ≤ (1 : ℝ) ^ 2 := (sq_le_sq).mpr (by simpa using h2)
      simpa using h3
    have h_eq : (a1 - a2) ^ 2 * (a1 + a2) ^ 2 = (b1 - b2) ^ 2 * (b1 + b2) ^ 2 := by
      have h1 : a1 ^ 2 - a2 ^ 2 = -(b1 ^ 2 - b2 ^ 2) := by linarith
      have h2 : (a1 - a2) * (a1 + a2) = -((b1 - b2) * (b1 + b2)) := by
        have h3 : (a1 - a2) * (a1 + a2) = a1 ^ 2 - a2 ^ 2 := by ring
        have h4 : (b1 - b2) * (b1 + b2) = b1 ^ 2 - b2 ^ 2 := by ring
        rw [h3, h4]; linarith
      have h5 : ((a1 - a2) * (a1 + a2)) ^ 2 = ((b1 - b2) * (b1 + b2)) ^ 2 := by rw [h2]; ring
      have h6 : (a1 - a2) ^ 2 * (a1 + a2) ^ 2 = ((a1 - a2) * (a1 + a2)) ^ 2 := by ring
      have h7 : ((b1 - b2) * (b1 + b2)) ^ 2 = (b1 - b2) ^ 2 * (b1 + b2) ^ 2 := by ring
      linarith
    have h_nonneg : 0 ≤ (a1 - a2) ^ 2 := by positivity
    have h9 : 3 * (a1 - a2) ^ 2 ≤ (a1 - a2) ^ 2 * (a1 + a2) ^ 2 := by
      calc 3 * (a1 - a2) ^ 2
        = (a1 - a2) ^ 2 * 3 := by ring
      _ ≤ (a1 - a2) ^ 2 * (a1 + a2) ^ 2 := by gcongr <;> linarith
    have h10 : (a1 - a2) ^ 2 * (a1 + a2) ^ 2 ≤ (b1 - b2) ^ 2 := by
      rw [h_eq]
      have h11 : 0 ≤ (b1 - b2) ^ 2 := by positivity
      calc (b1 - b2) ^ 2 * (b1 + b2) ^ 2
        ≤ (b1 - b2) ^ 2 * 1 := by gcongr <;> linarith
      _ = (b1 - b2) ^ 2 := by ring
    linarith
  have h_final : (b1 - b2) ^ 2 ≥ (3 / 4 : ℝ) * r ^ 2 := by
    have h : (a1 - a2) ^ 2 ≤ (1 / 3 : ℝ) * (b1 - b2) ^ 2 := by linarith
    linarith [h_norm2]
  have h_gt : (3 / 4 : ℝ) * r ^ 2 > ((5 / 6 : ℝ) * r) ^ 2 := by
    have h : (3 / 4 : ℝ) * r ^ 2 - ((5 / 6 : ℝ) * r) ^ 2 = (1 / 18 : ℝ) * r ^ 2 := by ring
    have h2 : 0 < (1 / 18 : ℝ) * r ^ 2 := by positivity
    have h3 : (3 / 4 : ℝ) * r ^ 2 - ((5 / 6 : ℝ) * r) ^ 2 > 0 := by rw [h] <;> exact h2
    linarith
  have h13 : (b1 - b2) ^ 2 > ((5 / 6 : ℝ) * r) ^ 2 := by linarith
  have h14 : 0 ≤ (5 / 6 : ℝ) * r := by positivity
  have h15 : |b1 - b2| ^ 2 = (b1 - b2) ^ 2 := by rw [sq_abs]
  have h16 : |(5 / 6 : ℝ) * r| = (5 / 6 : ℝ) * r := by
    rw [abs_of_pos] <;> positivity
  have h17 : |(5 / 6 : ℝ) * r| < |b1 - b2| := by
    have h13' : ((5 / 6 : ℝ) * r) ^ 2 < (b1 - b2) ^ 2 := h13
    exact (sq_lt_sq).mp h13'
  rw [h16] at h17
  exact le_of_lt h17

/-- At most 5 selected strip thickenings can contain a fixed point p. -/
lemma at_most_5_thickenings {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {base p : Point2} (hbase : ‖p - base‖ ≥ 1 / 2)
    {lines : Finset (AffineSubspace ℝ Point2)}
    (h_base : ∀ line ∈ lines, base ∈ (line : Set Point2))
    (h_fin : ∀ line ∈ lines, Module.finrank ℝ line.direction = 1)
    (h_sep : ∀ line₁ ∈ lines, ∀ line₂ ∈ lines, line₁ ≠ line₂ → WZ1LinesSeparated r line₁ line₂) :
    (lines.filter (fun (line : AffineSubspace ℝ Point2) => p ∈ Metric.thickening r (↑line : Set Point2))).card ≤ 5 := by
  let pred : AffineSubspace ℝ Point2 → Prop := fun line =>
    p ∈ Metric.thickening r (↑line : Set Point2)
  let S : Finset (AffineSubspace ℝ Point2) := lines.filter pred
  have hS_sub : S ⊆ lines := Finset.filter_subset _ _
  by_cases hS_empty : S = ∅
  · have h_goal : S.card ≤ 5 := by rw [hS_empty]; simp
    simpa [S, pred] using h_goal
  choose n hn_norm hn_orth using fun (line : _) (hline : line ∈ lines) =>
    exists_unit_normal_of_finrank_one (h_fin line hline)
  let v := p - base
  let rho := ‖v‖
  have hrho_pos : 0 < rho := by linarith [hbase]
  let u : Point2 := rho⁻¹ • v
  have hu_norm : ‖u‖ = 1 := by
    have h1 : ‖u‖ = |rho⁻¹| * ‖v‖ := norm_smul _ _
    rw [h1]
    have h2 : |rho⁻¹| = rho⁻¹ := by rw [abs_of_pos] <;> positivity
    rw [h2]
    have h3 : ‖v‖ = rho := by rfl
    rw [h3]
    field_simp [hrho_pos.ne'] <;> ring
  have h_b_bound_any : ∀ (line : _) (hline : line ∈ S) (n0 : Point2),
      ‖n0‖ = 1 → (∀ v ∈ line.direction, inner ℝ v n0 = 0) → |inner ℝ u n0| ≤ 2 * r := by
    intro line hline n0 hn0_norm hn0_orth
    have h_in : p ∈ Metric.thickening r (↑line : Set Point2) :=
      (Finset.mem_filter.mp hline).2
    have h_strip_set : Metric.thickening r (↑line : Set Point2) ⊆ {y : Point2 | |inner ℝ y n0 - inner ℝ base n0| ≤ r} :=
      thickening_subset_strip (h_fin line (hS_sub hline)) n0 hn0_norm hn0_orth
        base (h_base line (hS_sub hline)) r hr
    have h_strip : |inner ℝ p n0 - inner ℝ base n0| ≤ r := h_strip_set h_in
    have h3 : inner ℝ p n0 - inner ℝ base n0 = inner ℝ (p - base) n0 := by
      rw [←inner_sub_left]
    rw [h3] at h_strip
    have h4 : inner ℝ (p - base) n0 = rho * inner ℝ u n0 := by
      have h51 : rho • u = v := by
        calc rho • u
          = rho • (rho⁻¹ • v) := by rfl
        _ = (rho * rho⁻¹) • v := by rw [smul_smul]
        _ = (1 : ℝ) • v := by
          have h : rho * rho⁻¹ = 1 := by field_simp [hrho_pos.ne']
          rw [h]
        _ = v := by simp
      have h5 : p - base = rho • u := by exact h51.symm
      rw [h5]; simp [inner_smul_left] <;> ring
    rw [h4] at h_strip
    have h6 : |rho * inner ℝ u n0| ≤ r := h_strip
    have h7 : |inner ℝ u n0| ≤ r / rho := by
      have h8 : |rho * inner ℝ u n0| = rho * |inner ℝ u n0| := by
        rw [abs_mul, abs_of_pos hrho_pos]
      rw [h8] at h6
      calc |inner ℝ u n0|
        = (rho * |inner ℝ u n0|) / rho := by field_simp [hrho_pos.ne'] <;> ring
      _ ≤ r / rho := by gcongr
    have h9 : r / rho ≤ 2 * r := by
      have h10 : rho ≥ 1 / 2 := hbase
      have h11 : r / rho ≤ r / (1 / 2 : ℝ) := by gcongr
      have h12 : r / (1 / 2 : ℝ) = 2 * r := by ring
      rw [h12] at h11
      exact h11
    exact h7.trans h9
  let b_line : AffineSubspace ℝ Point2 → ℝ := fun line =>
    if hline : line ∈ S then
      let n0 := n line (hS_sub hline)
      let a0 := cross2 n0 u
      let n1 := if a0 > 0 then n0 else -n0
      inner ℝ u n1
    else 0
  have h_props : ∀ (line : _) (hline : line ∈ S),
      let n0 := n line (hS_sub hline)
      let a0 := cross2 n0 u
      let n1 := if a0 > 0 then n0 else -n0
      let a := cross2 n1 u
      let b := inner ℝ u n1
      ‖n1‖ = 1 ∧ (∀ v ∈ line.direction, inner ℝ v n1 = 0) ∧ a > 0 ∧ a ^ 2 + b ^ 2 = 1 ∧ |b| ≤ 2 * r := by
    intro line hline
    dsimp only
    let n0 := n line (hS_sub hline)
    have hn0_norm : ‖n0‖ = 1 := hn_norm line (hS_sub hline)
    have hn0_orth : ∀ v ∈ line.direction, inner ℝ v n0 = 0 := hn_orth line (hS_sub hline)
    let a0 := cross2 n0 u
    let b0 := inner ℝ u n0
    have hb0_bound : |b0| ≤ 2 * r := h_b_bound_any line hline n0 hn0_norm hn0_orth
    have ha0_ne_zero : a0 ≠ 0 := by
      by_contra ha0
      have h1 : ‖n0‖ ^ 2 = b0 ^ 2 + a0 ^ 2 := by
        have h_tmp := norm_cross_identity n0 u hu_norm
        have h_sym : inner ℝ n0 u = inner ℝ u n0 := (real_inner_comm n0 u).symm
        rw [h_sym] at h_tmp
        exact h_tmp
      rw [ha0] at h1
      rw [hn0_norm] at h1
      have h3 : b0 ^ 2 = 1 := by nlinarith
      have h4 : |b0| = 1 := by
        have h5 : b0 ^ 2 = 1 := h3
        have h6 : |b0| ^ 2 = 1 := by simpa [sq_abs] using h5
        have h7 : 0 ≤ |b0| := by positivity
        nlinarith
      rw [h4] at hb0_bound
      linarith [hr4]
    let n1 := if a0 > 0 then n0 else -n0
    let a := cross2 n1 u
    let b := inner ℝ u n1
    have hn1_norm : ‖n1‖ = 1 := by
      dsimp only [n1]; split_ifs <;> simp [hn0_norm] <;> norm_num
    have hn1_orth : ∀ v ∈ line.direction, inner ℝ v n1 = 0 := by
      dsimp only [n1]; split_ifs <;> simpa [hn0_orth, inner_neg_left] using hn0_orth
    have h_a_pos : a > 0 := by
      dsimp only [a, n1]
      by_cases hpos : a0 > 0
      · rw [if_pos hpos]; exact hpos
      · have hneg : a0 < 0 := by
          have h_le : a0 ≤ 0 := by linarith
          exact lt_of_le_of_ne h_le ha0_ne_zero
        rw [if_neg hpos]
        have h_cross_neg : cross2 (-n0) u = -cross2 n0 u := by
          simp [cross2] <;> ring
        rw [h_cross_neg]
        linarith
    have h_ab2 : a ^ 2 + b ^ 2 = 1 := by
      have h : ‖n1‖ ^ 2 = a ^ 2 + b ^ 2 := by
        have h_tmp := norm_cross_identity n1 u hu_norm
        have h_sym : inner ℝ n1 u = inner ℝ u n1 := (real_inner_comm n1 u).symm
        rw [h_sym] at h_tmp
        have h_eq : (inner ℝ u n1) ^ 2 + (cross2 n1 u) ^ 2 = a ^ 2 + b ^ 2 := by ring
        rw [h_eq] at h_tmp
        exact h_tmp
      have h2 : ‖n1‖ ^ 2 = 1 := by rw [hn1_norm] <;> norm_num
      linarith
    have h_b_bound : |b| ≤ 2 * r := h_b_bound_any line hline n1 hn1_norm hn1_orth
    exact ⟨hn1_norm, hn1_orth, h_a_pos, h_ab2, h_b_bound⟩
  have h_b_sep : ∀ (line1 : _) (hline1 : line1 ∈ S) (line2 : _) (hline2 : line2 ∈ S),
      line1 ≠ line2 → (5 / 6 : ℝ) * r ≤ |b_line line1 - b_line line2| := by
    intro line1 hline1 line2 hline2 hne
    dsimp only [b_line]
    rw [dif_pos hline1, dif_pos hline2]
    let n0_1 := n line1 (hS_sub hline1)
    let a0_1 := cross2 n0_1 u
    let n1 := if a0_1 > 0 then n0_1 else -n0_1
    let a1 := cross2 n1 u
    let b1 := inner ℝ u n1
    let n0_2 := n line2 (hS_sub hline2)
    let a0_2 := cross2 n0_2 u
    let n2 := if a0_2 > 0 then n0_2 else -n0_2
    let a2 := cross2 n2 u
    let b2 := inner ℝ u n2
    have h1 := h_props line1 hline1
    have h2 := h_props line2 hline2
    dsimp only at h1 h2
    rcases h1 with ⟨hn1_norm, hn1_orth, ha1_pos, h_ab1, hb1_bound⟩
    rcases h2 with ⟨hn2_norm, hn2_orth, ha2_pos, h_ab2, hb2_bound⟩
    have h_sep' : r ≤ ‖n1 - n2‖ :=
      (h_sep line1 (hS_sub hline1) line2 (hS_sub hline2) hne) n1 n2 hn1_norm hn2_norm hn1_orth hn2_orth |>.1
    have h_norm2 : ‖n1 - n2‖ ^ 2 = (b1 - b2) ^ 2 + (a1 - a2) ^ 2 := by
      have h : ‖n1 - n2‖ ^ 2 = (inner ℝ (n1 - n2) u) ^ 2 + (cross2 (n1 - n2) u) ^ 2 :=
        norm_cross_identity (n1 - n2) u hu_norm
      rw [h]
      have h_i : inner ℝ (n1 - n2) u = b1 - b2 := by
        rw [inner_sub_left]
        have h1 : inner ℝ n1 u = b1 := (real_inner_comm n1 u).symm
        have h2 : inner ℝ n2 u = b2 := (real_inner_comm n2 u).symm
        rw [h1, h2]
      have h_c : cross2 (n1 - n2) u = a1 - a2 := by
        have h_c1 : cross2 (n1 - n2) u = cross2 n1 u - cross2 n2 u := by
          simp [cross2] <;> ring
        rw [h_c1] <;> rfl
      rw [h_i, h_c] <;> ring
    have h_norm2_ge : (b1 - b2) ^ 2 + (a1 - a2) ^ 2 ≥ r ^ 2 := by
      have h : r ^ 2 ≤ ‖n1 - n2‖ ^ 2 := by gcongr
      rw [h_norm2] at h
      exact h
    exact algebraic_separation_bound hr hr4 ha1_pos ha2_pos h_ab1 h_ab2 hb1_bound hb2_bound h_norm2_ge
  let bSet : Finset ℝ := S.image b_line
  have h_bSet_bound : ∀ x ∈ bSet, -(4 * r) / 2 ≤ x ∧ x ≤ (4 * r) / 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨line, hline, rfl⟩
    have h_b : |b_line line| ≤ 2 * r := by
      dsimp only [b_line]; rw [dif_pos hline]
      exact (h_props line hline).2.2.2.2
    exact ⟨by linarith [abs_le.mp h_b], by linarith [abs_le.mp h_b]⟩
  have h_bSet_sep : ∀ x ∈ bSet, ∀ y ∈ bSet, x ≠ y → (5 / 6 : ℝ) * r ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨line1, hline1, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨line2, hline2, rfl⟩
    have hne' : line1 ≠ line2 := by intro h; rw [h] at hxy; exact hxy rfl
    exact h_b_sep line1 hline1 line2 hline2 hne'
  have hW : 0 < 4 * r := by positivity
  have hd : 0 < (5 / 6 : ℝ) * r := by positivity
  have hfive : 5 * ((5 / 6 : ℝ) * r) > 4 * r := by linarith
  have h_pack : bSet.card ≤ 5 := real_packing_5 hW hd hfive h_bSet_bound h_bSet_sep
  have h_inj : Set.InjOn b_line S := by
    intro line1 hline1 line2 hline2 h_eq
    by_contra hne
    have h10 := h_b_sep line1 hline1 line2 hline2 hne
    rw [h_eq] at h10
    have h_contra : (5 / 6 : ℝ) * r ≤ 0 := by
      simpa using h10
    have h_pos : 0 < (5 / 6 : ℝ) * r := by positivity
    linarith
  have h_card : bSet.card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  rw [←h_card]
  exact h_pack

/-! ### Combinatorial double counting -/

/--
Combinatorial core of WZ1 Lemma 44.

If every `G₂` point lies in at most `20` selected strip thickenings, and every
selected strip is heavy (contains `> K * r^(1/4) * #G₂` points of `G₂`), then
`#lines ≤ 20 / (K^2 * r^(1/2))`.

Proof: double count incidences, bound the sum of squares by `20 * #G₂^2`,
and apply Cauchy-Schwarz.
-/
lemma heavy_line_packing_from_multiplicity
    {r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    {G₂ : DiscreteSet 2}
    {lines : Finset (AffineSubspace ℝ Point2)}
    (S : AffineSubspace ℝ Point2 → DiscreteSet 2)
    (hS : ∀ line, S line = G₂.filter (fun p => p ∈ Metric.thickening r (line : Set Point2)))
    (h_heavy : ∀ line ∈ lines,
        ((S line).card : ENNReal) >
          ENNReal.ofReal (K * Real.rpow r (1 / 4 : ℝ)) * G₂.enncard)
    (h_mult : ∀ p ∈ G₂,
        (lines.filter (fun line => p ∈ S line)).card ≤ 20) :
    (lines.card : ℝ) ≤ 20 / (K ^ 2 * Real.rpow r (1 / 2 : ℝ)) := by
  by_cases hL : lines = ∅
  · rw [hL]
    simp
    <;> positivity
  have hL_nonempty : lines.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hL
  by_cases hG2 : G₂ = ∅
  · obtain ⟨line, hline⟩ := hL_nonempty
    have h_cont := h_heavy line hline
    simp [hG2, hS] at h_cont <;> contradiction
  have hG2_nonempty : G₂.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hG2
  set N : ℕ := G₂.card with hN_def
  set L : ℕ := lines.card with hL_def
  have hN_pos : 0 < N := G₂.card_pos.mpr hG2_nonempty
  have hL_pos : 0 < L := Finset.card_pos.mpr hL_nonempty
  have hS_sub : ∀ line, S line ⊆ G₂ := by
    intro line
    rw [hS line]
    exact Finset.filter_subset _ _
  have h_heavy_real : ∀ line ∈ lines,
      ((S line).card : ℝ) > K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ) := by
    intro line hline
    have h1 := h_heavy line hline
    have h_nonneg : 0 ≤ K * Real.rpow r (1 / 4 : ℝ) := by
      have h : 0 ≤ Real.rpow r (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
      exact mul_nonneg (by linarith) h
    have h_enncard : G₂.enncard = ↑N := by
      simp [hN_def] <;> rfl
    have h_mul : ENNReal.ofReal (K * Real.rpow r (1 / 4 : ℝ)) * (↑N : ENNReal) =
        ENNReal.ofReal (K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ)) := by
      have h_coe_N : (↑N : ENNReal) = ENNReal.ofReal (N : ℝ) := by simp
      rw [h_coe_N]
      rw [← ENNReal.ofReal_mul h_nonneg]
      <;> rfl
    rw [h_enncard, h_mul] at h1
    have h_coe_card : (↑(S line).card : ENNReal) =
        ENNReal.ofReal ((S line).card : ℝ) := by simp
    rw [h_coe_card] at h1
    have h_pos2 : 0 ≤ K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ) := by positivity
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_pos2).mp h1
  have h_alpha_lt_one : K * Real.rpow r (1 / 4 : ℝ) < 1 := by
    obtain ⟨line, hline⟩ := hL_nonempty
    have h3 : (S line).card ≤ N := Finset.card_le_card (hS_sub line)
    have h4 : ((S line).card : ℝ) > K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ) :=
      h_heavy_real line hline
    have h5 : ((S line).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast h3
    have hN_pos' : (N : ℝ) > 0 := by exact_mod_cast hN_pos
    nlinarith
  let d : Point2 → ℕ := fun p =>
    (lines.filter (fun line => p ∈ S line)).card
  let I : Finset (AffineSubspace ℝ Point2 × Point2) :=
    (lines ×ˢ G₂).filter (fun pair => pair.2 ∈ S pair.1)
  have hI1 : I.card = ∑ line ∈ lines, (S line).card := by
    have h_disj : ∀ line1 ∈ lines, ∀ line2 ∈ lines, line1 ≠ line2 →
        Disjoint (({line1} : Finset (AffineSubspace ℝ Point2)) ×ˢ S line1)
                 (({line2} : Finset (AffineSubspace ℝ Point2)) ×ˢ S line2) := by
      intro line1 _ line2 _ hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x.1 = line1 := Finset.mem_singleton.mp (Finset.mem_product.mp hx1).1
      have h2 : x.1 = line2 := Finset.mem_singleton.mp (Finset.mem_product.mp hx2).1
      exact hne (h1.symm.trans h2)
    have h_biUnion : I = lines.biUnion (fun line => {line} ×ˢ S line) := by
      ext ⟨line, p⟩
      simp [I, hS_sub line]
      <;> tauto
    rw [h_biUnion]
    rw [Finset.card_biUnion h_disj]
    apply Finset.sum_congr rfl
    intro line _
    simp
  have hI2 : I.card = ∑ p ∈ G₂, d p := by
    have h_disj2 : ∀ p1 ∈ G₂, ∀ p2 ∈ G₂, p1 ≠ p2 →
        Disjoint ((lines.filter (fun line => p1 ∈ S line)) ×ˢ ({p1} : Finset Point2))
                 ((lines.filter (fun line => p2 ∈ S line)) ×ˢ ({p2} : Finset Point2)) := by
      intro p1 _ p2 _ hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x.2 = p1 := Finset.mem_singleton.mp (Finset.mem_product.mp hx1).2
      have h2 : x.2 = p2 := Finset.mem_singleton.mp (Finset.mem_product.mp hx2).2
      exact hne (h1.symm.trans h2)
    have h_biUnion2 : I = G₂.biUnion (fun p =>
        (lines.filter (fun line => p ∈ S line)) ×ˢ ({p} : Finset Point2)) := by
      ext ⟨line, p⟩
      simp [I, d]
      <;> tauto
    rw [h_biUnion2]
    rw [Finset.card_biUnion h_disj2]
    apply Finset.sum_congr rfl
    intro p _
    simp [d]
  have h_incidence : ∑ line ∈ lines, (S line).card = ∑ p ∈ G₂, d p := by
    rw [← hI1, hI2]
  have h3 : ∀ line ∈ lines, (S line).card ^ 2 ≤ N * (S line).card := by
    intro line _
    have h4 : (S line).card ≤ N := Finset.card_le_card (hS_sub line)
    nlinarith
  have h5 : ∑ line ∈ lines, (S line).card ^ 2 ≤
      N * ∑ line ∈ lines, (S line).card := by
    calc
      ∑ line ∈ lines, (S line).card ^ 2
        ≤ ∑ line ∈ lines, N * (S line).card := by
          gcongr with line hline
          exact h3 line hline
      _ = N * ∑ line ∈ lines, (S line).card := by
        rw [Finset.mul_sum] <;> ring
  have h6 : N * ∑ line ∈ lines, (S line).card ≤ 20 * N ^ 2 := by
    rw [h_incidence]
    have h7 : ∑ p ∈ G₂, d p ≤ ∑ p ∈ G₂, 20 := by
      gcongr with p hp
      exact h_mult p hp
    have h8 : ∑ p ∈ G₂, (20 : ℕ) = 20 * N := by
      simp [hN_def, Finset.sum_const] <;> ring
    rw [h8] at h7
    nlinarith
  have h_sum_sq : ∑ line ∈ lines, (S line).card ^ 2 ≤ 20 * N ^ 2 :=
    h5.trans h6
  have h_cs :
      (∑ line ∈ lines, ((S line).card : ℝ)) ^ 2 ≤
      (L : ℝ) * ∑ line ∈ lines, (((S line).card : ℝ) ^ 2) := by
    exact sq_sum_le_card_mul_sum_sq
  have h_heavy_sum :
      (∑ line ∈ lines, ((S line).card : ℝ)) >
      (L : ℝ) * (K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ)) := by
    have h : ∑ line ∈ lines, ((S line).card : ℝ) >
        ∑ line ∈ lines, (K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ)) := by
      apply Finset.sum_lt_sum_of_nonempty hL_nonempty
      intro line hline
      exact h_heavy_real line hline
    have h9 : ∑ line ∈ lines, (K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ)) =
        (L : ℝ) * (K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ)) := by
      simp [Finset.sum_const, hL_def] <;> ring
    rw [h9] at h
    exact h
  have h_sum_sq_real :
      (∑ line ∈ lines, (((S line).card : ℝ) ^ 2)) ≤ (20 : ℝ) * (N : ℝ) ^ 2 := by
    exact_mod_cast h_sum_sq
  have h_rpow_sq :
      (Real.rpow r (1 / 4 : ℝ)) ^ 2 = Real.rpow r (1 / 2 : ℝ) := by
    have h_add : Real.rpow r (1 / 4 : ℝ) * Real.rpow r (1 / 4 : ℝ) =
        Real.rpow r ((1 / 4 : ℝ) + (1 / 4 : ℝ)) :=
      (Real.rpow_add hr (1 / 4 : ℝ) (1 / 4 : ℝ)).symm
    have h_eq2 : (1 / 4 : ℝ) + (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
    have h : (Real.rpow r (1 / 4 : ℝ)) ^ 2 =
        Real.rpow r (1 / 4 : ℝ) * Real.rpow r (1 / 4 : ℝ) := by ring
    rw [h, h_add, h_eq2]
  have h_main : (L : ℝ) * K ^ 2 * Real.rpow r (1 / 2 : ℝ) < 20 := by
    set a : ℝ := (L : ℝ) * (K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ)) with ha_def
    set b : ℝ := (∑ line ∈ lines, ((S line).card : ℝ)) with hb_def
    have h_ab : a < b := h_heavy_sum
    have ha_pos : 0 < a := by
      dsimp only [a]
      have h1 : 0 < (L : ℝ) := by exact_mod_cast hL_pos
      have h_rpow_pos : 0 < Real.rpow r (1 / 4 : ℝ) := Real.rpow_pos_of_pos hr _
      have hN_pos' : 0 < (N : ℝ) := by exact_mod_cast hN_pos
      have h2 : 0 < K * Real.rpow r (1 / 4 : ℝ) * (N : ℝ) := by
        exact mul_pos (mul_pos hK h_rpow_pos) hN_pos'
      exact mul_pos h1 h2
    have h8 : a ^ 2 < b ^ 2 := by nlinarith
    have h9 : b ^ 2 ≤ (L : ℝ) * (20 : ℝ) * (N : ℝ) ^ 2 := by
      calc
        b ^ 2 ≤ (L : ℝ) * ∑ line ∈ lines, (((S line).card : ℝ) ^ 2) := h_cs
        _ ≤ (L : ℝ) * ((20 : ℝ) * (N : ℝ) ^ 2) := by gcongr
        _ = (L : ℝ) * (20 : ℝ) * (N : ℝ) ^ 2 := by ring
    have h10 : a ^ 2 < (L : ℝ) * (20 : ℝ) * (N : ℝ) ^ 2 := by linarith
    have h_a_sq : a ^ 2 =
        (L : ℝ) ^ 2 * K ^ 2 * (Real.rpow r (1 / 4 : ℝ)) ^ 2 * (N : ℝ) ^ 2 := by
      simp [ha_def] <;> ring
    rw [h_a_sq, h_rpow_sq] at h10
    have hL_pos' : (L : ℝ) > 0 := by exact_mod_cast hL_pos
    have hN_pos' : (N : ℝ) > 0 := by exact_mod_cast hN_pos
    nlinarith
  have h_pos_denom : 0 < K ^ 2 * Real.rpow r (1 / 2 : ℝ) := by
    have h1 : 0 < K ^ 2 := by positivity
    have h2 : 0 < Real.rpow r (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
    exact mul_pos h1 h2
  have h_final : (L : ℝ) ≤ 20 / (K ^ 2 * Real.rpow r (1 / 2 : ℝ)) := by
    have h9 : (L : ℝ) * (K ^ 2 * Real.rpow r (1 / 2 : ℝ)) < 20 := by
      have h10 : (L : ℝ) * K ^ 2 * Real.rpow r (1 / 2 : ℝ) < 20 := h_main
      ring_nf at h10 ⊢ <;> exact h10
    have h_pos : 0 < K ^ 2 * Real.rpow r (1 / 2 : ℝ) := h_pos_denom
    have h_div : (L : ℝ) * (K ^ 2 * Real.rpow r (1 / 2 : ℝ)) / (K ^ 2 * Real.rpow r (1 / 2 : ℝ)) = (L : ℝ) := by
      apply mul_div_cancel_right₀
      exact h_pos_denom.ne'
    have h10 : (L : ℝ) < 20 / (K ^ 2 * Real.rpow r (1 / 2 : ℝ)) := by
      rw [← h_div]
      exact div_lt_div_of_pos_right h9 h_pos
    exact h10.le
  exact h_final

/-! ### Main theorem -/

theorem wz1_heavy_line_packing : WZ1HeavyLinePackingStatement := by
  intro delta r K hdelta hdr hr4 hK G₁ G₂ hsep base hbase lines hbase_line hfin hsep_lines h_heavy
  have hr_pos : 0 < r := by linarith
  by_cases h_lines_empty : lines = ∅
  · rw [h_lines_empty]
    simp
    <;> positivity
  let S_fun : AffineSubspace ℝ Point2 → DiscreteSet 2 := fun line =>
    G₂.filter (fun p => p ∈ Metric.thickening r (line : Set Point2))
  have hS_def : ∀ line, S_fun line = G₂.filter (fun p => p ∈ Metric.thickening r (line : Set Point2)) := by
    intro line; rfl
  have h_mult : ∀ p ∈ G₂, (lines.filter (fun line => p ∈ S_fun line)).card ≤ 20 := by
    intro p hp
    have h_dist : (1 / 2 : ℝ) ≤ dist base p := hsep base hbase p hp
    have hbase' : ‖p - base‖ ≥ 1 / 2 := by
      have h_dist : (1 / 2 : ℝ) ≤ dist base p := hsep base hbase p hp
      have h1 : dist base p = ‖base - p‖ := by simp [dist_eq_norm]
      have h2 : ‖base - p‖ = ‖p - base‖ := by
        have h3 : base - p = -(p - base) := by abel
        rw [h3, norm_neg]
      rw [h1, h2] at h_dist
      exact h_dist
    have h_filter_eq : lines.filter (fun line => p ∈ S_fun line) =
        lines.filter (fun (line : AffineSubspace ℝ Point2) => p ∈ Metric.thickening r (↑line : Set Point2)) := by
      apply Finset.filter_congr
      intro line _
      have h1 : p ∈ S_fun line ↔ p ∈ Metric.thickening r (↑line : Set Point2) := by
        simp only [S_fun, Finset.mem_filter]
        <;> tauto
      exact h1
    rw [h_filter_eq]
    have h5 : (lines.filter (fun (line : AffineSubspace ℝ Point2) => p ∈ Metric.thickening r (↑line : Set Point2))).card ≤ 5 :=
      @at_most_5_thickenings r hr_pos hr4 base p hbase' lines hbase_line hfin hsep_lines
    exact h5.trans (by norm_num)
  exact heavy_line_packing_from_multiplicity hr_pos hK S_fun hS_def h_heavy h_mult

end Kakeya.Assouad
