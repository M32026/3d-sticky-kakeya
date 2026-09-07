module

/-
  A2 Strip Packing Lemma

  Geometric argument: coarse tubes through a fixed Δ-square lie in a strip
  of width O(Δ) in (slope, intercept) parameter space. A Δ-separated set
  in such a strip has cardinality O(Δ^{-1}).

  This provides the hC_card_upper bound for A2.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.A2

open DirecretisedFurstenbergEstimate

/-! 1D packing: r-separated reals in interval of length L have ≤ L/r + 1 elements. -/

lemma one_d_packing {r L x0 : ℝ} (hr_pos : 0 < r) (hL_nonneg : 0 ≤ L)
    {S : Finset ℝ} (hS_sub : (S : Set ℝ) ⊆ Set.Icc x0 (x0 + L))
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ |x - y|) :
    (S.card : ℝ) ≤ L / r + 1 := by
  let f : ℝ → ℤ := fun x => Int.floor ((x - x0) / r)
  have h1 : ∀ x ∈ S, 0 ≤ f x := by
    intro x hx
    have h2 : x0 ≤ x := (hS_sub hx).1
    have h3 : 0 ≤ x - x0 := by linarith
    have h4 : 0 ≤ (x - x0) / r := by positivity
    exact Int.floor_nonneg.mpr h4
  have h4 : ∀ x ∈ S, (f x : ℝ) ≤ L / r := by
    intro x hx
    have h5 : x ≤ x0 + L := (hS_sub hx).2
    have h6 : x - x0 ≤ L := by linarith
    have h7 : (x - x0) / r ≤ L / r := by
      apply div_le_div_of_nonneg_right h6 hr_pos.le
    have h8 : (f x : ℝ) ≤ (x - x0) / r := Int.floor_le _
    linarith
  have h_inj : Set.InjOn f (S : Set ℝ) := by
    intro x hx y hy h_eq
    by_contra h_ne
    have h8 : (f x : ℝ) ≤ (x - x0) / r := Int.floor_le _
    have h9 : (x - x0) / r < (f x : ℝ) + 1 := Int.lt_floor_add_one _
    have h10 : (f y : ℝ) ≤ (y - x0) / r := Int.floor_le _
    have h11 : (y - x0) / r < (f y : ℝ) + 1 := Int.lt_floor_add_one _
    have h_eq' : (f x : ℝ) = (f y : ℝ) := by exact_mod_cast h_eq
    have h12 : (x - x0) / r - (y - x0) / r < 1 := by linarith
    have h13 : (y - x0) / r - (x - x0) / r < 1 := by linarith
    have h14 : |(x - x0) / r - (y - x0) / r| < 1 := by
      rw [abs_lt] <;> constructor <;> linarith
    have h15 : (x - x0) / r - (y - x0) / r = (x - y) / r := by ring
    rw [h15] at h14
    have h16 : |(x - y) / r| < 1 := h14
    have h17 : |x - y| / r < 1 := by
      have h18 : |(x - y) / r| = |x - y| / r := by
        rw [abs_div] <;> rw [abs_of_pos hr_pos]
      rw [h18] at h16 <;> exact h16
    have h19 : |x - y| < r := by
      calc |x - y| = (|x - y| / r) * r := by field_simp [hr_pos.ne'] <;> ring
      _ < 1 * r := by gcongr
      _ = r := by ring
    have h20 : r ≤ |x - y| := hS_sep x hx y hy h_ne
    linarith
  let S' : Finset ℤ := S.image f
  have h_card : S'.card = S.card := by
    apply Finset.card_image_of_injOn
    exact h_inj
  have h_floor_nonneg : 0 ≤ Int.floor (L / r) := by
    apply Int.floor_nonneg.mpr
    positivity
  have h_sub : S' ⊆ Finset.Icc 0 (Int.floor (L / r)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have h5 : 0 ≤ f x := h1 x hx
    have h6 : (f x : ℝ) ≤ L / r := h4 x hx
    have h7 : f x ≤ Int.floor (L / r) := by
      apply Int.le_floor.mpr
      exact h6
    simp only [Finset.mem_Icc]
    exact ⟨h5, h7⟩
  have h_final : S.card ≤ (Finset.Icc 0 (Int.floor (L / r))).card := by
    rw [←h_card]
    exact Finset.card_le_card h_sub
  have h_card2 : (Finset.Icc 0 (Int.floor (L / r))).card =
      (Int.floor (L / r)).toNat + 1 := by
    have h' : 0 ≤ Int.floor (L / r) := h_floor_nonneg
    simp [h', Finset.Icc_eq_empty_of_lt]
    <;> omega
  rw [h_card2] at h_final
  have h9 : ((Int.floor (L / r)).toNat : ℝ) ≤ (Int.floor (L / r) : ℝ) := by
    have h' : 0 ≤ Int.floor (L / r) := h_floor_nonneg
    have h'' : ((Int.floor (L / r)).toNat : ℤ) = Int.floor (L / r) := by
      rw [Int.toNat_of_nonneg h']
    have h3 : ((Int.floor (L / r)).toNat : ℝ) = (Int.floor (L / r) : ℝ) := by exact_mod_cast h''
    rw [h3]
  have h10 : (Int.floor (L / r) : ℝ) ≤ L / r := Int.floor_le _
  have h11 : ((Int.floor (L / r)).toNat : ℝ) ≤ L / r := by linarith
  have h12 : (S.card : ℝ) ≤ ((Int.floor (L / r)).toNat : ℝ) + 1 := by
    exact_mod_cast h_final
  linarith

/-! Strip packing for AffineLines through a Δ-square. -/

/-- A Δ-separated set of AffineLines, each passing within C*Δ of a point in
    a fixed Δ-square, has cardinality at most K/Δ. -/
lemma affineLine_strip_packing {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (C_strip : ℝ) (hC_nonneg : 0 ≤ C_strip)
    (S : Finset AffineLine)
    (hS_sep : SeparatedAt Δ (S : Set AffineLine))
    (hS_v : ∀ ℓ ∈ S, (LemmaE.getDirV ℓ) 1 ≠ 0)
    (hS_a : ∀ ℓ ∈ S, |(LemmaE.affineLineParams ℓ).1| ≤ 1)
    (hS_b : ∀ ℓ ∈ S, |(LemmaE.affineLineParams ℓ).2| ≤ 3)
    (Q : CoarseSquare Δ)
    (h_strip : ∀ ℓ ∈ S, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
        |(LemmaE.affineLineParams ℓ).2 - (p 0 - (LemmaE.affineLineParams ℓ).1 * p 1)| ≤ C_strip * Δ) :
    (S.card : ℝ) ≤ (42 : ℝ) * (40 * C_strip + 110) / Δ := by
  let a (ℓ : AffineLine) : ℝ := (LemmaE.affineLineParams ℓ).1
  let b (ℓ : AffineLine) : ℝ := (LemmaE.affineLineParams ℓ).2
  let w : ℝ := Δ / 20
  have hw_pos : 0 < w := by positivity
  have h_w_le : w ≤ Δ / 10 := by
    have h : Δ / 20 ≤ Δ / 10 := by
      apply div_le_div_of_nonneg_left hΔ_pos.le
      <;> norm_num
    exact h
  let k (ℓ : AffineLine) : ℤ := Int.floor ((a ℓ + 1) / w)
  have h_k_range : ∀ ℓ ∈ S, 0 ≤ k ℓ ∧ (k ℓ : ℝ) ≤ 40 / Δ := by
    intro ℓ hℓ
    have ha : |a ℓ| ≤ 1 := hS_a ℓ hℓ
    have ha1 : -1 ≤ a ℓ := (abs_le.mp ha).1
    have ha2 : a ℓ ≤ 1 := (abs_le.mp ha).2
    have h1 : 0 ≤ (a ℓ + 1) / w := by
      apply div_nonneg <;> linarith
    have h2 : (a ℓ + 1) / w ≤ 40 / Δ := by
      have h3 : a ℓ + 1 ≤ 2 := by linarith
      have h4 : (a ℓ + 1) / w ≤ 2 / w := by
        apply div_le_div_of_nonneg_right h3 hw_pos.le
      have h5 : 2 / w = 40 / Δ := by
        simp [w] <;> ring
      linarith
    constructor
    · exact Int.floor_nonneg.mpr h1
    · have h6 : (k ℓ : ℝ) ≤ (a ℓ + 1) / w := Int.floor_le _
      linarith
  have h_antilip : ∀ ℓ1 ℓ2 : AffineLine, ℓ1 ∈ S → ℓ2 ∈ S →
      dist ℓ1 ℓ2 ≤ 10 * dist (a ℓ1, b ℓ1) (a ℓ2, b ℓ2) := by
    intro ℓ1 ℓ2 h1 h2
    exact AffineLineLipschitzTransfer.affineLineParams_antilipschitz
      ℓ1 ℓ2 (hS_v ℓ1 h1) (hS_v ℓ2 h2) (hS_a ℓ1 h1) (hS_a ℓ2 h2) (hS_b ℓ1 h1) (hS_b ℓ2 h2)
  let K_b : ℝ := 40 * C_strip + 110
  have hK_b_pos : 0 < K_b := by positivity
  have h_main : ∀ (ki : ℤ), (S.filter (fun ℓ => k ℓ = ki)).card ≤ K_b := by
    intro ki
    let S_k := S.filter (fun ℓ => k ℓ = ki)
    by_cases h_empty : S_k = ∅
    · simpa [S_k, h_empty] using hK_b_pos.le
    · have hS_k_nonempty : S_k.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
      rcases hS_k_nonempty with ⟨ℓ0, hℓ0⟩
      have hℓ0_in_S : ℓ0 ∈ S := by
        simpa [S_k] using (Finset.mem_filter.mp hℓ0).1
      have h_k0 : k ℓ0 = ki := by
        simpa [S_k] using (Finset.mem_filter.mp hℓ0).2
      rcases h_strip ℓ0 hℓ0_in_S with ⟨p0, hp0_in, hpy0, h_close0⟩
      let b0 : ℝ := p0 0 - a ℓ0 * p0 1
      have h_b_interval : ∀ ℓ ∈ S_k, |b ℓ - b0| ≤ (2 * C_strip + 5) * Δ := by
        intro ℓ hℓ
        have hℓ_in_S : ℓ ∈ S := (Finset.mem_filter.mp hℓ).1
        have h_k_eq : k ℓ = ki := (Finset.mem_filter.mp hℓ).2
        have h_k_same : k ℓ = k ℓ0 := by rw [h_k_eq, h_k0]
        have h_a_close : |a ℓ - a ℓ0| < w := by
          have h1 : (k ℓ : ℝ) ≤ (a ℓ + 1) / w := Int.floor_le _
          have h2 : (a ℓ + 1) / w < (k ℓ : ℝ) + 1 := Int.lt_floor_add_one _
          have h3 : (k ℓ0 : ℝ) ≤ (a ℓ0 + 1) / w := Int.floor_le _
          have h4 : (a ℓ0 + 1) / w < (k ℓ0 : ℝ) + 1 := Int.lt_floor_add_one _
          have h_same' : (k ℓ : ℝ) = (k ℓ0 : ℝ) := by exact_mod_cast h_k_same
          have h5 : (a ℓ + 1) / w - (a ℓ0 + 1) / w < 1 := by linarith
          have h6 : (a ℓ0 + 1) / w - (a ℓ + 1) / w < 1 := by linarith
          have h7 : |(a ℓ + 1) / w - (a ℓ0 + 1) / w| < 1 := by
            rw [abs_lt] <;> constructor <;> linarith
          have h8 : (a ℓ + 1) / w - (a ℓ0 + 1) / w = (a ℓ - a ℓ0) / w := by ring
          rw [h8] at h7
          have h9 : |(a ℓ - a ℓ0) / w| < 1 := h7
          have h10 : |a ℓ - a ℓ0| / w < 1 := by
            have h11 : |(a ℓ - a ℓ0) / w| = |a ℓ - a ℓ0| / w := by
              rw [abs_div] <;> rw [abs_of_pos hw_pos]
            rw [h11] at h9 <;> exact h9
          exact (div_lt_one hw_pos).mp h10
        rcases h_strip ℓ hℓ_in_S with ⟨p, hp_in, hpy, h_close⟩
        have h_p1 : p 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := (hp_in).1
        have h_p01 : p0 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := (hp0_in).1
        have h_p1_diff : |p 0 - p0 0| ≤ Δ := by
          have h11 : Δ * (Q.1 : ℝ) ≤ p 0 := h_p1.1
          have h12 : p 0 < Δ * ((Q.1 : ℝ) + 1) := h_p1.2
          have h13 : Δ * (Q.1 : ℝ) ≤ p0 0 := h_p01.1
          have h14 : p0 0 < Δ * ((Q.1 : ℝ) + 1) := h_p01.2
          have h15 : p 0 - p0 0 ≤ Δ := by linarith
          have h16 : -Δ ≤ p 0 - p0 0 := by linarith
          exact abs_le.mpr ⟨h16, h15⟩
        have h_p2 : p 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := (hp_in).2
        have h_p02 : p0 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := (hp0_in).2
        have h_p2_diff : |p 1 - p0 1| ≤ Δ := by
          have h11 : Δ * (Q.2 : ℝ) ≤ p 1 := h_p2.1
          have h12 : p 1 < Δ * ((Q.2 : ℝ) + 1) := h_p2.2
          have h13 : Δ * (Q.2 : ℝ) ≤ p0 1 := h_p02.1
          have h14 : p0 1 < Δ * ((Q.2 : ℝ) + 1) := h_p02.2
          have h15 : p 1 - p0 1 ≤ Δ := by linarith
          have h16 : -Δ ≤ p 1 - p0 1 := by linarith
          exact abs_le.mpr ⟨h16, h15⟩
        have h_py_bound1 : |p 1| ≤ Real.sqrt 2 := hpy
        have h_py_bound0 : |p0 1| ≤ Real.sqrt 2 := hpy0
        have h_abs1 : |a ℓ * p 1 - a ℓ0 * p0 1| ≤
            |a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1| := by
          calc |a ℓ * p 1 - a ℓ0 * p0 1|
            = |a ℓ * (p 1 - p0 1) + (a ℓ - a ℓ0) * p0 1| := by ring_nf
          _ ≤ |a ℓ * (p 1 - p0 1)| + |(a ℓ - a ℓ0) * p0 1| := by
            exact DiscretisedFurstenbergEstimate.real_abs_add (a ℓ * (p.ofLp 1 - p0.ofLp 1)) ((a ℓ - a ℓ0) * p0.ofLp 1)
          _ = |a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1| := by
            rw [abs_mul, abs_mul]
        have h_abs2 : |a ℓ| ≤ 1 := hS_a ℓ hℓ_in_S
        have h_eq1 : b ℓ - b0 = (b ℓ - (p 0 - a ℓ * p 1)) + ((p 0 - a ℓ * p 1) - b0) := by
          simp [b0] <;> ring
        have h_main_ineq : |b ℓ - b0| ≤ (C_strip + 2 + Real.sqrt 2 / 20) * Δ := by
          calc |b ℓ - b0|
            = |(b ℓ - (p 0 - a ℓ * p 1)) + ((p 0 - a ℓ * p 1) - b0)| := by rw [h_eq1]
          _ ≤ |b ℓ - (p 0 - a ℓ * p 1)| + |(p 0 - a ℓ * p 1) - b0| := by
            exact DiscretisedFurstenbergEstimate.real_abs_add (b ℓ - (p.ofLp 0 - a ℓ * p.ofLp 1))
              (p.ofLp 0 - a ℓ * p.ofLp 1 - b0)
          _ ≤ C_strip * Δ + |(p 0 - a ℓ * p 1) - (p0 0 - a ℓ0 * p0 1)| := by
            have h_close' : |b ℓ - (p 0 - a ℓ * p 1)| ≤ C_strip * Δ := h_close
            gcongr
          _ ≤ C_strip * Δ + (|p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1|) := by
            have h : (p 0 - a ℓ * p 1) - (p0 0 - a ℓ0 * p0 1) = (p 0 - p0 0) - (a ℓ * p 1 - a ℓ0 * p0 1) := by ring
            have h2 : |(p 0 - a ℓ * p 1) - (p0 0 - a ℓ0 * p0 1)| ≤ |p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1| := by
              rw [h]
              exact DiscretisedFurstenbergEstimate.real_abs_sub (p.ofLp 0 - p0.ofLp 0) (a ℓ * p.ofLp 1 - a ℓ0 * p0.ofLp 1)
            have h_goal : C_strip * Δ + |(p 0 - a ℓ * p 1) - (p0 0 - a ℓ0 * p0 1)| ≤
                C_strip * Δ + (|p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1|) := by
              have h_comm1 : C_strip * Δ + |(p 0 - a ℓ * p 1) - (p0 0 - a ℓ0 * p0 1)| =
                  |(p 0 - a ℓ * p 1) - (p0 0 - a ℓ0 * p0 1)| + C_strip * Δ := by ring
              have h_comm2 : C_strip * Δ + (|p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1|) =
                  |p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1| + C_strip * Δ := by ring
              rw [h_comm1, h_comm2]
              exact add_le_add_left h2 (C_strip * Δ)
            exact h_goal
          _ ≤ C_strip * Δ + (Δ + (|a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1|)) := by
            have h3 : |p 0 - p0 0| ≤ Δ := h_p1_diff
            have h4 : |a ℓ * p 1 - a ℓ0 * p0 1| ≤ |a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1| := h_abs1
            have h5 : |p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1| ≤ Δ + (|a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1|) := by
              calc |p 0 - p0 0| + |a ℓ * p 1 - a ℓ0 * p0 1|
                ≤ Δ + |a ℓ * p 1 - a ℓ0 * p0 1| := by linarith
              _ ≤ Δ + (|a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1|) := by linarith
            linarith
          _ ≤ C_strip * Δ + (Δ + (1 * Δ + w * Real.sqrt 2)) := by
            have h5 : |a ℓ| ≤ 1 := h_abs2
            have h6 : |p 1 - p0 1| ≤ Δ := h_p2_diff
            have h7 : |a ℓ - a ℓ0| < w := h_a_close
            have h8 : |p0 1| ≤ Real.sqrt 2 := h_py_bound0
            have h91 : |a ℓ| * |p 1 - p0 1| ≤ 1 * Δ := by
              calc |a ℓ| * |p 1 - p0 1| ≤ 1 * |p 1 - p0 1| := by gcongr
                _ ≤ 1 * Δ := by gcongr
            have h92 : |a ℓ - a ℓ0| * |p0 1| ≤ w * Real.sqrt 2 := by
              calc |a ℓ - a ℓ0| * |p0 1| ≤ |a ℓ - a ℓ0| * Real.sqrt 2 := by gcongr
                _ ≤ w * Real.sqrt 2 := by
                  have h93 : |a ℓ - a ℓ0| < w := h7
                  have h94 : |a ℓ - a ℓ0| * Real.sqrt 2 ≤ w * Real.sqrt 2 := by
                    exact mul_le_mul_of_nonneg_right h93.le (by positivity)
                  exact h94
            have h9 : |a ℓ| * |p 1 - p0 1| + |a ℓ - a ℓ0| * |p0 1| ≤ 1 * Δ + w * Real.sqrt 2 := by
              linarith
            linarith
          _ = (C_strip + 2 + Real.sqrt 2 / 20) * Δ := by
            have h_w_def : w = Δ / 20 := by rfl
            rw [h_w_def]
            <;> ring_nf <;> field_simp <;> ring
        have h_final : (C_strip + 2 + Real.sqrt 2 / 20) * Δ ≤ (2 * C_strip + 5) * Δ := by
          have h_ineq : C_strip + 2 + Real.sqrt 2 / 20 ≤ 2 * C_strip + 5 := by
            have h1 : 0 ≤ C_strip := hC_nonneg
            have h2 : Real.sqrt 2 / 20 ≤ 1 := by
              have h3 : Real.sqrt 2 ≤ 2 := by
                nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              linarith
            linarith
          exact mul_le_mul_of_nonneg_right h_ineq hΔ_pos.le
        exact le_trans h_main_ineq h_final
      let b_set : Finset ℝ := S_k.image b
      have h_b_set_sub : (b_set : Set ℝ) ⊆
          Set.Icc (b0 - (2 * C_strip + 5) * Δ) (b0 + (2 * C_strip + 5) * Δ) := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨ℓ, hℓ, rfl⟩
        have h : |b ℓ - b0| ≤ (2 * C_strip + 5) * Δ := h_b_interval ℓ hℓ
        have h' : b0 - (2 * C_strip + 5) * Δ ≤ b ℓ := by
          linarith [abs_le.mp h]
        have h'' : b ℓ ≤ b0 + (2 * C_strip + 5) * Δ := by
          linarith [abs_le.mp h]
        exact ⟨h', h''⟩
      have h_b_set_sep : ∀ x ∈ b_set, ∀ y ∈ b_set, x ≠ y → (Δ / 10 : ℝ) ≤ |x - y| := by
        intro x hx y hy hne
        rcases Finset.mem_image.mp hx with ⟨ℓx, hℓx, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨ℓy, hℓy, rfl⟩
        have hℓx_in_S : ℓx ∈ S := (Finset.mem_filter.mp hℓx).1
        have hℓy_in_S : ℓy ∈ S := (Finset.mem_filter.mp hℓy).1
        have h_ne' : ℓx ≠ ℓy := by
          intro h
          rw [h] at hne
          exact hne rfl
        have h_dist : Δ ≤ dist ℓx ℓy := hS_sep hℓx_in_S hℓy_in_S h_ne'
        have h_antilip' : dist ℓx ℓy ≤ 10 * dist (a ℓx, b ℓx) (a ℓy, b ℓy) :=
          h_antilip ℓx ℓy hℓx_in_S hℓy_in_S
        have h_param_sep : (Δ / 10 : ℝ) ≤ dist (a ℓx, b ℓx) (a ℓy, b ℓy) := by
          linarith
        have h_a_close : |a ℓx - a ℓy| < Δ / 10 := by
          have h_kx : k ℓx = ki := (Finset.mem_filter.mp hℓx).2
          have h_ky : k ℓy = ki := (Finset.mem_filter.mp hℓy).2
          have h_same : k ℓx = k ℓy := by rw [h_kx, h_ky]
          have h1 : (k ℓx : ℝ) ≤ (a ℓx + 1) / w := Int.floor_le _
          have h2 : (a ℓx + 1) / w < (k ℓx : ℝ) + 1 := Int.lt_floor_add_one _
          have h3 : (k ℓy : ℝ) ≤ (a ℓy + 1) / w := Int.floor_le _
          have h4 : (a ℓy + 1) / w < (k ℓy : ℝ) + 1 := Int.lt_floor_add_one _
          have h_same' : (k ℓx : ℝ) = (k ℓy : ℝ) := by exact_mod_cast h_same
          have h5 : (a ℓx + 1) / w - (a ℓy + 1) / w < 1 := by linarith
          have h6 : (a ℓy + 1) / w - (a ℓx + 1) / w < 1 := by linarith
          have h7 : |(a ℓx + 1) / w - (a ℓy + 1) / w| < 1 := by
            rw [abs_lt] <;> constructor <;> linarith
          have h8 : (a ℓx + 1) / w - (a ℓy + 1) / w = (a ℓx - a ℓy) / w := by ring
          rw [h8] at h7
          have h9 : |(a ℓx - a ℓy) / w| < 1 := h7
          have h10 : |a ℓx - a ℓy| / w < 1 := by
            have h11 : |(a ℓx - a ℓy) / w| = |a ℓx - a ℓy| / w := by
              rw [abs_div] <;> rw [abs_of_pos hw_pos]
            rw [h11] at h9 <;> exact h9
          have h12 : |a ℓx - a ℓy| < w := (div_lt_one hw_pos).mp h10
          linarith [h_w_le]
        have h_b_sep : (Δ / 10 : ℝ) ≤ |b ℓx - b ℓy| := by
          have h10 : dist (a ℓx, b ℓx) (a ℓy, b ℓy) =
              max (dist (a ℓx) (a ℓy)) (dist (b ℓx) (b ℓy)) := by
            simp [Prod.dist_eq]
            <;> rfl
          rw [h10] at h_param_sep
          have h11 : dist (a ℓx) (a ℓy) = |a ℓx - a ℓy| := by
            simp [Real.dist_eq]
          have h12 : dist (b ℓx) (b ℓy) = |b ℓx - b ℓy| := by
            simp [Real.dist_eq]
          rw [h11, h12] at h_param_sep
          have h13 : |a ℓx - a ℓy| < Δ / 10 := h_a_close
          by_contra h14
          have h15 : max (|a ℓx - a ℓy|) (|b ℓx - b ℓy|) < Δ / 10 := by
            rw [max_lt_iff] <;> constructor <;> linarith
          linarith
        simpa using h_b_sep
      let W : ℝ := (2 * C_strip + 5) * Δ
      have hW_nonneg : 0 ≤ W := by positivity
      have h_b_set_sub' : (b_set : Set ℝ) ⊆ Set.Icc (b0 - W) (b0 - W + 2 * W) := by
        have h_eq : (b0 - W + 2 * W) = b0 + W := by ring
        rw [h_eq]
        exact h_b_set_sub
      have h_interval_len : 0 ≤ 2 * W := by positivity
      have h_b_card : (b_set.card : ℝ) ≤ (2 * W) / (Δ / 10) + 1 :=
        one_d_packing (show (0 : ℝ) < Δ / 10 by positivity) h_interval_len h_b_set_sub' h_b_set_sep
      have h_inj : Set.InjOn b (S_k : Set AffineLine) := by
        intro x hx y hy h_eq
        by_contra h_ne
        have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
        have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
        have h_dist : Δ ≤ dist x y := hS_sep hxS hyS h_ne
        have h_antilip' : dist x y ≤ 10 * dist (a x, b x) (a y, b y) :=
          h_antilip x y hxS hyS
        have h_kx : k x = ki := (Finset.mem_filter.mp hx).2
        have h_ky : k y = ki := (Finset.mem_filter.mp hy).2
        have h_same : k x = k y := by rw [h_kx, h_ky]
        have h_a_close : |a x - a y| < w := by
          have h1 : (k x : ℝ) ≤ (a x + 1) / w := Int.floor_le _
          have h2 : (a x + 1) / w < (k x : ℝ) + 1 := Int.lt_floor_add_one _
          have h3 : (k y : ℝ) ≤ (a y + 1) / w := Int.floor_le _
          have h4 : (a y + 1) / w < (k y : ℝ) + 1 := Int.lt_floor_add_one _
          have h_same' : (k x : ℝ) = (k y : ℝ) := by exact_mod_cast h_same
          have h5 : |(a x + 1) / w - (a y + 1) / w| < 1 := by
            rw [abs_lt] <;> constructor <;> linarith
          have h6 : (a x + 1) / w - (a y + 1) / w = (a x - a y) / w := by ring
          rw [h6] at h5
          have h7 : |(a x - a y) / w| < 1 := h5
          have h8 : |a x - a y| / w < 1 := by
            have h9 : |(a x - a y) / w| = |a x - a y| / w := by
              rw [abs_div] <;> rw [abs_of_pos hw_pos]
            rw [h9] at h7 <;> exact h7
          exact (div_lt_one hw_pos).mp h8
        have h_a_lt : |a x - a y| < Δ / 10 := by linarith [h_w_le]
        have h_param_dist : dist (a x, b x) (a y, b y) = max (|a x - a y|) (|b x - b y|) := by
          simp [Prod.dist_eq, Real.dist_eq] <;> rfl
        rw [h_param_dist] at h_antilip'
        have h11 : |b x - b y| = 0 := by rw [h_eq] <;> simp
        rw [h11] at h_antilip'
        have h9 : max (|a x - a y|) 0 = |a x - a y| := by
          rw [max_eq_left] <;> exact abs_nonneg _
        rw [h9] at h_antilip'
        have h_contra : dist x y < Δ := by
          have h1 : dist x y ≤ 10 * |a x - a y| := h_antilip'
          have h2 : |a x - a y| < Δ / 10 := h_a_lt
          have h3 : 10 * |a x - a y| < 10 * (Δ / 10) :=
            mul_lt_mul_of_pos_left h2 (by norm_num)
          have h4 : 10 * (Δ / 10) = Δ := by
            field_simp [hΔ_pos.ne'] <;> ring
          calc dist x y ≤ 10 * |a x - a y| := h1
          _ < 10 * (Δ / 10) := h3
          _ = Δ := h4
        exact False.elim (not_le.mpr h_contra h_dist)
      have h_card_eq : b_set.card = S_k.card := by
        apply Finset.card_image_of_injOn
        exact h_inj
      rw [h_card_eq] at h_b_card
      have h_final : (S_k.card : ℝ) ≤ K_b := by
        have h_simp : (2 * W) / (Δ / 10) + 1 = 40 * C_strip + 101 := by
          simp [W]
          <;> field_simp [hΔ_pos.ne'] <;> ring
        rw [h_simp] at h_b_card
        have h_ineq : (S_k.card : ℝ) ≤ 40 * C_strip + 101 := h_b_card
        have h_K_b : (40 * C_strip + 101 : ℝ) ≤ K_b := by
          dsimp only [K_b] <;> linarith
        exact le_trans h_ineq h_K_b
      exact_mod_cast h_final
  let K_int : ℤ := Int.floor (40 / Δ) + 1
  have h_k_bound : ∀ ℓ ∈ S, k ℓ ∈ Finset.Icc 0 K_int := by
    intro ℓ hℓ
    have h1 : 0 ≤ k ℓ := (h_k_range ℓ hℓ).1
    have h2 : (k ℓ : ℝ) ≤ 40 / Δ := (h_k_range ℓ hℓ).2
    have h3 : k ℓ ≤ Int.floor (40 / Δ) := Int.le_floor.mpr h2
    have h4 : k ℓ ≤ K_int := by
      dsimp only [K_int]
      linarith
    simp only [Finset.mem_Icc]
    exact ⟨h1, h4⟩
  let usedKs : Finset ℤ := S.image k
  have h_usedKs_sub : usedKs ⊆ Finset.Icc 0 K_int := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨ℓ, hℓ, rfl⟩
    exact h_k_bound ℓ hℓ
  have h_floor_nonneg2 : 0 ≤ Int.floor (40 / Δ) := by
    apply Int.floor_nonneg.mpr
    positivity
  have hK_int_nonneg : 0 ≤ K_int := by
    dsimp only [K_int]
    linarith [h_floor_nonneg2]
  have h_usedKs_card : (usedKs.card : ℝ) ≤ 42 / Δ := by
    have h1 : usedKs.card ≤ (Finset.Icc 0 K_int).card := Finset.card_le_card h_usedKs_sub
    have h2 : (Finset.Icc 0 K_int).card = K_int.toNat + 1 := by
      simp [hK_int_nonneg, Finset.Icc_eq_empty_of_lt] <;> omega
    have h3 : (K_int.toNat : ℤ) = K_int := by
      rw [Int.toNat_of_nonneg hK_int_nonneg]
    have h4 : (K_int.toNat : ℝ) = (K_int : ℝ) := by exact_mod_cast h3
    have h5 : (K_int : ℝ) ≤ 40 / Δ + 1 := by
      have hK_int_def : K_int = Int.floor (40 / Δ) + 1 := by rfl
      rw [hK_int_def]
      have h6 : (Int.floor (40 / Δ) : ℝ) ≤ 40 / Δ := Int.floor_le _
      have h7 : ((Int.floor (40 / Δ) + 1 : ℤ) : ℝ) = (Int.floor (40 / Δ) : ℝ) + 1 := by
        simp
      rw [h7]
      linarith
    have h7 : (usedKs.card : ℝ) ≤ (K_int.toNat : ℝ) + 1 := by
      rw [h2] at h1
      exact_mod_cast h1
    have h8 : (K_int.toNat : ℝ) + 1 ≤ 40 / Δ + 2 := by
      rw [h4]
      linarith
    have h9 : 40 / Δ + 2 ≤ 42 / Δ := by
      have h10 : Δ ≤ 1 := by linarith
      have h11 : 2 / Δ ≥ 2 := by
        have h12 : 2 / Δ ≥ 2 / 1 := by gcongr
        simpa using h12
      have h13 : 40 / Δ + 2 ≤ 40 / Δ + 2 / Δ := by gcongr
      have h14 : 40 / Δ + 2 / Δ = 42 / Δ := by
        field_simp [hΔ_pos.ne'] <;> ring
      exact le_trans h13 (by rw [h14])
    have h_final : (usedKs.card : ℝ) ≤ 42 / Δ := by
      calc (usedKs.card : ℝ)
        ≤ (K_int.toNat : ℝ) + 1 := h7
      _ ≤ 40 / Δ + 2 := h8
      _ ≤ 42 / Δ := h9
    exact h_final
  have h_disj : Set.PairwiseDisjoint (usedKs : Set ℤ) (fun ki : ℤ => S.filter (fun ℓ => k ℓ = ki)) := by
    intro ki1 hki1 ki2 hki2 hne
    simp only [Finset.disjoint_left]
    intro ℓ hℓ1 hℓ2
    have h1 : k ℓ = ki1 := (Finset.mem_filter.mp hℓ1).2
    have h2 : k ℓ = ki2 := (Finset.mem_filter.mp hℓ2).2
    have h3 : ki1 = ki2 := by rw [←h1, h2]
    exact hne h3
  have h_part : S = usedKs.biUnion (fun ki => S.filter (fun ℓ => k ℓ = ki)) := by
    ext ℓ
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hℓ
      exact ⟨k ℓ, Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩, ⟨hℓ, rfl⟩⟩
    · rintro ⟨ki, _, ⟨hℓ, rfl⟩⟩
      exact hℓ
  have h_sum : (S.card : ℝ) ≤ ∑ ki ∈ usedKs, ((S.filter (fun ℓ => k ℓ = ki)).card : ℝ) := by
    have h1 : S = usedKs.biUnion (fun ki => S.filter (fun ℓ => k ℓ = ki)) := h_part
    have h2 : (usedKs.biUnion (fun ki => S.filter (fun ℓ => k ℓ = ki))).card ≤
        ∑ ki ∈ usedKs, (S.filter (fun ℓ => k ℓ = ki)).card := Finset.card_biUnion_le
    have h3 : S.card = (usedKs.biUnion (fun ki => S.filter (fun ℓ => k ℓ = ki))).card := by
      exact congr_arg Finset.card h1
    rw [h3]
    exact_mod_cast h2
  have h_each : ∀ ki ∈ usedKs, ((S.filter (fun ℓ => k ℓ = ki)).card : ℝ) ≤ K_b := by
    intro ki _
    exact h_main ki
  calc (S.card : ℝ)
    ≤ ∑ ki ∈ usedKs, ((S.filter (fun ℓ => k ℓ = ki)).card : ℝ) := h_sum
  _ ≤ ∑ _ki ∈ usedKs, K_b := by
    apply Finset.sum_le_sum
    intro ki hki
    exact h_each ki hki
  _ = (usedKs.card : ℝ) * K_b := by
    simp [Finset.sum_const] <;> ring
  _ ≤ (42 / Δ) * K_b := by gcongr
  _ = (42 : ℝ) * (40 * C_strip + 110) / Δ := by ring

end DirecretisedFurstenbergEstimate.AppendixA.A2
