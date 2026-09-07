module

/-
  Config Heavy Helpers — Steps 8 & 9 for kestrel's theorem6_1_main_assembly

  Provides:
  1. `heavy_config_from_subset`: restrict NiceConfiguration P₀ to a heavy subset,
     keeping T₀/tubeFamily unchanged. Returns config_heavy + all Step 9 sub-hypotheses.
  2. `M_fiber_pos_from_upper`: prove 0 < (M_fiber : ℝ) from a fiber upper bound
     card(fiber) < 2 * M_fiber on a nonempty index set.

  Usage in assembly:
    rcases heavy_config_from_subset config P_heavy hP_heavy_sub hP_heavy_retention
        hP0_nonempty h_squares_unit h_tubes_strip h_tubes_bounded
      with ⟨config_heavy, hP0_eq, h_T0_sub, hP_heavy_nonempty', h_squares_unit', h_tubes_strip', h_tubes_bounded', h_T0_coverage⟩

    have hM_fiber_pos := M_fiber_pos_from_upper Q_heavy hQ_heavy_nonempty
      (fun Q => (P_heavy.filter (fun p => squareContained hnm p Q)).card)
      (fun Q hQ => (h_fiber_bounds Q hQ).2.2)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations

/-- Restrict a NiceConfiguration to a subset P_heavy of its P₀.

    Restricts T₀ to the union of tube families over P_heavy, ensuring every
    tube in T₀ belongs to some retained square's tubeFamily. This gives
    h_intersect coverage for all of T₀, needed for intercept bounds.

    Returns config_heavy plus all Step 9 sub-hypotheses needed by
    b1_bridge_data_helper. -/
lemma heavy_config_from_subset
    {n : ℕ} {s C₁ : ℝ} {M : ℕ}
    (config : CTNiceConfiguration n s C₁ M)
    (P_heavy : Finset (DyadicSquare n))
    (hP_heavy_sub : P_heavy ⊆ config.P₀)
    (hP_heavy_retention : (config.P₀.card : ℝ) ≤
      2 * (numDyadicLevels config.P₀.card : ℝ) * (P_heavy.card : ℝ))
    (hP0_nonempty : config.P₀.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16^n) :
    ∃ (config_heavy : CTNiceConfiguration n s C₁ M),
      config_heavy.P₀ = P_heavy ∧
      config_heavy.T₀ ⊆ config.T₀ ∧
      config_heavy.P₀.Nonempty ∧
      (∀ p ∈ config_heavy.P₀,
        0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ)) ∧
      (∀ T ∈ config_heavy.T₀,
        -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) ∧
      config_heavy.T₀.card ≤ 12 * 16^n ∧
      (∀ T ∈ config_heavy.T₀,
        ∃ (p : DyadicSquare n) (hp : p ∈ config_heavy.P₀),
          T ∈ config_heavy.tubeFamily p hp) := by
  -- P_heavy is nonempty because the retention bound is strictly positive
  have hP_heavy_nonempty : P_heavy.Nonempty := by
    by_contra h
    have h_empty : P_heavy = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at hP_heavy_retention
    have h_ret2 : (config.P₀.card : ℝ) ≤ 0 := by simpa using hP_heavy_retention
    have h_pos : (0 : ℝ) < (config.P₀.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hP0_nonempty
    exact not_le.mpr h_pos h_ret2
  -- Restricted T₀: union of tube families over P_heavy only
  let T0_heavy : Finset (DyadicTube n) :=
    P_heavy.attach.biUnion (fun p => config.tubeFamily p.val (hP_heavy_sub p.property))
  have hT0_sub : T0_heavy ⊆ config.T₀ := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨p, _, hT2⟩
    have h_sub : config.tubeFamily p.val (hP_heavy_sub p.property) ⊆ config.T₀ :=
      config.h_subset p.val (hP_heavy_sub p.property)
    exact h_sub hT2
  -- Build config_heavy by restricting P₀ and T₀
  let config_heavy : CTNiceConfiguration n s C₁ M :=
    { P₀ := P_heavy
    , T₀ := T0_heavy
    , tubeFamily := fun p hp => config.tubeFamily p (hP_heavy_sub hp)
    , h_subset := fun p hp => by
        have h : config.tubeFamily p (hP_heavy_sub hp) ⊆ T0_heavy := by
          intro T hT
          exact Finset.mem_biUnion.mpr ⟨⟨p, hp⟩, by simp, hT⟩
        exact h
    , h_size := fun p hp => config.h_size p (hP_heavy_sub hp)
    , h_delta_s_set := fun p hp => config.h_delta_s_set p (hP_heavy_sub hp)
    , h_intersect := fun p hp T hT => config.h_intersect p (hP_heavy_sub hp) T hT
    , h_tube_parameters := Bornology.IsBounded.subset config.h_tube_parameters hT0_sub
    , h_bounded := by
        have h1 : (⋃ p ∈ (P_heavy : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane)) ⊆
            (⋃ p ∈ (config.P₀ : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane)) := by
          intro x hx
          rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
          exact Set.mem_iUnion₂.mpr ⟨p, hP_heavy_sub hp, hxp⟩
        exact Bornology.IsBounded.subset config.h_bounded h1
    }
  have hP0_eq : config_heavy.P₀ = P_heavy := by rfl
  have h_nonempty' : config_heavy.P₀.Nonempty := by
    rw [hP0_eq]; exact hP_heavy_nonempty
  have h_squares_unit' : ∀ p ∈ config_heavy.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) := by
    intro p hp
    have hp' : p ∈ config.P₀ := by
      rw [hP0_eq] at hp; exact hP_heavy_sub hp
    exact h_squares_unit p hp'
  have h_tubes_strip' : ∀ T ∈ config_heavy.T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro T hT
    exact h_tubes_strip T (hT0_sub hT)
  have h_tubes_bounded' : config_heavy.T₀.card ≤ 12 * 16^n := by
    have h1 : config_heavy.T₀.card ≤ config.T₀.card := Finset.card_le_card hT0_sub
    exact le_trans h1 h_tubes_bounded
  have h_T0_sub : config_heavy.T₀ ⊆ config.T₀ := hT0_sub
  have h_T0_coverage : ∀ T ∈ config_heavy.T₀,
      ∃ (p : DyadicSquare n) (hp : p ∈ config_heavy.P₀),
        T ∈ config_heavy.tubeFamily p hp := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨p, _, hTq⟩
    have hp' : p.val ∈ config_heavy.P₀ := by
      simpa [hP0_eq] using p.property
    refine ⟨p.val, hp', ?_⟩
    exact hTq
  exact ⟨config_heavy, hP0_eq, h_T0_sub, h_nonempty', h_squares_unit', h_tubes_strip', h_tubes_bounded', h_T0_coverage⟩

/-- Prove 0 < (M_fiber : ℝ) from an upper bound card(fiber) < 2 * M_fiber
    on a nonempty index set. -/
lemma M_fiber_pos_from_upper
    {M_fiber : ℕ} {α : Type*}
    (s : Finset α) (hs_nonempty : s.Nonempty)
    (f : α → ℕ)
    (h_upper : ∀ x ∈ s, (f x : ℝ) < 2 * (M_fiber : ℝ)) :
    0 < (M_fiber : ℝ) := by
  rcases hs_nonempty with ⟨x, hx⟩
  have h1 : (f x : ℝ) < 2 * (M_fiber : ℝ) := h_upper x hx
  have h2 : (0 : ℝ) ≤ (f x : ℝ) := by positivity
  have h3 : (0 : ℝ) < 2 * (M_fiber : ℝ) := by linarith
  have h4 : (0 : ℝ) < (M_fiber : ℝ) := by linarith
  exact h4

/-- Polynomial bound on numDyadicLevels: if N ≤ 4^n, then numDyadicLevels N ≤ 2n + 2.

    Since config.P₀.card ≤ 4^n (squares live in a 2^n × 2^n grid), this gives
    a linear-in-n bound for the heavy-parent overhead factor. -/
lemma numDyadicLevels_le_linear {N n : ℕ} (hN : N ≤ 4^n) :
    numDyadicLevels N ≤ 2 * n + 2 := by
  have h1 : Nat.log 2 N ≤ Nat.log 2 (4^n) := Nat.log_mono_right hN
  have h2 : Nat.log 2 (4^n) = 2 * n := by
    have h21 : 4^n = 2^(2*n) := by
      have h : (4:ℕ)^n = (2:ℕ)^(2*n) := by
        rw [show (4:ℕ) = (2:ℕ)^2 by norm_num]
        rw [←pow_mul] <;> ring
      exact h
    rw [h21]
    rw [Nat.log_pow] <;> norm_num
  rw [h2] at h1
  dsimp only [numDyadicLevels]
  omega

/-- Polynomial bound on K_global: K_global ≤ 2 * (2700 * 3145728)^2 * (4n+7)^14.

    Combines K_B1 ≤ 2700 * 3145728 * (4n+7)^7 from the B1 bridge with
    K_global ≤ 2 * K_B1^2 from post-B1 retention. -/
lemma K_global_poly_bound
    {n : ℕ} {K_B1 K_global : ℝ}
    (hK_B1_nonneg : 0 ≤ K_B1)
    (hK_B1_bound : K_B1 ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (hK_global_bound : K_global ≤ 2 * K_B1^2) :
    K_global ≤ 2 * (2700 * 3145728)^2 * (4 * (n : ℝ) + 7)^14 := by
  calc
    K_global ≤ 2 * K_B1^2 := hK_global_bound
    _ ≤ 2 * (2700 * 3145728 * (4 * (n : ℝ) + 7)^7)^2 := by gcongr
    _ = 2 * (2700 * 3145728)^2 * (4 * (n : ℝ) + 7)^14 := by ring

/-- Card bound for NiceConfiguration P₀: at most 4^n squares.

    Follows from h_squares_unit: each square has i,j in [0, 2^n). -/
lemma config_P0_card_le_4n
    {n : ℕ} {s C₁ : ℝ} {M : ℕ}
    (config : CTNiceConfiguration n s C₁ M)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ)) :
    config.P₀.card ≤ 4^n := by
  let toPair : DiscretisedFurstenbergEstimate.DyadicSquare n → ℤ × ℤ := fun p => (p.i, p.j)
  have h_inj : Set.InjOn toPair (config.P₀ : Set _) := by
    intro p _ q _ h
    have h' : p.i = q.i ∧ p.j = q.j := by simpa [toPair, Prod.ext_iff] using h
    have h_eq : p = q := by
      cases p with | mk pi pj =>
      cases q with | mk qi qj =>
      simp [h'] at * <;> aesop
    exact h_eq
  let S : Finset (ℤ × ℤ) := Finset.Ico 0 (2^n) ×ˢ Finset.Ico 0 (2^n)
  have h1 : ∀ p ∈ config.P₀, toPair p ∈ S := by
    intro p hp
    have h2 := h_squares_unit p hp
    simp only [S, Finset.mem_product, Finset.mem_Ico] <;> exact ⟨⟨h2.1, h2.2.1⟩, ⟨h2.2.2.1, h2.2.2.2⟩⟩
  let img := config.P₀.image toPair
  have h_img_card : img.card = config.P₀.card := Finset.card_image_of_injOn h_inj
  have h_img_sub : img ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact h1 p hp
  have h3 : config.P₀.card ≤ S.card := by
    rw [←h_img_card]
    exact Finset.card_le_card h_img_sub
  have h4 : S.card = 4^n := by
    have h_card : S.card = (2^n) * (2^n) := by
      simp [S, Finset.card_product] <;> norm_cast
    rw [h_card]
    have h5 : (2^n) * (2^n) = 4^n := by
      calc (2^n) * (2^n)
        _ = 2^(n + n) := by rw [←pow_add] <;> ring
        _ = 2^(2 * n) := by rw [show n + n = 2 * n by ring]
        _ = (2^2)^n := by rw [pow_mul] <;> ring
        _ = 4^n := by norm_num
    exact h5
  rw [h4] at h3
  exact h3

/-- Intercept bound for a dyadic tube intersecting a unit-range dyadic square.

    Given a tube T intersecting a square q whose indices are in [0, 2^n),
    and |T.slope| ≤ 1, we have |T.intercept| ≤ 3.

    Proof: pick z ∈ T.toSet ∩ q.toSet. Then z 0, z 1 ∈ [0,1), and
    |z 1 - T.slope * z 0 - T.intercept| ≤ δ_n. Triangle inequality gives
    |T.intercept| ≤ |z 1| + |T.slope| * |z 0| + δ_n ≤ 1 + 1 + 1 = 3. -/
lemma tube_intercept_bound_from_intersection
    {n : ℕ} (hn_pos : 0 < n)
    (T : DiscretisedFurstenbergEstimate.DyadicTube n)
    (q : DiscretisedFurstenbergEstimate.DyadicSquare n)
    (hT_intersect : (T.toSet ∩ q.toSet).Nonempty)
    (h_q_unit : 0 ≤ q.i ∧ q.i < (2 ^ n : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ n : ℤ))
    (h_slope : |T.slope| ≤ 1) :
    |T.intercept| ≤ 3 := by
  rcases hT_intersect with ⟨z, hzT, hzq⟩
  let δn : ℝ := DiscretisedFurstenbergEstimate.dyadicDelta n
  have hδn_pos : 0 < δn := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have hδn_le_one : δn ≤ 1 := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ n := by
      have h2 : ∀ k : ℕ, 0 < k → (1 : ℝ) < (2 : ℝ) ^ k := by
        intro k hk
        induction' hk with k hk ih
        · norm_num
        · simp [pow_succ] at * <;> linarith
      exact h2 n hn_pos
    have h3 : δn = 1 / (2 : ℝ) ^ n := by rfl
    rw [h3]
    have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by linarith
    exact (div_le_one (by positivity)).mpr h4
  have h_prod : (2 ^ n : ℝ) * δn = 1 := by
    have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h_eq : δn = (1 : ℝ) / (2 ^ n : ℝ) := by rfl
    rw [h_eq]
    field_simp [h_pos.ne'] <;> ring
  have hzq1 : (q.i : ℝ) * δn ≤ z 0 := hzq.1
  have hzq2 : z 0 < ((q.i : ℝ) + 1) * δn := hzq.2.1
  have hzq3 : (q.j : ℝ) * δn ≤ z 1 := hzq.2.2.1
  have hzq4 : z 1 < ((q.j : ℝ) + 1) * δn := hzq.2.2.2
  have hz0_nonneg : 0 ≤ z 0 := by
    have h3 : 0 ≤ (q.i : ℝ) := by exact_mod_cast h_q_unit.1
    linarith [mul_nonneg h3 hδn_pos.le]
  have hz0_le_one : z 0 ≤ 1 := by
    have h4 : (q.i : ℝ) + 1 ≤ (2 ^ n : ℝ) := by exact_mod_cast h_q_unit.2.1
    have h5 : ((q.i : ℝ) + 1) * δn ≤ (2 ^ n : ℝ) * δn := by
      exact mul_le_mul_of_nonneg_right h4 hδn_pos.le
    have h6 : z 0 < (2 ^ n : ℝ) * δn := by linarith [hzq2, h5]
    rw [h_prod] at h6; linarith
  have hz0_abs : |z 0| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have hz1_nonneg : 0 ≤ z 1 := by
    have h3 : 0 ≤ (q.j : ℝ) := by exact_mod_cast h_q_unit.2.2.1
    linarith [mul_nonneg h3 hδn_pos.le]
  have hz1_le_one : z 1 ≤ 1 := by
    have h4 : (q.j : ℝ) + 1 ≤ (2 ^ n : ℝ) := by exact_mod_cast h_q_unit.2.2.2
    have h5 : ((q.j : ℝ) + 1) * δn ≤ (2 ^ n : ℝ) * δn := by
      exact mul_le_mul_of_nonneg_right h4 hδn_pos.le
    have h6 : z 1 < (2 ^ n : ℝ) * δn := by linarith [hzq4, h5]
    rw [h_prod] at h6; linarith
  have hz1_abs : |z 1| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have h_strip : |z 1 - T.slope * z 0 - T.intercept| ≤ δn := hzT
  have h1 : |T.intercept| ≤ |z 1 - T.slope * z 0| + |z 1 - T.slope * z 0 - T.intercept| := by
    let a := z 1 - T.slope * z 0
    let b := z 1 - T.slope * z 0 - T.intercept
    have h_eq : a - b = T.intercept := by ring
    have h_triangle : |a - b| ≤ |a| + |b| := by
      have h : |a - b| ≤ |a - (0 : ℝ)| + |(0 : ℝ) - b| := abs_sub_le (a := a) (b := (0 : ℝ)) (c := b)
      simpa using h
    rw [h_eq] at *
    <;> exact h_triangle
  have h2 : |z 1 - T.slope * z 0| ≤ |z 1| + |T.slope| * |z 0| := by
    have h21 : |z 1 - T.slope * z 0| ≤ |z 1| + |T.slope * z 0| := by
      exact real_abs_sub (z.ofLp 1) (T.slope * z.ofLp 0)
    have h22 : |T.slope * z 0| = |T.slope| * |z 0| := abs_mul _ _
    rw [h22] at h21
    exact h21
  have h3 : |z 1| + |T.slope| * |z 0| ≤ 2 := by
    have h4 : |T.slope| * |z 0| ≤ 1 := by
      calc |T.slope| * |z 0| ≤ 1 * |z 0| := by gcongr
        _ = |z 0| := by ring
        _ ≤ 1 := hz0_abs
    linarith [hz1_abs]
  linarith [h1, h2, h_strip, h3, hδn_le_one]

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
