module

/-
  Heavy square refinement and energy bound lemmas.

  ## Main results

  1. `pair_energy_bound`: pair energy of a (Δ,t)-non-concentrated set
     is bounded by C * |S|² * log(1/Δ).

  Whiteprint: heavy_squares (energy sub-part)
  Dependencies: EnergyBoundPlane, CoveringUtils
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyBoundPlane
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.Lagoon

open DirecretisedFurstenbergEstimate

/-! ### Pair energy bound for non-concentrated sets -/

/-- Helper: (a*2)^t * a^(-t) = 2^t for a > 0. -/
lemma rpow_double_cancel {a t : ℝ} (ha : 0 < a) :
    Real.rpow (a * 2) t * Real.rpow a (-t) = (2 : ℝ)^t := by
  have h1 : Real.rpow (a * 2) t = Real.rpow a t * (2 : ℝ)^t := by
    have h_comm : a * 2 = (2 : ℝ) * a := by ring
    rw [h_comm]
    have h_mul : Real.rpow ((2 : ℝ) * a) t = (2 : ℝ)^t * Real.rpow a t :=
      Real.mul_rpow (by positivity) (by positivity)
    rw [h_mul] <;> ring
  rw [h1]
  have h2 : Real.rpow a t * Real.rpow a (-t) = 1 := by
    have h3 : Real.rpow a t * Real.rpow a (-t) = Real.rpow a (t + (-t)) :=
      (Real.rpow_add ha t (-t)).symm
    rw [h3]
    have h4 : t + (-t) = 0 := by ring
    rw [h4]
    simp
  have h_goal : Real.rpow a t * (2 : ℝ)^t * Real.rpow a (-t) = (2 : ℝ)^t := by
    have h_comm : Real.rpow a t * (2 : ℝ)^t * Real.rpow a (-t) =
        (Real.rpow a t * Real.rpow a (-t)) * (2 : ℝ)^t := by ring
    rw [h_comm, h2] <;> ring
  exact h_goal

/-- Helper: 2^(log2 x) = x for x > 0. -/
lemma two_rpow_log2 {x : ℝ} (hx : 0 < x) :
    (2 : ℝ)^(Real.log x / Real.log 2) = x := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log ((2 : ℝ)^(Real.log x / Real.log 2)) = Real.log x := by
    rw [Real.log_rpow (by norm_num)]
    <;> field_simp [h_log2_pos.ne'] <;> ring
  have h2 : 0 < (2 : ℝ)^(Real.log x / Real.log 2) := by positivity
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr h2) (Set.mem_Ioi.mpr hx) h1

/-- Helper: 1 ≤ 2^n for n : ℕ. -/
lemma one_le_two_rpow_nat (n : ℕ) : (1 : ℝ) ≤ (2 : ℝ)^(n : ℝ) := by
  have h₁ : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h₂ : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
  have h₃ : (1 : ℝ)^(n : ℝ) ≤ (2 : ℝ)^(n : ℝ) :=
    Real.rpow_le_rpow (by norm_num) h₂ h₁
  simpa using h₃

/-- Helper: 2^a ≤ 2^b for a ≤ b. -/
lemma two_rpow_mono {a b : ℝ} (h : a ≤ b) : (2 : ℝ)^a ≤ (2 : ℝ)^b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- Pair energy bound for a (Δ,t)-non-concentrated set.

  If `S` is Δ-separated and satisfies `|S ∩ B(x,r)| ≤ C * r^t * |S|` for all `r ≥ Δ`,
  and `S` has diameter ≤ `R`, then:
  `pairEnergy(t)(S) ≤ C * 2^t * |S|² * (ceil(log(R/Δ)/log 2) + 1) + |S|²`

  The logarithmic factor comes from the dyadic annulus decomposition.
-/
lemma pair_energy_bound {X : Type*} [MetricSpace X] [DecidableEq X]
    {Δ t C R : ℝ} (hΔ_pos : 0 < Δ) (ht_pos : 0 < t) (hC_pos : 0 < C)
    (hR_pos : 0 < R) (hΔ_le_R : Δ ≤ R)
    {S : Finset X}
    (hS_sep : Set.Pairwise (S : Set X) (fun x y => Δ ≤ dist x y))
    (hS_ball : ∀ (x : X) (r : ℝ), Δ ≤ r →
      ((S.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ C * r^t * (S.card : ℝ))
    (hS_diam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R) :
    pairEnergy t S ≤ C * (2 : ℝ)^t * (S.card : ℝ)^2 *
        ((Nat.ceil (Real.log (R / Δ) / Real.log 2) : ℝ) + 1) := by
  let K : ℕ := Nat.ceil (Real.log (R / Δ) / Real.log 2) + 1
  have hK_pos : 0 < K := by positivity
  have hR_div_pos : 0 < R / Δ := by positivity
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK_cover : (2 : ℝ)^((K : ℝ) - 1) ≥ R / Δ := by
    have h1 : (K : ℝ) - 1 = (Nat.ceil (Real.log (R / Δ) / Real.log 2) : ℝ) := by
      simp [K] <;> norm_cast
    rw [h1]
    have h2 : (Nat.ceil (Real.log (R / Δ) / Real.log 2) : ℝ) ≥
        Real.log (R / Δ) / Real.log 2 := Nat.le_ceil _
    have h3 : (2 : ℝ)^(Nat.ceil (Real.log (R / Δ) / Real.log 2) : ℝ) ≥
        (2 : ℝ)^(Real.log (R / Δ) / Real.log 2) := two_rpow_mono h2
    rw [two_rpow_log2 hR_div_pos] at h3
    exact h3

  have h_point : ∀ (x : X), x ∈ S → pointEnergy t S x ≤
      C * (2 : ℝ)^t * (S.card : ℝ) * (K : ℝ) := by
    intro x hx
    -- All points in S.erase x are at distance ≥ Δ by separation.
    let far := S.filter (fun y => Δ ≤ dist x y)
    have h_erase_eq_far : S.erase x = far := by
      ext y
      have h1 : y ∈ S.erase x ↔ y ∈ S ∧ y ≠ x := by
        simp [Finset.mem_erase] <;> tauto
      have h2 : y ∈ far ↔ y ∈ S ∧ Δ ≤ dist x y := by
        simp [far, Finset.mem_filter] <;> tauto
      rw [h1, h2]
      constructor
      · rintro ⟨hy, hne⟩
        have hsep : Δ ≤ dist x y := hS_sep hx hy (Ne.symm hne)
        exact ⟨hy, hsep⟩
      · rintro ⟨hy, hsep⟩
        have hne : y ≠ x := by
          intro h_eq
          have h_dist : dist x y = 0 := by rw [h_eq] <;> simp
          rw [h_dist] at hsep
          exact not_le.mpr hΔ_pos hsep
        exact ⟨hy, hne⟩

    -- Far points covered by K dyadic annuli.
    have h_far_cover : far ⊆ Finset.biUnion (Finset.range K) (fun k =>
        S.filter (fun y => (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y ∧
          dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ)) := by
      intro y hy
      have h1 : Δ ≤ dist x y := (Finset.mem_filter.mp hy).2
      have h2 : dist x y ≤ R := hS_diam x hx y (Finset.mem_filter.mp hy).1
      have h3 : dist x y / Δ ≤ R / Δ := by gcongr
      have h_d_pos : 0 < dist x y := hΔ_pos.trans_le h1
      have h_pos_d : 0 < dist x y / Δ := div_pos h_d_pos hΔ_pos
      classical
      let k : ℕ := Nat.floor (Real.log (dist x y / Δ) / Real.log 2)
      have h_log_nonneg : 0 ≤ Real.log (dist x y / Δ) / Real.log 2 := by
        have h9 : 1 ≤ dist x y / Δ := by
          have h10 : Δ ≤ dist x y := h1
          have h11 : Δ / Δ ≤ dist x y / Δ := by gcongr
          have h12 : Δ / Δ = 1 := by field_simp [hΔ_pos.ne']
          linarith
        have h13 : 0 ≤ Real.log (dist x y / Δ) := Real.log_nonneg h9
        have h14 : 0 < Real.log 2 := h_log2_pos
        exact div_nonneg h13 h14.le
      have hk1 : (k : ℝ) ≤ Real.log (dist x y / Δ) / Real.log 2 :=
        Nat.floor_le h_log_nonneg
      have hk2 : Real.log (dist x y / Δ) / Real.log 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
      have h_k_lt_K : k < K := by
        have h5 : Real.log (dist x y / Δ) ≤ Real.log (R / Δ) :=
          Real.log_le_log (by positivity) h3
        have h6 : Real.log (dist x y / Δ) / Real.log 2 ≤ Real.log (R / Δ) / Real.log 2 := by
          gcongr
        have h7 : (k : ℝ) ≤ Real.log (R / Δ) / Real.log 2 := le_trans hk1 h6
        have h8 : k ≤ Nat.ceil (Real.log (R / Δ) / Real.log 2) := by
          exact_mod_cast le_trans h7 (Nat.le_ceil _)
        have h9 : k < Nat.ceil (Real.log (R / Δ) / Real.log 2) + 1 := Nat.lt_succ_of_le h8
        simpa [K] using h9
      have h_lower : (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y := by
        have h7 : (2 : ℝ)^(k : ℝ) ≤ dist x y / Δ := by
          calc (2 : ℝ)^(k : ℝ)
            ≤ (2 : ℝ)^(Real.log (dist x y / Δ) / Real.log 2) := two_rpow_mono hk1
          _ = dist x y / Δ := two_rpow_log2 h_pos_d
        calc (2 : ℝ)^(k : ℝ) * Δ ≤ (dist x y / Δ) * Δ := by gcongr
          _ = dist x y := by field_simp [hΔ_pos.ne'] <;> ring
      have h_upper : dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ := by
        have h7 : dist x y / Δ < (2 : ℝ)^((k : ℝ) + 1) := by
          have h8 : dist x y / Δ = (2 : ℝ)^(Real.log (dist x y / Δ) / Real.log 2) :=
            (two_rpow_log2 h_pos_d).symm
          rw [h8]
          exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hk2
        calc dist x y
          = (dist x y / Δ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
        _ < (2 : ℝ)^((k : ℝ) + 1) * Δ := by gcongr
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr h_k_lt_K, by
        simp only [Finset.mem_filter] <;> exact ⟨(Finset.mem_filter.mp hy).1, ⟨h_lower, h_upper⟩⟩⟩

    have h_annulus : ∀ (k : ℕ), k < K →
        ∑ y ∈ (S.filter (fun y => (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y ∧
            dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ)),
          Real.rpow (dist x y) (-t) ≤ C * (2 : ℝ)^t * (S.card : ℝ) := by
      intro k _
      let A_k := S.filter (fun y => (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y ∧
          dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ)
      have hA_sub : A_k ⊆ S.filter (fun y => dist x y ≤ (2 : ℝ)^((k : ℝ) + 1) * Δ) := by
        intro y hy
        have h := (Finset.mem_filter.mp hy).2
        simp only [Finset.mem_filter] <;> exact ⟨(Finset.mem_filter.mp hy).1, h.2.le⟩
      have h_r : Δ ≤ (2 : ℝ)^((k : ℝ) + 1) * Δ := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ)^((k : ℝ) + 1) := by
          have h2 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
          have h3 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
          have h4 : (1 : ℝ)^((k : ℝ) + 1) ≤ (2 : ℝ)^((k : ℝ) + 1) :=
            Real.rpow_le_rpow (by norm_num) h3 h2
          simpa using h4
        calc Δ = 1 * Δ := by ring
          _ ≤ (2 : ℝ)^((k : ℝ) + 1) * Δ := by gcongr
      have hA_card : (A_k.card : ℝ) ≤ C * ((2 : ℝ)^((k : ℝ) + 1) * Δ)^t * (S.card : ℝ) := by
        have h := hS_ball x ((2 : ℝ)^((k : ℝ) + 1) * Δ) h_r
        exact le_trans (by exact_mod_cast Finset.card_le_card hA_sub) h
      have h_bound : ∀ y ∈ A_k, Real.rpow (dist x y) (-t) ≤
          Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) := by
        intro y hy
        have h_dist : (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y :=
          (Finset.mem_filter.mp hy).2.1
        have h_pos1 : 0 < (2 : ℝ)^(k : ℝ) * Δ := by positivity
        have h_ge1 : (1 : ℝ) ≤ (2 : ℝ)^(k : ℝ) := one_le_two_rpow_nat k
        have h_Δ_le : Δ ≤ (2 : ℝ)^(k : ℝ) * Δ := by
          calc Δ = 1 * Δ := by ring
            _ ≤ (2 : ℝ)^(k : ℝ) * Δ := by gcongr
        have h_pos2 : 0 < dist x y := hΔ_pos.trans_le (h_Δ_le.trans h_dist)
        have h_t_nonneg : 0 ≤ t := by linarith
        have h1 : Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) t ≤ Real.rpow (dist x y) t :=
          Real.rpow_le_rpow (by positivity) h_dist h_t_nonneg
        have h2 : Real.rpow (dist x y) (-t) = (Real.rpow (dist x y) t)⁻¹ :=
          Real.rpow_neg h_pos2.le t
        have h3 : Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) =
            (Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) t)⁻¹ :=
          Real.rpow_neg h_pos1.le t
        rw [h2, h3]
        have h_pos3 : 0 < Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) t :=
          Real.rpow_pos_of_pos h_pos1 t
        have h_pos4 : 0 < Real.rpow (dist x y) t :=
          Real.rpow_pos_of_pos h_pos2 t
        have h_final : (Real.rpow (dist x y) t)⁻¹ ≤
            (Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) t)⁻¹ := by
          have h5 : (Real.rpow (dist x y) t)⁻¹ = 1 / (Real.rpow (dist x y) t) := by simp
          have h6 : (Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) t)⁻¹ =
              1 / (Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) t) := by simp
          rw [h5, h6]
          exact one_div_le_one_div_of_le h_pos3 h1
        exact h_final
      calc
        ∑ y ∈ A_k, Real.rpow (dist x y) (-t)
          ≤ ∑ y ∈ A_k, Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) :=
            Finset.sum_le_sum fun y hy => h_bound y hy
        _ = (A_k.card : ℝ) * Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) := by
          simp [Finset.sum_const] <;> ring
        _ ≤ C * ((2 : ℝ)^((k : ℝ) + 1) * Δ)^t * (S.card : ℝ) *
              Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) := by
          have h_rpow_nonneg : 0 ≤ Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) :=
            Real.rpow_nonneg (by positivity) _
          gcongr <;> exact h_rpow_nonneg
        _ = C * (2 : ℝ)^t * (S.card : ℝ) := by
          have h_pos2 : 0 < (2 : ℝ)^(k : ℝ) * Δ := by positivity
          have h_eq : (2 : ℝ)^((k : ℝ) + 1) * Δ = ((2 : ℝ)^(k : ℝ) * Δ) * 2 := by
            have h_exp : (2 : ℝ)^((k : ℝ) + 1) = (2 : ℝ)^(k : ℝ) * 2 := by
              rw [Real.rpow_add (by norm_num)] <;> ring
            rw [h_exp] <;> ring
          have h_goal : C * Real.rpow ((2 : ℝ)^((k : ℝ) + 1) * Δ) t * (S.card : ℝ) *
                        Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) =
                      C * (2 : ℝ)^t * (S.card : ℝ) := by
            rw [h_eq]
            have h4 : Real.rpow (((2 : ℝ)^(k : ℝ) * Δ) * 2) t *
                      Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) = (2 : ℝ)^t :=
              rpow_double_cancel h_pos2
            have h5 : C * Real.rpow (((2 : ℝ)^(k : ℝ) * Δ) * 2) t * (S.card : ℝ) *
                        Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t) =
                      C * (S.card : ℝ) * (Real.rpow (((2 : ℝ)^(k : ℝ) * Δ) * 2) t *
                        Real.rpow ((2 : ℝ)^(k : ℝ) * Δ) (-t)) := by ring
            rw [h5, h4] <;> ring
          exact h_goal

    have h_far_sum : ∑ y ∈ far, Real.rpow (dist x y) (-t) ≤
        (K : ℝ) * C * (2 : ℝ)^t * (S.card : ℝ) := by
      let bigUnion := Finset.biUnion (Finset.range K) (fun k =>
        S.filter (fun y => (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y ∧
          dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ))
      have h_nonneg : ∀ (i : X), i ∈ bigUnion → i ∉ far →
          0 ≤ Real.rpow (dist x i) (-t) :=
        fun i _ _ => Real.rpow_nonneg dist_nonneg _
      have h : ∑ y ∈ far, Real.rpow (dist x y) (-t) ≤
          ∑ y ∈ bigUnion, Real.rpow (dist x y) (-t) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_far_cover h_nonneg
      have h_disj : ∀ (i : ℕ), i ∈ Finset.range K → ∀ (j : ℕ), j ∈ Finset.range K →
          i ≠ j → Disjoint
            (S.filter (fun y => (2 : ℝ)^(i : ℝ) * Δ ≤ dist x y ∧
              dist x y < (2 : ℝ)^((i : ℝ) + 1) * Δ))
            (S.filter (fun y => (2 : ℝ)^(j : ℝ) * Δ ≤ dist x y ∧
              dist x y < (2 : ℝ)^((j : ℝ) + 1) * Δ)) := by
        intro i _ j _ hne
        simp only [Finset.disjoint_left]
        intro y hy1 hy2
        have h1 : (2 : ℝ)^(i : ℝ) * Δ ≤ dist x y := (Finset.mem_filter.mp hy1).2.1
        have h2 : dist x y < (2 : ℝ)^((i : ℝ) + 1) * Δ := (Finset.mem_filter.mp hy1).2.2
        have h3 : (2 : ℝ)^(j : ℝ) * Δ ≤ dist x y := (Finset.mem_filter.mp hy2).2.1
        have h4 : dist x y < (2 : ℝ)^((j : ℝ) + 1) * Δ := (Finset.mem_filter.mp hy2).2.2
        by_cases h : i < j
        · have h5 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h
          have h6 : (2 : ℝ)^((i : ℝ) + 1) ≤ (2 : ℝ)^(j : ℝ) := two_rpow_mono h5
          have h7 : (2 : ℝ)^((i : ℝ) + 1) * Δ ≤ (2 : ℝ)^(j : ℝ) * Δ := by gcongr
          have h8 : (2 : ℝ)^((i : ℝ) + 1) * Δ ≤ dist x y := le_trans h7 h3
          exact not_le.mpr h2 h8
        · have h7 : j < i := by omega
          have h8 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h7
          have h9 : (2 : ℝ)^((j : ℝ) + 1) ≤ (2 : ℝ)^(i : ℝ) := two_rpow_mono h8
          have h10 : (2 : ℝ)^((j : ℝ) + 1) * Δ ≤ (2 : ℝ)^(i : ℝ) * Δ := by gcongr
          have h11 : (2 : ℝ)^((j : ℝ) + 1) * Δ ≤ dist x y := le_trans h10 h1
          exact not_le.mpr h4 h11
      have h_sum_biUnion : ∑ y ∈ bigUnion, Real.rpow (dist x y) (-t) =
          ∑ k ∈ Finset.range K, ∑ y ∈ (S.filter (fun y => (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y ∧
              dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ)), Real.rpow (dist x y) (-t) := by
        exact Finset.sum_biUnion h_disj
      rw [h_sum_biUnion] at h
      calc
        ∑ y ∈ far, Real.rpow (dist x y) (-t)
          ≤ ∑ k ∈ Finset.range K, ∑ y ∈ (S.filter (fun y => (2 : ℝ)^(k : ℝ) * Δ ≤ dist x y ∧
                dist x y < (2 : ℝ)^((k : ℝ) + 1) * Δ)), Real.rpow (dist x y) (-t) := h
        _ ≤ ∑ k ∈ Finset.range K, C * (2 : ℝ)^t * (S.card : ℝ) :=
            Finset.sum_le_sum fun k hk => h_annulus k (Finset.mem_range.mp hk)
        _ = (K : ℝ) * C * (2 : ℝ)^t * (S.card : ℝ) := by
            simp [Finset.sum_const] <;> ring

    calc
      pointEnergy t S x
        = ∑ y ∈ S.erase x, Real.rpow (dist x y) (-t) := by rfl
      _ = ∑ y ∈ far, Real.rpow (dist x y) (-t) := by rw [h_erase_eq_far]
      _ ≤ (K : ℝ) * C * (2 : ℝ)^t * (S.card : ℝ) := h_far_sum
      _ = C * (2 : ℝ)^t * (S.card : ℝ) * (K : ℝ) := by ring

  calc
    pairEnergy t S
      = ∑ x ∈ S, pointEnergy t S x := by rfl
    _ ≤ ∑ x ∈ S, (C * (2 : ℝ)^t * (S.card : ℝ) * (K : ℝ)) :=
        Finset.sum_le_sum fun x hx => h_point x hx
    _ = (S.card : ℝ) * (C * (2 : ℝ)^t * (S.card : ℝ) * (K : ℝ)) := by
        simp [Finset.sum_const] <;> ring
    _ = C * (2 : ℝ)^t * (S.card : ℝ)^2 * (K : ℝ) := by ring
    _ = C * (2 : ℝ)^t * (S.card : ℝ)^2 *
          ((Nat.ceil (Real.log (R / Δ) / Real.log 2) : ℝ) + 1) := by
      have hK_def : (K : ℝ) = (Nat.ceil (Real.log (R / Δ) / Real.log 2) : ℝ) + 1 := by
        simp [K] <;> norm_cast
      rw [hK_def] <;> ring

end DirecretisedFurstenbergEstimate.Lagoon
