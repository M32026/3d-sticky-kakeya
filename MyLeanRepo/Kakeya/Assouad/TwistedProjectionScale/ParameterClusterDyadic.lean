import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Dyadic regularization lemma

Given a finite set with weights bounded between `base_mass` and
`imbalance * base_mass`, partition into dyadic levels and select the
level with the largest total weight.
-/

namespace Kakeya.Assouad

/--
Dyadic regularization: select one dyadic level of cluster masses.

Given `points` with weights `mass_fn` all in `[base_mass, imbalance * base_mass]`,
there exists a level `k` such that:
- Every selected point has weight in `[clusterMass, 2 * clusterMass)`
- The total weight of selected points is at least `total / L`,
  where `L = Nat.log 2 (2 * imbalance) + 1`.
-/
lemma dyadic_regularization
    {α : Type*} [DecidableEq α]
    (points : Finset α)
    (mass_fn : α → ENNReal)
    (base_mass : ENNReal)
    (imbalance : ℕ)
    (hpoints_nonempty : points.Nonempty)
    (hbase_pos : 0 < base_mass)
    (hbase_ne_top : base_mass ≠ ⊤)
    (himbalance_pos : 0 < imbalance)
    (hlower : ∀ p ∈ points, base_mass ≤ mass_fn p)
    (hupper : ∀ p ∈ points, mass_fn p ≤ (imbalance : ENNReal) * base_mass)
    (hmass_ne_top : ∀ p ∈ points, mass_fn p ≠ ⊤) :
    ∃ (selected : Finset α) (clusterMass : ENNReal),
      selected.Nonempty ∧
      selected ⊆ points ∧
      (∀ p ∈ selected, clusterMass ≤ mass_fn p ∧ mass_fn p ≤ 2 * clusterMass) ∧
      (∑ p ∈ points, mass_fn p) / ((Nat.log 2 (2 * imbalance) + 1 : ENNReal)) ≤
        ∑ p ∈ selected, mass_fn p := by
  let L : ℕ := Nat.log 2 (2 * imbalance) + 1
  have hL_pos : 0 < L := by positivity
  have h_ne_zero : (2 * imbalance) ≠ 0 := by omega
  have h2 : 2 * imbalance < (2 : ℕ) ^ (Nat.log 2 (2 * imbalance) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (2 * imbalance)
  have h2' : (imbalance : ENNReal) < ((2 : ℕ) ^ L : ENNReal) := by
    have h21 : imbalance ≤ 2 * imbalance := by omega
    exact_mod_cast (h21.trans_lt h2)
  have h_total_ne_top : (∑ p ∈ points, mass_fn p) ≠ ⊤ := by
    have h : ¬ ∃ p ∈ points, mass_fn p = ⊤ := by
      intro h
      rcases h with ⟨p, hp, htop⟩
      exact hmass_ne_top p hp htop
    simpa [ENNReal.sum_eq_top] using h

  let level : ℕ → Finset α := fun k =>
    points.filter fun p =>
      base_mass * (2^k : ENNReal) ≤ mass_fn p ∧
      mass_fn p < base_mass * (2^(k+1) : ENNReal)

  have h_exists_upper : ∀ (p : α), p ∈ points →
      ∃ k : ℕ, mass_fn p < base_mass * (2^(k+1) : ENNReal) := by
    intro p hp
    have h3 : mass_fn p ≤ (imbalance : ENNReal) * base_mass := hupper p hp
    have h3' : mass_fn p ≤ base_mass * (imbalance : ENNReal) := by
      have h_comm : (imbalance : ENNReal) * base_mass = base_mass * (imbalance : ENNReal) := by ring
      rw [h_comm] at h3
      exact h3
    have h_mult : base_mass * (imbalance : ENNReal) <
        base_mass * ((2 : ℕ) ^ L : ENNReal) := by
      gcongr
      <;> exact h2'
    have h4 : mass_fn p < base_mass * ((2 : ℕ) ^ L : ENNReal) :=
      h3'.trans_lt h_mult
    refine ⟨L - 1, ?_⟩
    have h5 : L - 1 + 1 = L := by omega
    rw [h5]
    exact h4

  have h_cover : ∀ p ∈ points, ∃ k ∈ Finset.range L, p ∈ level k := by
    intro p hp
    let P : ℕ → Prop := fun m =>
      mass_fn p < base_mass * (2^(m+1) : ENNReal)
    let hP : ∃ m, P m := h_exists_upper p hp
    let k : ℕ := Nat.find hP
    have hk_upper : P k := Nat.find_spec hP
    have hk_lower : base_mass * (2^k : ENNReal) ≤ mass_fn p := by
      by_cases hk0 : k = 0
      · rw [hk0]
        simpa using hlower p hp
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have h_prev : k - 1 < k := by omega
        have h_not : ¬P (k - 1) := by
          exact Nat.find_min (H := hP) (m := k - 1) h_prev
        have h_not2 : ¬(mass_fn p < base_mass * (2^k : ENNReal)) := by
          simpa [P, show (k - 1) + 1 = k by omega] using h_not
        exact not_lt.mp h_not2
    have hk_lt_L : k < L := by
      by_contra h
      have h6 : L ≤ k := by linarith
      have h7 : L - 1 < k := by omega
      have h_not : ¬P (L - 1) := by
        exact Nat.find_min (H := hP) (m := L - 1) h7
      have h_not2 : ¬(mass_fn p < base_mass * (2^L : ENNReal)) := by
        simpa [P, show (L - 1) + 1 = L by omega] using h_not
      have h_P_L1 : mass_fn p < base_mass * (2^L : ENNReal) := by
        have h3 : mass_fn p ≤ (imbalance : ENNReal) * base_mass := hupper p hp
        have h3' : mass_fn p ≤ base_mass * (imbalance : ENNReal) := by
          have h_comm : (imbalance : ENNReal) * base_mass = base_mass * (imbalance : ENNReal) := by ring
          rw [h_comm] at h3
          exact h3
        have h_mult : base_mass * (imbalance : ENNReal) <
            base_mass * ((2 : ℕ) ^ L : ENNReal) := by
          gcongr <;> exact h2'
        exact h3'.trans_lt h_mult
      exact h_not2 h_P_L1
    exact ⟨k, Finset.mem_range.mpr hk_lt_L,
      Finset.mem_filter.mpr ⟨hp, ⟨hk_lower, hk_upper⟩⟩⟩

  have h_levels_subset : ∀ k ∈ Finset.range L, level k ⊆ points := by
    intro k _
    exact Finset.filter_subset _ _

  have h_disjoint : ∀ k ∈ Finset.range L, ∀ l ∈ Finset.range L,
      k ≠ l → Disjoint (level k) (level l) := by
    intro k hk l hl hne
    simp only [Finset.disjoint_left]
    intro p hp1 hp2
    by_cases hkl : k < l
    · -- k < l
      have h3 : k + 1 ≤ l := by linarith
      have h4 : base_mass * (2^(k+1) : ENNReal) ≤ base_mass * (2^l : ENNReal) := by
        gcongr
        <;> norm_cast <;> omega
      have h5 : base_mass * (2^(k+1) : ENNReal) ≤ mass_fn p :=
        h4.trans (Finset.mem_filter.mp hp2).2.1
      have h6 : mass_fn p < base_mass * (2^(k+1) : ENNReal) :=
        (Finset.mem_filter.mp hp1).2.2
      exact (not_lt.mpr h5) h6
    · -- l < k (since k ≠ l)
      have hlk : l < k := by omega
      have h3 : l + 1 ≤ k := by linarith
      have h4 : base_mass * (2^(l+1) : ENNReal) ≤ base_mass * (2^k : ENNReal) := by
        gcongr
        <;> norm_cast <;> omega
      have h5 : base_mass * (2^(l+1) : ENNReal) ≤ mass_fn p :=
        h4.trans (Finset.mem_filter.mp hp1).2.1
      have h6 : mass_fn p < base_mass * (2^(l+1) : ENNReal) :=
        (Finset.mem_filter.mp hp2).2.2
      exact (not_lt.mpr h5) h6

  have h_bunion : (Finset.range L).biUnion level = points := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hpk⟩
      exact (Finset.mem_filter.mp hpk).1
    · intro hp
      rcases h_cover p hp with ⟨k, hk, hpk⟩
      exact ⟨k, hk, hpk⟩

  let S : ENNReal := ∑ p ∈ points, mass_fn p
  have hS_ne_top : S ≠ ⊤ := h_total_ne_top

  let level_sum : ℕ → ENNReal := fun k => ∑ p ∈ level k, mass_fn p
  have h_sum_levels : S = ∑ k ∈ Finset.range L, level_sum k := by
    rw [← Finset.sum_biUnion h_disjoint, h_bunion]
    <;> rfl

  have h_max_exists : ∃ k ∈ Finset.range L,
      ∀ l ∈ Finset.range L, level_sum l ≤ level_sum k :=
    Finset.exists_max_image (Finset.range L) level_sum (by simp [hL_pos.ne'])

  rcases h_max_exists with ⟨k, hk_range, hk_max⟩

  have hL_ne_zero : (L : ENNReal) ≠ 0 := by simp [hL_pos.ne']
  have hL_ne_top : (L : ENNReal) ≠ ⊤ := by simp

  have h_le : ∑ l ∈ Finset.range L, level_sum l ≤ (L : ENNReal) * level_sum k := by
    calc
      ∑ l ∈ Finset.range L, level_sum l
        ≤ ∑ l ∈ Finset.range L, level_sum k :=
          Finset.sum_le_sum (fun l hl => hk_max l hl)
      _ = (L : ENNReal) * level_sum k := by
        simp [Finset.sum_const, hL_pos.ne']
        <;> ring

  have hk_sum : S / (L : ENNReal) ≤ level_sum k := by
    have h : S ≤ (L : ENNReal) * level_sum k := by
      rw [h_sum_levels] <;> exact h_le
    calc
      S / (L : ENNReal) = S * (L : ENNReal)⁻¹ := by rfl
      _ ≤ ((L : ENNReal) * level_sum k) * (L : ENNReal)⁻¹ := by gcongr
      _ = level_sum k := by
        have h_cancel : (L : ENNReal) * (L : ENNReal)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hL_ne_zero hL_ne_top
        calc
          ((L : ENNReal) * level_sum k) * (L : ENNReal)⁻¹
            = (L : ENNReal) * ((L : ENNReal)⁻¹ * level_sum k) := by ring
          _ = ((L : ENNReal) * (L : ENNReal)⁻¹) * level_sum k := by ring
          _ = 1 * level_sum k := by rw [h_cancel]
          _ = level_sum k := by ring
  let selected := level k
  let clusterMass := base_mass * (2^k : ENNReal)
  have hk_sum' : S / (L : ENNReal) ≤ ∑ p ∈ selected, mass_fn p := by
    simpa [selected, level_sum] using hk_sum
  have h_selected_nonempty : selected.Nonempty := by
    by_contra h
    have h_empty : selected = ∅ := by simpa using h
    have h_sum_zero : ∑ p ∈ selected, mass_fn p = 0 := by
      rw [h_empty] <;> simp
    rw [h_sum_zero] at hk_sum'
    have hS_pos : S ≠ 0 := by
      rcases hpoints_nonempty with ⟨p, hp⟩
      have h1 : 0 < mass_fn p := hbase_pos.trans_le (hlower p hp)
      have h2 : mass_fn p ≤ S := Finset.single_le_sum (fun _ _ => by positivity) hp
      exact ne_of_gt (h1.trans_le h2)
    have h_div_zero : S / (L : ENNReal) = 0 := by simpa using hk_sum'
    have hS_zero : S = 0 := by
      simpa [div_eq_mul_inv, hL_ne_zero, hL_ne_top] using h_div_zero
    exact hS_pos hS_zero
  have h_two_sided : ∀ p ∈ selected,
      clusterMass ≤ mass_fn p ∧ mass_fn p ≤ 2 * clusterMass := by
    intro p hp
    have h6 : clusterMass ≤ mass_fn p :=
      (Finset.mem_filter.mp hp).2.1
    have h7 : mass_fn p < 2 * clusterMass := by
      have h8 := (Finset.mem_filter.mp hp).2.2
      have h9 : base_mass * (2^(k+1) : ENNReal) = 2 * clusterMass := by
        simp [clusterMass, pow_succ]
        <;> ring
      rw [h9] at h8
      exact h8
    exact ⟨h6, h7.le⟩
  have hk_sum_final : (∑ p ∈ points, mass_fn p) / ((Nat.log 2 (2 * imbalance) + 1 : ENNReal)) ≤
      ∑ p ∈ selected, mass_fn p := by
    simpa [S, L] using hk_sum'
  exact ⟨selected, clusterMass, h_selected_nonempty,
    h_levels_subset k hk_range, h_two_sided, hk_sum_final⟩

end Kakeya.Assouad
