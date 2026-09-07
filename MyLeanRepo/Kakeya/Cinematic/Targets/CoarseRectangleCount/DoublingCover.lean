import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# Doubling cover lemma

From a cinematic family with doubling constant D, produce a finite cover by
balls of radius r with polynomially many centers.
-/

noncomputable section

open Kakeya.Cinematic Set Finset

namespace Kakeya.Cinematic

/--
One step of the doubling iteration: given a finite cover at radius R,
produce a cover at radius R/2 with at most |C| * D centers.
-/
lemma doubling_step {family : Set C2Function} {K D : ℝ}
    (hcin : IsCinematicFamily family K D)
    (R : ℝ) (hR : 0 < R)
    (C : Finset C2Function) (hC : (C : Set C2Function) ⊆ family)
    (hcover : ∀ f ∈ family, ∃ c ∈ C, c2Distance f c ≤ R) :
    ∃ (C' : Finset C2Function),
      (C' : Set C2Function) ⊆ family ∧
      (∀ f ∈ family, ∃ c ∈ C', c2Distance f c ≤ R / 2) ∧
      (C'.card : ℝ) ≤ (C.card : ℝ) * D := by
  classical
  have hdoub := hcin.2.1
  have h_for_each : ∀ (c : C2Function), c ∈ C → ∃ (S : Finset C2Function),
      (S : Set C2Function) ⊆ family ∧
      (S.card : ℝ) ≤ D ∧
      ∀ g ∈ family, c2Distance g c ≤ R → ∃ h ∈ S, c2Distance h g ≤ R / 2 := by
    intro c hc
    have hc' : c ∈ family := hC hc
    have h := hdoub hc' R hR
    rcases h with ⟨centers, hfin, hsub, hcard, hcover'⟩
    let S : Finset C2Function := hfin.toFinset
    have hS_coe : (S : Set C2Function) = centers := by
      exact Set.Finite.coe_toFinset hfin
    have h_ncard : (S.card : ℝ) = (centers.ncard : ℝ) := by
      have h : S.card = centers.ncard := by
        rw [←hS_coe]
        simp
      exact_mod_cast h
    refine ⟨S, ?_, ?_, ?_⟩
    · simpa [hS_coe] using hsub
    · rw [h_ncard]
      exact hcard
    · intro g hg hdist
      have hdist' : c2Distance c g ≤ R := by
        have h_comm : c2Distance c g = c2Distance g c := by
          simp [c2Distance_eq_dist, dist_comm]
        rw [h_comm]
        exact hdist
      have h' := hcover' hg hdist'
      have h'' : ∃ h ∈ (S : Set C2Function), c2Distance h g ≤ R / 2 := by
        rw [hS_coe]
        exact h'
      simpa using h''
  choose S hS_sub hS_card hS_cover using h_for_each
  let S' : C2Function → Finset C2Function := fun c =>
    if h : c ∈ C then S c h else ∅
  let C' : Finset C2Function := C.biUnion S'
  refine ⟨C', ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
    have hS'c : S' c = S c hc := by
      simp [S', hc]
    rw [hS'c] at hxc
    exact hS_sub c hc hxc
  · intro f hf
    rcases hcover f hf with ⟨c, hc, hdist⟩
    have hS'c : S' c = S c hc := by simp [S', hc]
    have h' := hS_cover c hc f hf hdist
    rcases h' with ⟨h, hh, hdist2⟩
    have hdist3 : c2Distance f h ≤ R / 2 := by
      have h_comm : c2Distance f h = c2Distance h f := by
        simp [c2Distance_eq_dist, dist_comm]
      rw [h_comm]
      exact hdist2
    refine ⟨h, Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩, hdist3⟩
    rw [hS'c]
    exact hh
  · have h_card : C'.card ≤ ∑ c ∈ C, (S' c).card := Finset.card_biUnion_le
    have h_sum : (∑ c ∈ C, (S' c).card : ℝ) ≤ ∑ c ∈ C, D := by
      apply Finset.sum_le_sum
      intro i hi
      have hS'i : S' i = S i hi := by simp [S', hi]
      rw [hS'i]
      exact hS_card i hi
    have h_sum2 : (∑ c ∈ C, D : ℝ) = (C.card : ℝ) * D := by
      simp [Finset.sum_const]
      <;> ring
    calc
      (C'.card : ℝ) ≤ (∑ c ∈ C, (S' c).card : ℝ) := by exact_mod_cast h_card
      _ ≤ ∑ c ∈ C, D := h_sum
      _ = (C.card : ℝ) * D := h_sum2

/--
Iterated doubling: for any m : ℕ, there is a cover of family by ≤ D^m balls
of radius K / 2^m, with centers in family.
-/
lemma doubling_iterate {family : Set C2Function} {K D : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hcin : IsCinematicFamily family K D)
    (f0 : C2Function) (hf0 : f0 ∈ family) :
    ∀ (m : ℕ), ∃ (C : Finset C2Function),
      (C : Set C2Function) ⊆ family ∧
      (∀ f ∈ family, ∃ c ∈ C, c2Distance f c ≤ K / (2 : ℝ)^m) ∧
      (C.card : ℝ) ≤ D^m := by
  have hdiam := hcin.1
  intro m
  induction m with
  | zero =>
    have h_r0 : K / (2 : ℝ)^0 = K := by norm_num
    refine ⟨{f0}, ?_, ?_, ?_⟩
    · simp [hf0]
    · intro f hf
      refine ⟨f0, by simp, ?_⟩
      rw [h_r0]
      exact hdiam hf hf0
    · simp
  | succ m ih =>
    rcases ih with ⟨C, hC_sub, hC_cover, hC_card⟩
    have hR_pos : 0 < K / (2 : ℝ)^m := by positivity
    rcases doubling_step hcin (K / (2 : ℝ)^m) hR_pos C hC_sub hC_cover
      with ⟨C', hC'_sub, hC'_cover, hC'_card⟩
    have h_radius : K / (2 : ℝ)^(m + 1) = (K / (2 : ℝ)^m) / 2 := by
      have h_pow : (2 : ℝ)^(m + 1) = 2 * (2 : ℝ)^m := by
        simp [pow_succ] <;> ring
      rw [h_pow]
      <;> ring
    have hC'_cover2 : ∀ f ∈ family, ∃ c ∈ C', c2Distance f c ≤ K / (2 : ℝ)^(m + 1) := by
      intro f hf
      rcases hC'_cover f hf with ⟨c, hc, hdist⟩
      refine ⟨c, hc, ?_⟩
      rw [h_radius]
      exact hdist
    refine ⟨C', hC'_sub, hC'_cover2, ?_⟩
    calc
      (C'.card : ℝ) ≤ (C.card : ℝ) * D := hC'_card
      _ ≤ D^m * D := by gcongr
      _ = D^(m + 1) := by simp [pow_succ] <;> ring

/--
The doubling cover lemma: a cinematic family of diameter K with doubling
constant D can be covered by polynomially many balls of radius r.
-/
lemma doubling_cover {family : Set C2Function} {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hcin : IsCinematicFamily family K D) (r : ℝ) (hr : 0 < r) :
    ∃ (centers : Finset C2Function),
      (centers : Set C2Function) ⊆ family ∧
      (∀ f ∈ family, ∃ c ∈ centers, c2Distance f c ≤ r) ∧
      (centers.card : ℝ) ≤ D * (2 * K / r + 1) ^ (Real.log D / Real.log 2) := by
  by_cases hfam : family = ∅
  · refine ⟨∅, by simp [hfam], ?_, ?_⟩
    · intro f hf
      simp [hfam] at hf <;> tauto
    · have h_pos : 0 ≤ D * (2 * K / r + 1) ^ (Real.log D / Real.log 2) := by positivity
      simpa using h_pos
  · have hnonempty : ∃ f0, f0 ∈ family := Set.nonempty_iff_ne_empty.mpr hfam
    rcases hnonempty with ⟨f0, hf0⟩
    have hK_pos : 0 < K := by linarith
    have h_exists : ∃ m : ℕ, K / (2 : ℝ)^m ≤ r := by
      have h_arch : ∃ m : ℕ, (K / r : ℝ) ≤ (m : ℝ) := exists_nat_ge (K / r)
      rcases h_arch with ⟨m, hm⟩
      have h2 : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ)^n := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
          calc
            (↑(n + 1) : ℝ) = (n : ℝ) + 1 := by simp
            _ ≤ (2 : ℝ)^n + 1 := by linarith
            _ ≤ (2 : ℝ)^n + (2 : ℝ)^n := by
              have h : (1 : ℝ) ≤ (2 : ℝ)^n := by
                have h₁ : ∀ k : ℕ, (1 : ℝ) ≤ (2 : ℝ)^k := by
                  intro k
                  induction k with
                  | zero => norm_num
                  | succ k ih => simp [pow_succ] at * <;> linarith
                exact h₁ n
              linarith
            _ = (2 : ℝ)^(n + 1) := by simp [pow_succ] <;> ring
      have h2m := h2 m
      have h3 : (K / r : ℝ) ≤ (2 : ℝ)^m := by
        calc
          (K / r : ℝ) ≤ (m : ℝ) := hm
          _ ≤ (2 : ℝ)^m := h2m
      have h4 : K / (2 : ℝ)^m ≤ r := by
        have h5 : 0 < (2 : ℝ)^m := by positivity
        have h6 : K / (2 : ℝ)^m ≤ K / (K / r) := by
          gcongr
          <;> linarith
        have h7 : K / (K / r) = r := by
          field_simp [hK_pos.ne', hr.ne'] <;> ring
        rw [h7] at h6
        exact h6
      exact ⟨m, h4⟩
    classical
    let P : ℕ → Prop := fun m => K / (2 : ℝ)^m ≤ r
    let m : ℕ := Nat.find h_exists
    have hP_m : P m := Nat.find_spec h_exists
    have h_iter := doubling_iterate hK hD hcin f0 hf0 m
    rcases h_iter with ⟨C, hC_sub, hC_cover, hC_card⟩
    have h_cover_r : ∀ f ∈ family, ∃ c ∈ C, c2Distance f c ≤ r := by
      intro f hf
      rcases hC_cover f hf with ⟨c, hc, hdist⟩
      exact ⟨c, hc, hdist.trans hP_m⟩
    have h_bound : (C.card : ℝ) ≤ D * (2 * K / r + 1) ^ (Real.log D / Real.log 2) := by
      have h_card2 : (C.card : ℝ) ≤ D^m := hC_card
      by_cases h_m : m = 0
      · rw [h_m] at h_card2
        have h1 : (D ^ 0 : ℝ) = 1 := by simp
        rw [h1] at h_card2
        have h_logD_nonneg : 0 ≤ Real.log D := Real.log_nonneg hD
        have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h4 : 0 ≤ Real.log D / Real.log 2 := div_nonneg h_logD_nonneg h_log2_pos.le
        have h5 : 1 ≤ 2 * K / r + 1 := by
          have h51 : 0 < 2 * K / r := by positivity
          linarith
        have h6 : 1 ≤ (2 * K / r + 1) ^ (Real.log D / Real.log 2) :=
          Real.one_le_rpow h5 h4
        let X := (2 * K / r + 1) ^ (Real.log D / Real.log 2)
        have h7 : 0 ≤ X := by positivity
        have h8 : D * X ≥ X := by
          have h9 : D - 1 ≥ 0 := by linarith
          have h10 : (D - 1) * X ≥ 0 := mul_nonneg h9 h7
          linarith
        have h2 : (1 : ℝ) ≤ D * X := by
          calc
            (1 : ℝ) ≤ X := h6
            _ ≤ D * X := h8
        exact h_card2.trans h2
      · -- m > 0
        have h_m_pos : 0 < m := Nat.pos_of_ne_zero h_m
        have h_min : ¬P (m - 1) := Nat.find_min h_exists (by omega)
        have h_gt : K / (2 : ℝ)^(m - 1) > r := by simpa [P] using h_min
        have h11 : 0 < (2 : ℝ)^(m - 1) := by positivity
        have h12 : r * (2 : ℝ)^(m - 1) < K := by
          have h : K / (2 : ℝ)^(m - 1) > r := h_gt
          have h' : K > r * (2 : ℝ)^(m - 1) := by
            calc
              K = (K / (2 : ℝ)^(m - 1)) * (2 : ℝ)^(m - 1) := by
                field_simp [h11.ne'] <;> ring
              _ > r * (2 : ℝ)^(m - 1) := by gcongr
          exact h'
        have h15 : (2 : ℝ)^(m - 1) < K / r := by
          calc
            (2 : ℝ)^(m - 1)
              = (r * (2 : ℝ)^(m - 1)) / r := by field_simp [hr.ne'] <;> ring
            _ < K / r := by gcongr
        have h_eq : m = (m - 1) + 1 := by omega
        have h13 : (2 : ℝ)^m = 2 * (2 : ℝ)^(m - 1) := by
          rw [h_eq]
          simp [pow_succ] <;> ring
        have h9 : (2 : ℝ)^m < 2 * K / r := by
          rw [h13]
          have h10 : 2 * (2 : ℝ)^(m - 1) < 2 * (K / r) :=
            mul_lt_mul_of_pos_left h15 (by norm_num)
          have h11 : 2 * (K / r) = 2 * K / r := by ring
          rw [h11] at h10
          exact h10
        have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have h_logD_nonneg : 0 ≤ Real.log D := Real.log_nonneg hD
        have h_exp_nonneg : 0 ≤ Real.log D / Real.log 2 := by positivity
        have h10 : (m : ℝ) * Real.log 2 < Real.log (2 * K / r) := by
          have h11' : Real.log ((2 : ℝ)^m) = (m : ℝ) * Real.log 2 := by
            rw [Real.log_pow] <;> norm_num
          have h12 : (2 : ℝ)^m > 0 := by positivity
          rw [←h11']
          exact Real.log_lt_log h12 h9
        have h13' : (m : ℝ) < Real.log (2 * K / r) / Real.log 2 := by
          calc
            (m : ℝ) = ((m : ℝ) * Real.log 2) / Real.log 2 := by
              field_simp [h_log2_pos.ne'] <;> ring
            _ < Real.log (2 * K / r) / Real.log 2 := by gcongr
        have h14_le : (m : ℝ) ≤ Real.log (2 * K / r) / Real.log 2 := by linarith
        have h_cast : (D^m : ℝ) = D ^ (m : ℝ) := by
          simp [Real.rpow_natCast]
        have h14 : D ^ (m : ℝ) ≤ D ^ (Real.log (2 * K / r) / Real.log 2) :=
          Real.rpow_le_rpow_of_exponent_le hD h14_le
        have h14' : (D^m : ℝ) ≤ D ^ (Real.log (2 * K / r) / Real.log 2) := by
          rw [h_cast]
          exact h14
        have h_posD : 0 < D := by linarith
        have h_posx : 0 < 2 * K / r := by positivity
        have h16 : D ^ (Real.log (2 * K / r) / Real.log 2) =
            (2 * K / r) ^ (Real.log D / Real.log 2) := by
          rw [Real.rpow_def_of_pos h_posD, Real.rpow_def_of_pos h_posx]
          <;> congr 1 <;> ring
        rw [h16] at h14'
        have h17 : (2 * K / r) ^ (Real.log D / Real.log 2) ≤
            (2 * K / r + 1) ^ (Real.log D / Real.log 2) := by
          have h18 : 0 < 2 * K / r := by positivity
          have h19 : 2 * K / r ≤ 2 * K / r + 1 := by linarith
          exact Real.rpow_le_rpow (by linarith) h19 h_exp_nonneg
        let Y := (2 * K / r + 1) ^ (Real.log D / Real.log 2)
        have h21 : 0 ≤ Y := by positivity
        have h22 : D - 1 ≥ 0 := by linarith
        have h23 : (D - 1) * Y ≥ 0 := mul_nonneg h22 h21
        have h20 : Y ≤ D * Y := by linarith
        exact h_card2.trans (h14'.trans (h17.trans h20))
    exact ⟨C, hC_sub, h_cover_r, h_bound⟩

end Kakeya.Cinematic
