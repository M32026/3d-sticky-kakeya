import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Iterated doubling cover

Given a cinematic family with doubling constant `D`, any ball of radius `R`
can be covered by at most `D^k` balls of radius `R / 2^k` with centers in the
family.  A continuous version gives a polynomial bound in `R / r`.
-/

noncomputable section

namespace Kakeya.Cinematic

open Finset

/--
Iterated doubling: any `g` in the family within `R` of `f₀` is within
`R / 2^k` of some center from a set of size at most `D^k`.
-/
lemma polynomial_doubling_cover_iter
    {family : Set C2Function} {K D : ℝ}
    (hCinematic : IsCinematicFamily family K D)
    (f₀ : C2Function) (hf₀ : f₀ ∈ family)
    (R : ℝ) (hR : 0 < R) (k : ℕ) :
    ∃ (centers : Finset C2Function),
      (centers : Set C2Function) ⊆ family ∧
      (centers.card : ℝ) ≤ D ^ k ∧
      ∀ g ∈ family, c2Distance f₀ g ≤ R →
        ∃ h ∈ centers, c2Distance h g ≤ R / (2 ^ k) := by
  classical
  have hR_nonneg : 0 ≤ R := by linarith
  have hD_ge_one : 1 ≤ D := by
    rcases hCinematic.2.1 hf₀ R hR with ⟨centers, hfin, hsub, hcard, hcov⟩
    have h_f0_covered : ∃ h ∈ centers, c2Distance h f₀ ≤ R / 2 :=
      hcov hf₀ (by simpa using hR_nonneg)
    rcases h_f0_covered with ⟨h, hh, _⟩
    have h_nonempty : centers.Nonempty := ⟨h, hh⟩
    have h1 : 0 < centers.ncard :=
      Set.Nonempty.ncard_pos hfin h_nonempty
    have h2 : (1 : ℝ) ≤ (centers.ncard : ℝ) := by exact_mod_cast h1
    have h3 : (centers.ncard : ℝ) ≤ D := hcard
    linarith
  have hD_nonneg : 0 ≤ D := by linarith
  induction k with
  | zero =>
    refine' ⟨{f₀}, _, _, _⟩
    · simp only [Finset.coe_singleton, Set.singleton_subset_iff]
      exact hf₀
    · simp
    · intro g _ hdist
      refine' ⟨f₀, Finset.mem_singleton_self f₀, _⟩
      simpa using hdist
  | succ k ih =>
    rcases ih with ⟨centers_k, hsub_k, hcard_k, hcov_k⟩
    have hR_k_pos : 0 < R / (2 ^ k : ℝ) := by positivity
    choose centers_h hfin_h hsub_h hcard_h hcov_h using
      fun (h : C2Function) (hh : h ∈ centers_k) =>
        hCinematic.2.1 (hsub_k hh) (R / (2 ^ k : ℝ)) hR_k_pos
    let centers_h' : C2Function → Finset C2Function := fun h =>
      if hh : h ∈ centers_k then (hfin_h h hh).toFinset else ∅
    let centers_next : Finset C2Function :=
      centers_k.biUnion (fun h => centers_h' h)
    have h_set_eq : ∀ (h : C2Function) (hh : h ∈ centers_k),
        (centers_h' h : Set C2Function) = centers_h h hh := by
      intro h hh
      have h_def : centers_h' h = (hfin_h h hh).toFinset := by
        simp [centers_h', hh]
      ext y
      rw [h_def]
      simp
    refine' ⟨centers_next, _, _, _⟩
    · -- centers_next ⊆ family
      intro x hx
      have h_bex : ∃ (h : C2Function), h ∈ centers_k ∧ x ∈ centers_h' h :=
        Finset.mem_biUnion.mp hx
      rcases h_bex with ⟨h, hh, hx'⟩
      have h_in_coe : x ∈ (centers_h' h : Set C2Function) := hx'
      rw [h_set_eq h hh] at h_in_coe
      exact hsub_h h hh h_in_coe
    · -- card bound
      have h1 : centers_next.card ≤ ∑ h ∈ centers_k, (centers_h' h).card :=
        Finset.card_biUnion_le
      have h2 : ∀ (i : C2Function), i ∈ centers_k →
          ((centers_h' i).card : ℝ) ≤ D := by
        intro i hi
        have h_set : (centers_h' i : Set C2Function) = centers_h i hi :=
          h_set_eq i hi
        have h_card : ((centers_h' i).card : ℝ) = (centers_h i hi).ncard := by
          have h5 : ((centers_h' i).card : ℕ) = (centers_h' i : Set C2Function).ncard := by
            simp
          rw [h5, h_set]
        rw [h_card]
        exact hcard_h i hi
      have h_sum : (∑ h ∈ centers_k, (centers_h' h).card : ℝ) ≤
          ∑ h ∈ centers_k, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact h2 i hi
      have h3 : (∑ h ∈ centers_k, D : ℝ) = (centers_k.card : ℝ) * D := by
        simp [Finset.sum_const]
      have h4 : (centers_next.card : ℝ) ≤ (centers_k.card : ℝ) * D := by
        calc
          (centers_next.card : ℝ)
            ≤ (∑ h ∈ centers_k, (centers_h' h).card : ℝ) := by exact_mod_cast h1
          _ ≤ (∑ h ∈ centers_k, D : ℝ) := h_sum
          _ = (centers_k.card : ℝ) * D := h3
      have h5 : (centers_k.card : ℝ) * D ≤ (D ^ k : ℝ) * D :=
        mul_le_mul_of_nonneg_right hcard_k hD_nonneg
      have h6 : (D ^ k : ℝ) * D = D ^ (k + 1) := by
        simp [pow_succ]
      rw [h6] at h5
      exact h4.trans h5
    · -- coverage
      intro g hg hdist
      rcases hcov_k g hg hdist with ⟨h, hh, hdist_h⟩
      have h_h_in_family : h ∈ family := hsub_k hh
      rcases hcov_h h hh hg hdist_h with ⟨h', hh', hdist_h'⟩
      have h_h'_in : h' ∈ centers_next := by
        have h_in_coe : h' ∈ (centers_h' h : Set C2Function) := by
          rw [h_set_eq h hh]
          exact hh'
        exact Finset.mem_biUnion.mpr ⟨h, hh, h_in_coe⟩
      refine' ⟨h', h_h'_in, _⟩
      have h7 : R / (2 ^ (k + 1) : ℝ) = (R / (2 ^ k : ℝ)) / 2 := by
        field_simp [pow_succ] <;> ring
      rw [h7]
      exact hdist_h'

/--
Continuous version: cover a ball of radius `R` by balls of radius `r` with
at most `D * (R / r)^(Real.log D / Real.log 2)` centers.
-/
lemma polynomial_doubling_cover
    {family : Set C2Function} {K D : ℝ}
    (hCinematic : IsCinematicFamily family K D) (hD : 1 ≤ D)
    (f₀ : C2Function) (hf₀ : f₀ ∈ family)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ (centers : Finset C2Function),
      (centers : Set C2Function) ⊆ family ∧
      (centers.card : ℝ) ≤ D * Real.rpow (R / r) (Real.log D / Real.log 2) ∧
      ∀ g ∈ family, c2Distance f₀ g ≤ R →
        ∃ h ∈ centers, c2Distance h g ≤ r := by
  classical
  have hR_nonneg : 0 ≤ R := by linarith
  have hD_pos : 0 < D := by linarith
  have hRr_pos : 0 < R / r := by positivity
  have hRr_ge_one : 1 ≤ R / r := by
    calc
      1 = r / r := by field_simp [hr.ne']
      _ ≤ R / r := by gcongr
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_Rr_nonneg : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg hRr_ge_one
  let alpha : ℝ := Real.log (R / r) / Real.log 2
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg hlog_Rr_nonneg (by linarith)
  let k : ℕ := Nat.ceil alpha
  have h_k_ge : (k : ℝ) ≥ alpha := Nat.le_ceil _
  have h_k_lt : (k : ℝ) < alpha + 1 := Nat.ceil_lt_add_one halpha_nonneg
  have h_pow_ge : (2 : ℝ) ^ k ≥ R / r := by
    have h2 : (2 : ℝ) ^ alpha = R / r := by
      have h21 : Real.log ((2 : ℝ) ^ alpha) = Real.log (R / r) := by
        rw [Real.log_rpow (by norm_num)]
        dsimp only [alpha]
        field_simp [hlog2_pos.ne']
      have h_pos1 : 0 < (2 : ℝ) ^ alpha := by positivity
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos1) (Set.mem_Ioi.mpr hRr_pos) h21
    have h3 : (2 : ℝ) ^ alpha ≤ (2 : ℝ) ^ (k : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · norm_num
      · exact h_k_ge
    have h4 : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by norm_cast
    rw [h4] at h3
    rw [h2] at h3
    exact h3
  have h_radius_le : R / (2 ^ k : ℝ) ≤ r := by
    have h4 : R / (2 ^ k : ℝ) ≤ R / (R / r) := by
      apply div_le_div_of_nonneg_left hR_nonneg
      · positivity
      · exact h_pow_ge
    have h5 : R / (R / r) = r := by
      field_simp [hr.ne']
    rw [h5] at h4
    exact h4
  rcases polynomial_doubling_cover_iter hCinematic f₀ hf₀ R hR k with
    ⟨centers, hsub, hcard, hcov⟩
  have h6 : (centers.card : ℝ) ≤ D ^ k := hcard
  have h7 : (D ^ k : ℝ) = Real.rpow D (k : ℝ) := by
    simp [Real.rpow_natCast]
  have h6' : (centers.card : ℝ) ≤ Real.rpow D (k : ℝ) := by
    rw [h7] at h6
    exact h6
  have h8 : Real.rpow D (k : ℝ) ≤ Real.rpow D (alpha + 1) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    ; linarith
  have h91 : Real.rpow D (alpha + 1) = Real.rpow D alpha * Real.rpow D 1 :=
    Real.rpow_add hD_pos alpha 1
  have h92 : Real.rpow D 1 = D := by simp
  have h9 : Real.rpow D (alpha + 1) = D * Real.rpow D alpha := by
    rw [h91, h92]
    exact mul_comm _ _
  have h10 : Real.rpow D alpha = Real.rpow (R / r) (Real.log D / Real.log 2) := by
    dsimp only [alpha]
    have h13 : Real.rpow D (Real.log (R / r) / Real.log 2) =
        Real.exp (Real.log D * (Real.log (R / r) / Real.log 2)) :=
      Real.rpow_def_of_pos hD_pos (Real.log (R / r) / Real.log 2)
    have h14 : Real.rpow (R / r) (Real.log D / Real.log 2) =
        Real.exp (Real.log (R / r) * (Real.log D / Real.log 2)) :=
      Real.rpow_def_of_pos hRr_pos (Real.log D / Real.log 2)
    rw [h13, h14]
    congr 1
    have h_comm : Real.log D * (Real.log (R / r) / Real.log 2) =
        Real.log (R / r) * (Real.log D / Real.log 2) := by ring
    exact h_comm
  have h_card_final : (centers.card : ℝ) ≤
      D * Real.rpow (R / r) (Real.log D / Real.log 2) := by
    calc
      (centers.card : ℝ)
        ≤ Real.rpow D (k : ℝ) := h6'
      _ ≤ Real.rpow D (alpha + 1) := h8
      _ = D * Real.rpow D alpha := h9
      _ = D * Real.rpow (R / r) (Real.log D / Real.log 2) := by rw [h10]
  have h_cov_final : ∀ g ∈ family, c2Distance f₀ g ≤ R →
      ∃ h ∈ centers, c2Distance h g ≤ r := by
    intro g hg hdist
    rcases hcov g hg hdist with ⟨h, hh, hdist_h⟩
    refine' ⟨h, hh, _⟩
    exact hdist_h.trans h_radius_le
  exact ⟨centers, hsub, h_card_final, h_cov_final⟩

end Kakeya.Cinematic
