import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Helper lemmas for WZ1 Lemma 19 (one-scale local grain)

Diameter covering bound and two-bound IsADSet1 assembly.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/-- Covering number bound from diameter in `ℝ`.

A set of diameter at most `D` can be covered by at most `2*D/t + 2` balls
of radius `t`. -/
lemma covering_by_diameter {A : Set ℝ} {t D : ℝ} (ht : 0 < t) (hD : 0 ≤ D)
    (h : ∀ x y, x ∈ A → y ∈ A → dist x y ≤ D) :
    (Metric.externalCoveringNumber ⟨t, ht.le⟩ A : ENNReal) ≤
      ENNReal.ofReal (2 * D / t + 2) := by
  by_cases hA : A = ∅
  · rw [hA]; simp
  · rcases Set.nonempty_iff_ne_empty.mpr hA with ⟨a, ha⟩
    have h1 : A ⊆ closedBall a D := by
      intro x hx; exact h x a hx ha
    by_cases hDt : D ≤ t
    · -- D ≤ t: one ball of radius t suffices (since A ⊆ B(a,D) ⊆ B(a,t))
      have h_sub : A ⊆ closedBall a t := by
        intro x hx
        have h2 : dist x a ≤ D := h x a hx ha
        exact h2.trans hDt
      have h4 : Metric.externalCoveringNumber ⟨t, ht.le⟩ A ≤ 1 := by
        have h5 : Metric.IsCover ⟨t, ht.le⟩ A ({a} : Set ℝ) := by
          intro x hx
          refine ⟨a, by simp, ?_⟩
          simpa [Set.mem_setOf_eq] using dist_le_coe.mp (h_sub hx)
        have h6 := h5.externalCoveringNumber_le_encard
        simpa using h6
      have h7 : (Metric.externalCoveringNumber ⟨t, ht.le⟩ A : ENNReal) ≤ 1 := by
        exact_mod_cast h4
      have h8 : (1 : ENNReal) ≤ ENNReal.ofReal (2 * D / t + 2) := by
        have h9 : 0 ≤ D := hD
        have h10 : (1 : ℝ) ≤ 2 * D / t + 2 := by
          have h11 : 0 ≤ 2 * D / t := by positivity
          linarith
        simpa using ENNReal.ofReal_le_ofReal h10
      exact h7.trans h8
    · -- D > t
      have hD_pos : 0 < D := by linarith
      have hDt' : t ≤ D := by linarith
      rcases real_closedBall_finer_cover a ht hD_pos hDt' with
        ⟨centers, hcard, hcover⟩
      have h3 : A ⊆ ⋃ y ∈ centers, closedBall y t := h1.trans hcover
      have h4 : Metric.IsCover ⟨t, ht.le⟩ A (centers : Set ℝ) := by
        intro x hx
        have h5 : x ∈ ⋃ y ∈ centers, closedBall y t := h3 hx
        rcases Set.mem_iUnion₂.mp h5 with ⟨y, hy, hball⟩
        refine ⟨y, hy, ?_⟩
        simpa [Set.mem_setOf_eq] using dist_le_coe.mp hball
      have h5 : Metric.externalCoveringNumber ⟨t, ht.le⟩ A ≤ (centers.card : ℕ∞) := by
        have h_main := h4.externalCoveringNumber_le_encard
        simpa using h_main
      have h6 : (centers.card : ℝ) ≤ 2 * D / t + 2 := by
        have h7 : (centers.card : ℝ) ≤ (Nat.ceil (2 * D / t) + 1 : ℝ) := by
          exact_mod_cast hcard
        have h8 : (Nat.ceil (2 * D / t) : ℝ) ≤ 2 * D / t + 1 := by
          have h9 : (Nat.ceil (2 * D / t) : ℝ) < 2 * D / t + 1 :=
            Nat.ceil_lt_add_one (by positivity)
          linarith
        linarith
      have h9 : (centers.card : ENNReal) ≤ ENNReal.ofReal (2 * D / t + 2) := by
        have h10 : (centers.card : ENNReal) = ENNReal.ofReal (centers.card : ℝ) := by simp
        rw [h10]
        exact ENNReal.ofReal_le_ofReal h6
      have h11 : (Metric.externalCoveringNumber ⟨t, ht.le⟩ A : ENNReal) ≤
          (centers.card : ENNReal) := by
        exact_mod_cast h5
      exact h11.trans h9

/-- Simple crossover lemma: if `A^(1-α) * K^α ≤ C`, then for all `u > 0`,
`min(A, K*u) ≤ C * u^α`. -/
lemma crossover_lemma (A K C u alpha : ℝ)
    (hA_pos : 0 < A) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (hu_pos : 0 < u) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (h : A^(1-alpha) * K^alpha ≤ C) :
    min A (K * u) ≤ C * u^alpha := by
  set u_star : ℝ := A / K with hu_star_def
  have h_ustar_pos : 0 < u_star := by positivity
  have h_crossover : A ≤ C * u_star^alpha := by
    have h_pos1 : 0 < A^alpha := Real.rpow_pos_of_pos hA_pos _
    have h_pos2 : 0 < K^alpha := Real.rpow_pos_of_pos hK_pos _
    have h_nonneg1 : 0 ≤ A / K := by positivity
    have h_nonneg2 : 0 ≤ K := by positivity
    have h13 : (A / K)^alpha * K^alpha = A^alpha := by
      have h14 : (A / K)^alpha * K^alpha = ((A / K) * K)^alpha := by
        rw [← Real.mul_rpow h_nonneg1 h_nonneg2] <;> ring
      rw [h14]
      have h15 : (A / K) * K = A := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h15] <;> rfl
    have h4 : A * K^alpha ≤ C * A^alpha := by
      have h5 : A^(1-alpha) * A^alpha = A := by
        have h6 : A^(1-alpha) * A^alpha = A^((1-alpha)+alpha) := by
          rw [← Real.rpow_add hA_pos]
        rw [h6]
        have h7 : (1-alpha)+alpha = 1 := by ring
        rw [h7]
        exact Real.rpow_one A
      have h6 : A * K^alpha = (A^(1-alpha) * K^alpha) * A^alpha := by
        calc
          A * K^alpha = (A^(1-alpha) * A^alpha) * K^alpha := by rw [h5] <;> ring
          _ = (A^(1-alpha) * K^alpha) * A^alpha := by ring
      rw [h6]
      have h7 : A^(1-alpha) * K^alpha ≤ C := h
      have h8 : (A^(1-alpha) * K^alpha) * A^alpha ≤ C * A^alpha := by
        gcongr
      exact h8
    have h9 : A * K^alpha ≤ (C * (A / K)^alpha) * K^alpha := by
      rw [mul_assoc, h13]
      exact h4
    have h10 : A ≤ C * (A / K)^alpha := by
      have h11 : 0 < K^alpha := h_pos2
      nlinarith
    dsimp only [u_star]
    exact h10
  by_cases h_case : u ≥ u_star
  · have h10 : A ≤ C * u^alpha := by
      calc A ≤ C * u_star^alpha := h_crossover
           _ ≤ C * u^alpha := by
             gcongr
    exact (min_le_left _ _).trans h10
  · have h_case' : u < u_star := by linarith
    have h11 : K * u < A := by
      have h12 : K * u_star = A := by
        dsimp only [u_star]; field_simp [hK_pos.ne'] <;> ring
      nlinarith
    have h_min : min A (K * u) = K * u := by
      rw [min_eq_right] <;> linarith
    rw [h_min]
    have h13 : K ≤ C * u_star^(alpha - 1) := by
      have h14 : K * u_star ≤ C * u_star^alpha := by
        have h15 : K * u_star = A := by
          dsimp only [u_star]; field_simp [hK_pos.ne'] <;> ring
        linarith [h_crossover]
      calc
        K = (K * u_star) / u_star := by field_simp [h_ustar_pos.ne'] <;> ring
        _ ≤ (C * u_star^alpha) / u_star := by gcongr
        _ = C * u_star^(alpha - 1) := by
          have h16 : u_star^alpha / u_star = u_star^(alpha - 1) := by
            have h17 : u_star^(alpha - 1) * u_star = u_star^alpha := by
              calc
                u_star^(alpha - 1) * u_star
                  = u_star^(alpha - 1) * u_star^(1 : ℝ) := by
                    congr 1
                    exact (Real.rpow_one u_star).symm
                _ = u_star^((alpha - 1) + 1) := by
                    rw [← Real.rpow_add h_ustar_pos] <;> ring
                _ = u_star^alpha := by
                    have h19 : (alpha - 1) + 1 = alpha := by ring
                    rw [h19]
            rw [h17.symm]
            <;> field_simp [h_ustar_pos.ne'] <;> ring
          have h18 : C * u_star^alpha / u_star = C * (u_star^alpha / u_star) := by ring
          rw [h18, h16] <;> ring
    have h19 : C * u^(alpha - 1) > K := by
      have h20 : u^(1 - alpha) < u_star^(1 - alpha) :=
        Real.rpow_lt_rpow (by positivity) h_case' (by positivity)
      have h21 : C * u^(alpha - 1) = C / u^(1 - alpha) := by
        have h22 : alpha - 1 = -(1 - alpha) := by ring
        rw [h22, Real.rpow_neg hu_pos.le] <;> ring
      rw [h21]
      have h23 : C / u^(1 - alpha) > C / u_star^(1 - alpha) := by gcongr
      have h24 : C / u_star^(1 - alpha) = C * u_star^(alpha - 1) := by
        have h25 : u_star^(alpha - 1) = (u_star^(1 - alpha))⁻¹ := by
          have h26 : alpha - 1 = -(1 - alpha) := by ring
          rw [h26, Real.rpow_neg h_ustar_pos.le] <;> ring
        rw [h25] <;> ring
      rw [h24] at h23; linarith
    have h25 : K * u ≤ C * u^alpha := by
      have h26 : K * u ≤ (C * u^(alpha - 1)) * u := by gcongr
      have h27 : (C * u^(alpha - 1)) * u = C * u^alpha := by
        have h28 : u^(alpha - 1) * u = u^alpha := by
          have h29 : u^(alpha - 1) * u^(1 : ℝ) = u^((alpha - 1) + 1) := by
            rw [← Real.rpow_add hu_pos]
          have h30 : u^(1 : ℝ) = u := Real.rpow_one u
          have h31 : u^(alpha - 1) * u = u^(alpha - 1) * u^(1 : ℝ) := by
            exact congr_arg (fun x : ℝ => u^(alpha - 1) * x) h30.symm
          rw [h31, h29]
          have h32 : (alpha - 1) + 1 = alpha := by ring
          rw [h32]
        rw [mul_assoc, h28]
      rw [h27] at h26; exact h26
    exact h25

/-- A set in `ℝ` of diameter at most `2R` is contained in 3 balls of radius `R`. -/
lemma real_cover_by_three_balls {E : Set ℝ} {R : ℝ} (hR : 0 < R)
    (h_diam : ∀ x y, x ∈ E → y ∈ E → dist x y ≤ 2 * R) :
    ∃ (centers : Finset ℝ), centers.card ≤ 3 ∧
      E ⊆ ⋃ c ∈ centers, closedBall c R := by
  by_cases hE : E = ∅
  · refine ⟨∅, by simp, ?_⟩
    rw [hE]; simp
  · have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE
    rcases hE_nonempty with ⟨y, hy⟩
    have hE_sub : E ⊆ closedBall y (2 * R) := by
      intro z hz
      exact h_diam z y hz hy
    let centers : Finset ℝ := {y - 2 * R, y, y + 2 * R}
    have hcard : centers.card ≤ 3 := by
      dsimp only [centers]
      exact Finset.card_le_three
    have hcover : closedBall y (2 * R) ⊆ ⋃ c ∈ centers, closedBall c R := by
      intro x hx
      have hdist : dist x y ≤ 2 * R := hx
      have habs : |x - y| ≤ 2 * R := by simpa [Real.dist_eq] using hdist
      have h1 : y - 2 * R ≤ x := by linarith [abs_le.mp habs]
      have h2 : x ≤ y + 2 * R := by linarith [abs_le.mp habs]
      by_cases h3 : x ≤ y - R
      · have h41 : 0 ≤ x - (y - 2 * R) := by linarith
        have h42 : x - (y - 2 * R) ≤ R := by linarith
        have h4 : x ∈ closedBall (y - 2 * R) R := by
          simp only [Metric.mem_closedBall, Real.dist_eq]
          rw [abs_of_nonneg h41]
          <;> linarith
        exact Set.mem_iUnion₂.mpr ⟨y - 2 * R, by simp [centers], h4⟩
      · by_cases h5 : x ≤ y + R
        · have h61 : -R ≤ x - y := by linarith
          have h62 : x - y ≤ R := by linarith
          have h6 : x ∈ closedBall y R := by
            simp only [Metric.mem_closedBall, Real.dist_eq]
            rw [abs_le] <;> exact ⟨h61, h62⟩
          exact Set.mem_iUnion₂.mpr ⟨y, by simp [centers], h6⟩
        · have h7 : x ∈ closedBall (y + 2 * R) R := by
            simp only [Metric.mem_closedBall, Real.dist_eq]
            have h74 : x - (y + 2 * R) ≤ 0 := by linarith
            rw [abs_of_nonpos h74] <;> linarith
          exact Set.mem_iUnion₂.mpr ⟨y + 2 * R, by simp [centers], h7⟩
    exact ⟨centers, hcard, hE_sub.trans hcover⟩

/-- Covering number of a binary union is at most the sum. -/
lemma externalCoveringNumber_union_le {X : Type*} [PseudoEMetricSpace X] {ε : NNReal} {A B : Set X} :
    Metric.externalCoveringNumber ε (A ∪ B) ≤
      Metric.externalCoveringNumber ε A + Metric.externalCoveringNumber ε B := by
  let b : ℕ∞ := Metric.externalCoveringNumber ε B
  have h1 : ∀ (CA : Set X), Metric.IsCover ε A CA →
      Metric.externalCoveringNumber ε (A ∪ B) ≤ CA.encard + b := by
    intro CA hCA
    have h2 : ∀ (CB : Set X), Metric.IsCover ε B CB →
        Metric.externalCoveringNumber ε (A ∪ B) ≤ CA.encard + CB.encard := by
      intro CB hCB
      have h_union : Metric.IsCover ε (A ∪ B) (CA ∪ CB) := by
        intro x hx
        cases hx with
        | inl hxA =>
          rcases hCA hxA with ⟨c, hc, hdist⟩
          exact ⟨c, Or.inl hc, hdist⟩
        | inr hxB =>
          rcases hCB hxB with ⟨c, hc, hdist⟩
          exact ⟨c, Or.inr hc, hdist⟩
      have h3 : Metric.externalCoveringNumber ε (A ∪ B) ≤ (CA ∪ CB).encard :=
        h_union.externalCoveringNumber_le_encard
      have h4 : (CA ∪ CB).encard ≤ CA.encard + CB.encard := Set.encard_union_le _ _
      exact h3.trans h4
    have h5 : Metric.externalCoveringNumber ε (A ∪ B) ≤
        ⨅ (CB : Set X) (_ : Metric.IsCover ε B CB), CA.encard + CB.encard :=
      le_iInf₂ h2
    let g : Set X → ℕ∞ := fun CB => ⨅ (_ : Metric.IsCover ε B CB), CB.encard
    have hg : iInf g = b := by rfl
    have h_inner : ∀ (CB : Set X), (⨅ (_ : Metric.IsCover ε B CB), CA.encard + CB.encard) =
        CA.encard + g CB := by
      intro CB
      let f : Metric.IsCover ε B CB → ℕ∞ := fun _ => CB.encard
      have h_eq : (⨅ (h : Metric.IsCover ε B CB), CA.encard + CB.encard) =
          CA.encard + iInf f := by
        have h : CA.encard + iInf f = ⨅ (h : Metric.IsCover ε B CB), CA.encard + f h :=
          ENat.add_iInf
        exact h.symm
      exact h_eq
    have h6 : (⨅ (CB : Set X) (_ : Metric.IsCover ε B CB), CA.encard + CB.encard) =
        ⨅ (CB : Set X), CA.encard + g CB := by
      congr with CB
      exact h_inner CB
    rw [h6] at h5
    have h7 : (⨅ (CB : Set X), CA.encard + g CB) = CA.encard + iInf g := by
      have h : CA.encard + iInf g = ⨅ (CB : Set X), CA.encard + g CB := ENat.add_iInf
      exact h.symm
    rw [h7, hg] at h5
    exact h5
  have h7 : Metric.externalCoveringNumber ε (A ∪ B) ≤
      ⨅ (CA : Set X), (⨅ (_ : Metric.IsCover ε A CA), CA.encard) + b := by
    have h71 : ∀ (CA : Set X), Metric.externalCoveringNumber ε (A ∪ B) ≤
        (⨅ (_ : Metric.IsCover ε A CA), CA.encard) + b := by
      intro CA
      have h72 : Metric.externalCoveringNumber ε (A ∪ B) ≤
          ⨅ (_ : Metric.IsCover ε A CA), CA.encard + b :=
        le_iInf (fun h => h1 CA h)
      let f : Metric.IsCover ε A CA → ℕ∞ := fun _ => CA.encard
      have h73 : (⨅ (h : Metric.IsCover ε A CA), CA.encard + b) =
          (iInf f) + b := by
        have h74 : iInf f + b = ⨅ (h : Metric.IsCover ε A CA), f h + b := ENat.iInf_add
        exact h74.symm
      rw [h73] at h72
      exact h72
    exact le_iInf h71
  let fOuter : Set X → ℕ∞ := fun CA => ⨅ (_ : Metric.IsCover ε A CA), CA.encard
  have h8 : (⨅ (CA : Set X), fOuter CA + b) = (iInf fOuter) + b := by
    have h : iInf fOuter + b = ⨅ (CA : Set X), fOuter CA + b := ENat.iInf_add
    exact h.symm
  have h9 : iInf fOuter = Metric.externalCoveringNumber ε A := by rfl
  rw [h8, h9] at h7
  exact h7

/-- Covering number of a finite union is at most `card * B` when each piece is ≤ `B`. -/
lemma externalCoveringNumber_biUnion_le_card {X : Type*} [PseudoEMetricSpace X] {ε : NNReal}
    {ι : Type*} {s : Finset ι} {A : ι → Set X} {B : ENNReal}
    (h : ∀ i ∈ s, (Metric.externalCoveringNumber ε (A i) : ENNReal) ≤ B) :
    (Metric.externalCoveringNumber ε (⋃ i ∈ s, A i) : ENNReal) ≤ (s.card : ENNReal) * B := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert i s hi ih =>
    have h9 : (⋃ j ∈ (insert i s), A j) = A i ∪ (⋃ j ∈ s, A j) := by
      ext x
      simp [Finset.mem_insert, hi] <;> tauto
    rw [h9]
    have h10 : (Metric.externalCoveringNumber ε (A i ∪ (⋃ j ∈ s, A j)) : ENNReal) ≤
        (Metric.externalCoveringNumber ε (A i) : ENNReal) +
        (Metric.externalCoveringNumber ε (⋃ j ∈ s, A j) : ENNReal) := by
      exact_mod_cast externalCoveringNumber_union_le
    have h11 : (Metric.externalCoveringNumber ε (A i) : ENNReal) ≤ B :=
      h i (Finset.mem_insert_self i s)
    have h12 : (Metric.externalCoveringNumber ε (⋃ j ∈ s, A j) : ENNReal) ≤ (s.card : ENNReal) * B :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc
      (Metric.externalCoveringNumber ε (A i ∪ (⋃ j ∈ s, A j)) : ENNReal)
        ≤ (Metric.externalCoveringNumber ε (A i) : ENNReal) +
            (Metric.externalCoveringNumber ε (⋃ j ∈ s, A j) : ENNReal) := h10
      _ ≤ B + (s.card : ENNReal) * B := by gcongr
      _ = ((insert i s).card : ENNReal) * B := by
        have hcard : (insert i s).card = s.card + 1 := Finset.card_insert_of_notMem hi
        rw [hcard]
        simp [Nat.cast_add, add_mul] <;> ring

/-- Assemble `IsADSet1` from interval bounds and diameter bound.

Given:
- `E` has diameter at most `2 * Real.sqrt rho`
- interval bounds at every radius `r ∈ [rho, sqrt(rho)]` with constant `C_int`
- absorption condition `(3*C_int)^(1-α) * K^α * rho^(-α(1-α)/2) ≤ C`
- `K ≥ 6`

Produces `IsADSet1 E rho α C`. -/
lemma interval_bounds_to_ad_set
    (E : Set ℝ) (rho alpha C_int C K : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hK : 6 ≤ K) (hC_int : 1 ≤ C_int) (hC : 1 ≤ C)
    (h_bounded : E ⊆ Set.Icc (-4 : ℝ) 4)
    (h_diam : ∀ x y, x ∈ E → y ∈ E → dist x y ≤ 2 * Real.sqrt rho)
    (h_interval : ∀ (r : ℝ), rho ≤ r → r ≤ Real.sqrt rho → ∀ (x : ℝ),
        (↑(Metric.externalCoveringNumber ⟨rho, hrho.le⟩
            (E ∩ Metric.closedBall x r)) : ENNReal) ≤
          ENNReal.ofReal (C_int * (r / rho)^alpha))
    (h_absorb : (3 * C_int)^(1-alpha) * K^alpha * rho^(-alpha*(1-alpha)/2) ≤ C) :
    IsADSet1 E rho alpha (ENNReal.ofReal C) := by
  set A_const : ℝ := 3 * C_int with hA_const_def
  have hA_const_pos : 0 < A_const := by positivity
  have hC_pos : 0 < C := by linarith
  have hK_pos : 0 < K := by linarith
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hC_one : (1 : ENNReal) ≤ ENNReal.ofReal C := by
    simpa using ENNReal.ofReal_le_ofReal hC
  refine ⟨hrho, halpha, halpha1.le, hC_one, h_bounded, ?_⟩
  intro t ht_nonneg hrho_t ht_one x r ht_r hr_one
  set A_set : Set ℝ := E ∩ Metric.closedBall x r with hA_def
  have ht_pos : 0 < t := by linarith
  let m : ℝ := min r (Real.sqrt rho)
  have hr_pos : 0 < r := by linarith
  have hm_pos : 0 < m := by
    apply lt_min hr_pos
    exact Real.sqrt_pos.mpr hrho
  -- Diameter of A_set ≤ 2*m
  have h_diam_m : ∀ a b, a ∈ A_set → b ∈ A_set → dist a b ≤ 2 * m := by
    intro a b ha hb
    have h1 : dist a b ≤ 2 * r := by
      have h2 : dist a b ≤ dist a x + dist x b := dist_triangle a x b
      have h3 : dist a x ≤ r := ha.2
      have h4 : dist x b ≤ r := by simpa [dist_comm] using hb.2
      linarith
    have h2 : dist a b ≤ 2 * Real.sqrt rho := h_diam a b ha.1 hb.1
    have h3 : dist a b ≤ 2 * m := by
      cases le_total r (Real.sqrt rho) with
      | inl h4 =>
        have h5 : m = r := by simp [m, h4]
        rw [h5] <;> linarith
      | inr h4 =>
        have h5 : m = Real.sqrt rho := by simp [m, h4]
        rw [h5] <;> linarith
    exact h3
  -- Case 1: t ≥ Real.sqrt rho
  by_cases h_case1 : t ≥ Real.sqrt rho
  · -- Diameter of A_set ≤ 2*t, so 3 balls of radius t suffice
    have h_diam_2t : ∀ a b, a ∈ A_set → b ∈ A_set → dist a b ≤ 2 * t := by
      intro a b ha hb
      have h : dist a b ≤ 2 * m := h_diam_m a b ha hb
      have h2 : m ≤ Real.sqrt rho := min_le_right _ _
      have h3 : Real.sqrt rho ≤ t := by linarith
      linarith
    rcases real_cover_by_three_balls ht_pos h_diam_2t with ⟨centers, hcard3, hcover3⟩
    have h5 : Metric.IsCover ⟨t, ht_nonneg⟩ A_set (centers : Set ℝ) := by
      intro a ha
      have h6 : a ∈ ⋃ c ∈ centers, closedBall c t := hcover3 ha
      rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, hball⟩
      refine ⟨c, hc, ?_⟩
      simpa [Set.mem_setOf_eq] using dist_le_coe.mp hball
    have h6 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤ (centers.card : ENNReal) := by
      have h_main : Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set ≤ (centers : Set ℝ).encard :=
        h5.externalCoveringNumber_le_encard
      have h10 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤ ((centers : Set ℝ).encard : ENNReal) := by
        exact_mod_cast h_main
      have h11 : ((centers : Set ℝ).encard : ENNReal) = (centers.card : ENNReal) := by simp
      rw [h11] at h10
      exact h10
    have hcov : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤ (3 : ENNReal) := by
      have h7 : (centers.card : ENNReal) ≤ 3 := by exact_mod_cast hcard3
      exact h6.trans h7
    have hC3 : (3 : ℝ) ≤ C := by
      have h1 : (3 * C_int)^(1-alpha) ≥ 3^(1-alpha) := by
        have h2 : 3 ≤ 3 * C_int := by linarith
        exact Real.rpow_le_rpow (by positivity) h2 (by positivity)
      have h3 : K^alpha ≥ 6^alpha := Real.rpow_le_rpow (by positivity) hK (by positivity)
      have h4 : rho^(-alpha*(1-alpha)/2) ≥ 1 := by
        set e : ℝ := -alpha*(1-alpha)/2 with he_def
        set f : ℝ := -e with hf_def
        have hf_nonneg : 0 ≤ f := by
          dsimp only [f, e]
          have h1 : 0 ≤ alpha := by linarith
          have h2 : 0 ≤ 1 - alpha := by linarith
          have h3 : 0 ≤ alpha * (1 - alpha) := mul_nonneg h1 h2
          have h4 : 0 ≤ alpha * (1 - alpha) / 2 := by positivity
          linarith
        have h_rho_f : rho^f ≤ 1 := by
          have h : rho^f ≤ 1^f := Real.rpow_le_rpow (by linarith) hrho1 hf_nonneg
          simpa using h
        have h_rho_e : rho^e = (rho^f)⁻¹ := by
          have h_e_neg : e = -f := by linarith
          rw [h_e_neg]
          rw [Real.rpow_neg hrho.le] <;> ring
        rw [h_rho_e]
        have h_pos : 0 < rho^f := Real.rpow_pos_of_pos hrho f
        have h_inv_ge_one : 1 ≤ (rho^f)⁻¹ := by
          have h_pos : 0 < rho^f := Real.rpow_pos_of_pos hrho f
          have h_le : rho^f ≤ 1 := h_rho_f
          have h : (rho^f)⁻¹ ≥ 1 := by
            calc (rho^f)⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
                 _ = 1 := by norm_num
          exact h
        exact h_inv_ge_one
      have h8 : (3 * C_int)^(1-alpha) * K^alpha * rho^(-alpha*(1-alpha)/2) ≥ 3 := by
        have h_ineq : (3 : ℝ)^(1-alpha) * (6 : ℝ)^alpha ≥ 3 := by
          have h1 : (6 : ℝ)^alpha ≥ (3 : ℝ)^alpha :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
          have h2 : (3 : ℝ)^(1-alpha) * (6 : ℝ)^alpha ≥ (3 : ℝ)^(1-alpha) * (3 : ℝ)^alpha := by gcongr
          have h3 : (3 : ℝ)^(1-alpha) * (3 : ℝ)^alpha = 3 := by
            have hpos : 0 < (3 : ℝ) := by norm_num
            have h4 : (3 : ℝ)^((1-alpha)+alpha) = (3 : ℝ)^(1-alpha) * (3 : ℝ)^alpha :=
              Real.rpow_add hpos (1-alpha) alpha
            have h5 : (1-alpha)+alpha = 1 := by ring
            have h6 : (3 : ℝ)^((1-alpha)+alpha) = 3 := by
              rw [h5]
              exact Real.rpow_one 3
            exact h4.symm.trans h6
          rw [h3] at h2
          exact h2
        have h91 : (3 * C_int)^(1-alpha) ≥ (3 : ℝ)^(1-alpha) := by
          have h : 3 ≤ 3 * C_int := by linarith
          exact Real.rpow_le_rpow (by norm_num) h (by linarith)
        have h92 : K^alpha ≥ (6 : ℝ)^alpha := Real.rpow_le_rpow (by norm_num) hK (by linarith)
        have h93 : rho^(-alpha*(1-alpha)/2) ≥ 1 := h4
        have h9 : (3 * C_int)^(1-alpha) * K^alpha * rho^(-alpha*(1-alpha)/2) ≥
                   (3 : ℝ)^(1-alpha) * (6 : ℝ)^alpha := by
          calc
            (3 * C_int)^(1-alpha) * K^alpha * rho^(-alpha*(1-alpha)/2)
              ≥ (3 : ℝ)^(1-alpha) * (6 : ℝ)^alpha * 1 := by gcongr
            _ = (3 : ℝ)^(1-alpha) * (6 : ℝ)^alpha := by ring
        have h10 : (3 * C_int)^(1-alpha) * K^alpha * rho^(-alpha*(1-alpha)/2) ≥ 3 := by
          calc
            (3 * C_int)^(1-alpha) * K^alpha * rho^(-alpha*(1-alpha)/2)
              ≥ (3 : ℝ)^(1-alpha) * (6 : ℝ)^alpha := h9
            _ ≥ 3 := h_ineq
        exact h10
      linarith [h_absorb]
    have h3 : (3 : ENNReal) ≤ ENNReal.ofReal C * Kakeya.realRpowENN (r / t) alpha := by
      have h4 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r / t) alpha := by
        simp only [Kakeya.realRpowENN]
        have h5 : 1 ≤ r / t := by
          calc (1 : ℝ) = t / t := by field_simp [ht_pos.ne']
               _ ≤ r / t := by gcongr
        have h6 : (1 : ℝ) ≤ Real.rpow (r / t) alpha := Real.one_le_rpow h5 (by linarith)
        simpa using ENNReal.ofReal_le_ofReal h6
      have h7 : (3 : ENNReal) ≤ ENNReal.ofReal C := by
        simpa using ENNReal.ofReal_le_ofReal hC3
      calc (3 : ENNReal) ≤ ENNReal.ofReal C := h7
           _ ≤ ENNReal.ofReal C * Kakeya.realRpowENN (r / t) alpha := le_mul_of_one_le_right' h4
    exact hcov.trans h3
  · -- Case 2/3: t < Real.sqrt rho
    have h_t_lt_sqrt : t < Real.sqrt rho := by linarith
    have hmt : t ≤ m := le_min ht_r (by linarith [h_t_lt_sqrt])
    have h_diam_bound : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        ENNReal.ofReal (K * m / t) := by
      have hcov : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
          ENNReal.ofReal (2 * (2 * m) / t + 2) := covering_by_diameter ht_pos (by positivity) h_diam_m
      set q : ℝ := m / t with hq_def
      have hq1 : 1 ≤ q := by
        dsimp only [q]
        calc (1 : ℝ) = t / t := by field_simp [ht_pos.ne']
             _ ≤ m / t := by gcongr
      have h11 : 2 ≤ 2 * q := by
        calc 2 = 2 * (1 : ℝ) := by ring
             _ ≤ 2 * q := by gcongr
      have h : 4 * q + 2 ≤ K * q := by
        have h9 : K ≥ 6 := hK
        calc 4 * q + 2 ≤ 4 * q + 2 * q := by gcongr
             _ = 6 * q := by ring
             _ ≤ K * q := by gcongr
      have h_goal : 2 * (2 * m) / t + 2 ≤ K * m / t := by
        have h_eq1 : 2 * (2 * m) / t + 2 = 4 * q + 2 := by
          simp [hq_def] <;> ring
        have h_eq2 : K * m / t = K * q := by
          simp [hq_def] <;> ring
        rw [h_eq1, h_eq2]
        exact h
      exact hcov.trans (ENNReal.ofReal_le_ofReal h_goal)
    set u : ℝ := m / t with hu_def
    set v : ℝ := m / rho with hv_def
    have hu_pos : 0 < u := by positivity
    have hv_pos : 0 < v := by positivity
    have hu1 : 1 ≤ u := by
      dsimp only [u]; have h : t ≤ m := hmt
      calc (1 : ℝ) = t / t := by field_simp [ht_pos.ne']
           _ ≤ m / t := by gcongr
    have huv : u ≤ v := by
      dsimp only [u, v]
      have h : t ≥ rho := hrho_t
      gcongr
    have hv_le : v ≤ rho^(-1 / 2 : ℝ) := by
      dsimp only [v]
      have h1 : m ≤ Real.sqrt rho := min_le_right _ _
      have h2 : m / rho ≤ Real.sqrt rho / rho := by gcongr
      have h3 : Real.sqrt rho / rho = rho^(-1 / 2 : ℝ) := by
        have h4 : Real.sqrt rho = rho^(1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
        rw [h4]
        have h5 : rho^(1 / 2 : ℝ) / rho = rho^(-1 / 2 : ℝ) := by
          have h51 : rho^(1 / 2 : ℝ) / rho = rho^(1 / 2 : ℝ) * rho⁻¹ := by ring
          rw [h51]
          have h52 : rho⁻¹ = rho^(-1 : ℝ) := by
            rw [Real.rpow_neg (by linarith)] <;> simp
          rw [h52]
          have h53 : rho^(1 / 2 : ℝ) * rho^(-1 : ℝ) = rho^((1 / 2 : ℝ) + (-1 : ℝ)) := by
            rw [← Real.rpow_add (by linarith)]
          rw [h53]
          have h54 : (1 / 2 : ℝ) + (-1 : ℝ) = -1 / 2 := by norm_num
          rw [h54]
        exact h5
      linarith
    -- Interval bound: covering(t, A_set) ≤ covering(rho, A_set) ≤ A_const * v^alpha
    have h_mono : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        (Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A_set : ENNReal) := by
      have h_nn : (⟨rho, hrho.le⟩ : NNReal) ≤ ⟨t, ht_nonneg⟩ := by
        exact Subtype.mk_le_mk.mpr hrho_t
      have h : Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set ≤
          Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A_set :=
        Metric.externalCoveringNumber_anti h_nn
      exact_mod_cast h
    have h_interval_bound : (Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A_set : ENNReal) ≤
        ENNReal.ofReal (A_const * v^alpha) := by
      by_cases hE : E = ∅
      · rw [hE] at hA_def
        simp [hA_def]
      · by_cases h_r_le : r ≤ Real.sqrt rho
        · -- r ≤ sqrt(rho): use h_interval r directly
          have hr_rho : rho ≤ r := by linarith
          have h_eq1 : C_int * (r / rho)^alpha ≤ A_const * v^alpha := by
            dsimp only [v, A_const]
            have h10 : m = r := by simp [m, h_r_le]
            have h11 : m / rho = r / rho := by
              congr 1 <;> exact h10
            rw [h11]
            have h12 : 0 ≤ (r / rho)^alpha := by positivity
            nlinarith
          have h10 : (Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A_set : ENNReal) ≤
              ENNReal.ofReal (C_int * (r / rho)^alpha) := h_interval r hr_rho h_r_le x
          exact h10.trans (ENNReal.ofReal_le_ofReal h_eq1)
        · -- r > sqrt(rho): cover E by 3 balls of radius sqrt(rho)
          have h_r_gt : Real.sqrt rho < r := by linarith
          rcases real_cover_by_three_balls hsqrt_pos h_diam with
            ⟨centers, hcard3, hcover3⟩
          have h4 : A_set ⊆ ⋃ c ∈ centers, closedBall c (Real.sqrt rho) := by
            intro z hz
            have hzE : z ∈ E := hz.1
            exact hcover3 hzE
          have h5 : Metric.IsCover ⟨Real.sqrt rho, hsqrt_pos.le⟩ A_set (centers : Set ℝ) := by
            intro a ha
            have h6 : a ∈ ⋃ c ∈ centers, closedBall c (Real.sqrt rho) := h4 ha
            rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, hball⟩
            refine ⟨c, hc, ?_⟩
            simpa [Set.mem_setOf_eq] using dist_le_coe.mp hball
          have h_pieces : ∀ c ∈ centers,
              (Metric.externalCoveringNumber ⟨rho, hrho.le⟩
                (A_set ∩ closedBall c (Real.sqrt rho)) : ENNReal) ≤
              ENNReal.ofReal (C_int * (Real.sqrt rho / rho)^alpha) := by
            intro c hc
            have h_sub : A_set ∩ closedBall c (Real.sqrt rho) ⊆
                E ∩ closedBall c (Real.sqrt rho) := by
              intro x hx; exact ⟨hx.1.1, hx.2⟩
            have h_mono_set : (Metric.externalCoveringNumber ⟨rho, hrho.le⟩
                (A_set ∩ closedBall c (Real.sqrt rho)) : ENNReal) ≤
                (Metric.externalCoveringNumber ⟨rho, hrho.le⟩
                (E ∩ closedBall c (Real.sqrt rho)) : ENNReal) := by
              exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
            have h_int := h_interval (Real.sqrt rho) (by linarith) (by linarith) c
            exact h_mono_set.trans h_int
          have h_union_eq : A_set = ⋃ c ∈ centers, (A_set ∩ closedBall c (Real.sqrt rho)) := by
            ext z
            simp only [Set.mem_iUnion, Set.mem_inter_iff]
            constructor
            · intro hz
              have hcov : z ∈ ⋃ c ∈ centers, closedBall c (Real.sqrt rho) := h4 hz
              rcases Set.mem_iUnion₂.mp hcov with ⟨c, hc, hball⟩
              exact ⟨c, hc, hz, hball⟩
            · rintro ⟨c, _, hz, _⟩; exact hz
          have h_bunion : (Metric.externalCoveringNumber ⟨rho, hrho.le⟩ A_set : ENNReal) ≤
              (centers.card : ENNReal) * ENNReal.ofReal (C_int * (Real.sqrt rho / rho)^alpha) := by
            rw [h_union_eq]
            exact externalCoveringNumber_biUnion_le_card h_pieces
          have hcard3' : (centers.card : ENNReal) ≤ 3 := by exact_mod_cast hcard3
          have h7 : (centers.card : ENNReal) * ENNReal.ofReal (C_int * (Real.sqrt rho / rho)^alpha) ≤
              ENNReal.ofReal (A_const * (Real.sqrt rho / rho)^alpha) := by
            have h8 : (centers.card : ℝ) * (C_int * (Real.sqrt rho / rho)^alpha) ≤
                A_const * (Real.sqrt rho / rho)^alpha := by
              have h9 : (centers.card : ℝ) ≤ 3 := by exact_mod_cast hcard3
              dsimp only [A_const]
              have h10 : 0 ≤ C_int * (Real.sqrt rho / rho)^alpha := by positivity
              nlinarith
            simpa [ENNReal.ofReal_mul] using ENNReal.ofReal_le_ofReal h8
          have h9 : A_const * (Real.sqrt rho / rho)^alpha = A_const * v^alpha := by
            have h10 : m = Real.sqrt rho := by simp [m, h_r_gt.le]
            have h11 : v = Real.sqrt rho / rho := by
              dsimp only [v]
              rw [h10] <;> ring
            rw [h11]
          rw [h9] at h7
          exact h_bunion.trans h7
    have h_interval_enn : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        ENNReal.ofReal (A_const * v^alpha) :=
      h_mono.trans h_interval_bound
    -- Absorption condition
    have h_absorb2 : (A_const * v^alpha)^(1-alpha) * K^alpha ≤ C := by
      have h1 : (A_const * v^alpha)^(1-alpha) =
          A_const^(1-alpha) * v^(alpha * (1-alpha)) := by
        have h2 : (A_const * v^alpha)^(1-alpha) =
            A_const^(1-alpha) * (v^alpha)^(1-alpha) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        rw [h2]
        have h3 : (v^alpha)^(1-alpha) = v^(alpha * (1-alpha)) := by
          rw [← Real.rpow_mul (by positivity)]
        rw [h3]
      rw [h1]
      have h3 : v^(alpha * (1-alpha)) ≤ rho^(-alpha * (1-alpha) / 2) := by
        have h4 : v ≤ rho^(-1 / 2 : ℝ) := hv_le
        have h5 : 0 ≤ alpha * (1 - alpha) := by positivity
        have h6 : 0 ≤ v := by positivity
        have h7 : v^(alpha * (1-alpha)) ≤ (rho^(-1 / 2 : ℝ))^(alpha * (1-alpha)) :=
          Real.rpow_le_rpow h6 h4 h5
        have h8 : (rho^(-1 / 2 : ℝ))^(alpha * (1-alpha)) = rho^(-alpha * (1-alpha) / 2) := by
          have h9 : (rho^(-1 / 2 : ℝ))^(alpha * (1-alpha)) =
              rho^((-1 / 2 : ℝ) * (alpha * (1-alpha))) := by
            rw [← Real.rpow_mul (by linarith)]
          rw [h9]
          have h10 : (-1 / 2 : ℝ) * (alpha * (1 - alpha)) = -alpha * (1 - alpha) / 2 := by ring
          rw [h10]
        rw [h8] at h7
        exact h7
      have h6 : A_const^(1-alpha) * v^(alpha * (1-alpha)) * K^alpha ≤
               A_const^(1-alpha) * rho^(-alpha * (1-alpha) / 2) * K^alpha := by
        gcongr
      have h7 : A_const = 3 * C_int := by simp [A_const]
      rw [h7] at *
      <;> linarith [h_absorb]
    have h_cross : min (A_const * v^alpha) (K * u) ≤ C * u^alpha :=
      crossover_lemma (A_const * v^alpha) K C u alpha
        (by positivity) hK_pos hC_pos hu_pos halpha halpha1 h_absorb2
    have h_diam_enn : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        ENNReal.ofReal (K * u) := by
      have h_eq : K * m / t = K * u := by
        dsimp only [u] <;> ring
      rw [h_eq] at h_diam_bound
      exact h_diam_bound
    -- Final comparison
    have h_final : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        ENNReal.ofReal (C * u^alpha) := by
      rcases le_total (A_const * v^alpha) (K * u) with hAB | hAB
      · have h : A_const * v^alpha ≤ C * u^alpha := by
          have hmin : min (A_const * v^alpha) (K * u) = A_const * v^alpha := by
            rw [min_eq_left hAB]
          rw [hmin] at h_cross; exact h_cross
        exact h_interval_enn.trans (ENNReal.ofReal_le_ofReal h)
      · have h : K * u ≤ C * u^alpha := by
          have hmin : min (A_const * v^alpha) (K * u) = K * u := by
            rw [min_eq_right hAB]
          rw [hmin] at h_cross; exact h_cross
        exact h_diam_enn.trans (ENNReal.ofReal_le_ofReal h)
    -- u = m/t ≤ r/t, so C*u^alpha ≤ C*(r/t)^alpha
    have h_u_le : u ≤ r / t := by
      dsimp only [u, m]
      have h : min r (Real.sqrt rho) ≤ r := min_le_left _ _
      gcongr
    have h_goal : C * u^alpha ≤ C * (r / t)^alpha := by
      gcongr
      <;> exact Real.rpow_le_rpow (by positivity) h_u_le (by positivity)
    have h_final2 : (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal) ≤
        ENNReal.ofReal C * Kakeya.realRpowENN (r / t) alpha := by
      have h_eq : ENNReal.ofReal (C * (r / t)^alpha) =
          ENNReal.ofReal C * Kakeya.realRpowENN (r / t) alpha := by
        have h_nonneg1 : 0 ≤ C := by linarith
        have h_nonneg2 : 0 ≤ (r / t)^alpha := by positivity
        have h9 : ENNReal.ofReal (C * (r / t)^alpha) =
            ENNReal.ofReal C * ENNReal.ofReal ((r / t)^alpha) :=
          ENNReal.ofReal_mul h_nonneg1
        rw [h9]
        <;> rfl
      calc (Metric.externalCoveringNumber ⟨t, ht_nonneg⟩ A_set : ENNReal)
          ≤ ENNReal.ofReal (C * u^alpha) := h_final
        _ ≤ ENNReal.ofReal (C * (r / t)^alpha) := ENNReal.ofReal_le_ofReal h_goal
        _ = ENNReal.ofReal C * Kakeya.realRpowENN (r / t) alpha := h_eq
    exact h_final2

/-- Absorb a constant factor into a power of delta.

Given `a < b`, for any `K > 0` there exists `delta₀ > 0` such that for all
`0 < delta ≤ delta₀`, `K * delta^(-a) ≤ delta^(-b)`. -/
lemma absorb_rpow_const (a b K : ℝ) (ha : a < b) (hK : 0 < K) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        K * Real.rpow delta (-a) ≤ Real.rpow delta (-b) := by
  have h_diff : 0 < b - a := by linarith
  let threshold : ℝ := Real.rpow K (-(1 / (b - a)))
  have hth_pos : 0 < threshold := Real.rpow_pos_of_pos hK _
  let delta₀ : ℝ := min threshold 1
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := by simp [delta₀]
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have h1 : delta ≤ threshold := hdelta_le.trans (min_le_left _ _)
  have h_pos1 : 0 ≤ delta := by linarith
  have h2 : Real.rpow delta (b - a) ≤ Real.rpow threshold (b - a) :=
    Real.rpow_le_rpow h_pos1 h1 (by linarith)
  have h3 : Real.rpow threshold (b - a) = 1 / K := by
    dsimp only [threshold]
    set y : ℝ := -(1 / (b - a)) with hy_def
    have h5 : Real.rpow (Real.rpow K y) (b - a) = Real.rpow K (y * (b - a)) :=
      (Real.rpow_mul (by linarith) y (b - a)).symm
    have h6 : y * (b - a) = -1 := by
      simp only [hy_def]
      field_simp [h_diff.ne'] <;> ring
    have h7 : Real.rpow (Real.rpow K y) (b - a) = 1 / K := by
      rw [h5, h6]
      have h8 : Real.rpow K (-1 : ℝ) = 1 / K := by
        have h9 : Real.rpow K (-1 : ℝ) = (Real.rpow K (1 : ℝ))⁻¹ := by
          exact Real.rpow_neg (by linarith) (1 : ℝ)
        rw [h9]
        have h10 : Real.rpow K (1 : ℝ) = K := by simp
        rw [h10] <;> field_simp [hK.ne']
      exact h8
    exact h7
  have h6 : Real.rpow delta (b - a) ≤ 1 / K := by
    rw [h3] at h2
    exact h2
  have h7 : Real.rpow delta (-(b - a)) ≥ K := by
    have h8 : Real.rpow delta (-(b - a)) = (Real.rpow delta (b - a))⁻¹ := by
      exact Real.rpow_neg hdelta_pos.le (b - a)
    rw [h8]
    have h9 : 0 < Real.rpow delta (b - a) := Real.rpow_pos_of_pos hdelta_pos _
    have h10 : (Real.rpow delta (b - a))⁻¹ ≥ K := by
      calc
        (Real.rpow delta (b - a))⁻¹ ≥ (1 / K)⁻¹ := by gcongr
        _ = K := by field_simp [hK.ne'] <;> ring
    exact h10
  have h11 : Real.rpow delta (-b) = Real.rpow delta (-a) * Real.rpow delta (-(b - a)) := by
    have h12 : -b = -a + (-(b - a)) := by ring
    have h13 : Real.rpow delta (-a + (-(b - a))) = Real.rpow delta (-a) * Real.rpow delta (-(b - a)) :=
      Real.rpow_add hdelta_pos (-a) (-(b - a))
    rw [h12]
    exact h13
  rw [h11]
  have h13 : K ≤ Real.rpow delta (-(b - a)) := h7
  have h14 : K * Real.rpow delta (-a) ≤ Real.rpow delta (-a) * Real.rpow delta (-(b - a)) := by
    have h_pos : 0 < Real.rpow delta (-a) := Real.rpow_pos_of_pos hdelta_pos _
    nlinarith
  exact h14

/-- If `midLoss + ε < outputLoss`, then for small enough delta,
any constant `K` can be absorbed. -/
lemma absorb_constant_general (midLoss outputLoss ε K : ℝ)
    (h : midLoss + ε < outputLoss) (hK : 0 < K) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        K * Real.rpow delta (-midLoss - ε) ≤ Real.rpow delta (-outputLoss) := by
  have h_eq : -(midLoss + ε) = -midLoss - ε := by ring
  simpa [h_eq] using absorb_rpow_const (midLoss + ε) outputLoss K h hK

end Kakeya.Assouad
