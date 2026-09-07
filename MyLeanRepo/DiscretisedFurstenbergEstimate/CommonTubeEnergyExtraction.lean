module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Common-tube energy extraction

This is the exact averaging-and-pruning step behind OS (A.31)--(A.41).
It separates the combinatorics from the preceding geometric estimate of the
total `(t-s)`-energy.

The conclusion gives one tube carrying many coarse squares and a large subset
on which every point has bounded energy.  The displayed ball-count estimate is
the non-concentration estimate used to obtain a `(Δ,t-s)`-set.

## Main definitions

- `SeparatedAt`: a set is `r`-separated if any two distinct points are at distance at least `r`.
- `pointEnergy`: energy of a single point with respect to a finite set.
- `pairEnergy`: total pair energy of a finite set.

## Main theorem

- `common_tube_energy_extraction`: given a family of tubes with fibers in a
  δ-separated set, bounded total incidence and pair energy, extracts one tube
  and a subset with bounded pointwise energy and ball-count growth.
-/

noncomputable section

def SeparatedAt {X : Type*} [PseudoMetricSpace X]
    (r : ℝ) (P : Set X) : Prop :=
  P.Pairwise fun x y => r ≤ dist x y

def pointEnergy {X : Type*} [MetricSpace X] [DecidableEq X]
    (u : ℝ) (P : Finset X) (x : X) : ℝ :=
  ∑ y ∈ P.erase x, Real.rpow (dist x y) (-u)

def pairEnergy {X : Type*} [MetricSpace X] [DecidableEq X]
    (u : ℝ) (P : Finset X) : ℝ :=
  ∑ x ∈ P, pointEnergy u P x

theorem common_tube_energy_extraction
    {X Tube : Type*} [MetricSpace X]
    [DecidableEq X] [DecidableEq Tube]
    (δ u I E L : ℝ)
    (Q : Finset X) (𝒯 : Finset Tube)
    (fiber : Tube → Finset X)
    (hδ : 0 < δ) (hu : 0 < u)
    (hI : 0 < I) (hE : 0 ≤ E) (hL : 0 < L)
    (hQsep : SeparatedAt δ (Q : Set X))
    (hfiber : ∀ T ∈ 𝒯, fiber T ⊆ Q)
    (hcard : (𝒯.card : ℝ) ≤ L)
    (hincidence : I ≤ ∑ T ∈ 𝒯, ((fiber T).card : ℝ))
    (henergy : ∑ T ∈ 𝒯, pairEnergy u (fiber T) ≤ E) :
    ∃ T₀ ∈ 𝒯, ∃ Q₀ : Finset X,
      Q₀ ⊆ fiber T₀ ∧
      I ≤ 4 * L * (Q₀.card : ℝ) ∧
      (∀ q ∈ Q₀, pointEnergy u Q₀ q ≤ 4 * E / I) ∧
      ∀ q ∈ Q₀, ∀ r : ℝ, δ ≤ r →
        ((Q₀.filter fun q' => dist q q' ≤ r).card : ℝ) ≤
          1 + (4 * E / I) * Real.rpow r u := by
  have h_pe_nonneg : ∀ (P : Finset X) (x : X), 0 ≤ pointEnergy u P x := by
    intro P x
    apply Finset.sum_nonneg
    intro y _
    exact Real.rpow_nonneg dist_nonneg _
  have h_pairEnergy_nonneg : ∀ (P : Finset X), 0 ≤ pairEnergy u P := by
    intro P
    apply Finset.sum_nonneg
    intro x _
    exact h_pe_nonneg P x
  by_cases hE_pos : 0 < E
  · -- Case E > 0
    have h_main : ∃ T₀ ∈ 𝒯,
        (pairEnergy u (fiber T₀) ≤ (2 * E / I) * (fiber T₀).card) ∧
        (I / (2 * L) ≤ (fiber T₀).card) := by
      let good : Tube → Prop := fun T =>
        pairEnergy u (fiber T) ≤ (2 * E / I) * (fiber T).card
      let goodTubes := 𝒯.filter good
      let badTubes := 𝒯.filter (fun T => ¬ good T)
      have h_disj : Disjoint goodTubes badTubes := by
        simp [goodTubes, badTubes, Finset.disjoint_left] <;> tauto
      have h_union : goodTubes ∪ badTubes = 𝒯 := by
        ext T; simp [goodTubes, badTubes] <;> tauto
      have h_bad_ineq : ∀ T ∈ badTubes,
          (2 * E / I) * ((fiber T).card : ℝ) ≤ pairEnergy u (fiber T) := by
        intro T hT
        have h_bad : T ∈ 𝒯 ∧ ¬ good T := by simpa [badTubes] using hT
        exact le_of_not_ge h_bad.2
      have h_bad_sum : (2 * E / I) * ∑ T ∈ badTubes, ((fiber T).card : ℝ) ≤
          ∑ T ∈ badTubes, pairEnergy u (fiber T) := by
        calc
          (2 * E / I) * ∑ T ∈ badTubes, ((fiber T).card : ℝ)
            = ∑ T ∈ badTubes, (2 * E / I) * ((fiber T).card : ℝ) := by
              rw [Finset.mul_sum] <;> ring
          _ ≤ ∑ T ∈ badTubes, pairEnergy u (fiber T) :=
              Finset.sum_le_sum fun T hT => h_bad_ineq T hT
      have h_bad_subset : badTubes ⊆ 𝒯 := by simp [badTubes]
      have h_bad_le_all : ∑ T ∈ badTubes, pairEnergy u (fiber T) ≤
          ∑ T ∈ 𝒯, pairEnergy u (fiber T) :=
        Finset.sum_le_sum_of_subset_of_nonneg h_bad_subset
          (fun T hT _ => h_pairEnergy_nonneg (fiber T))
      have h_bad_energy : ∑ T ∈ badTubes, pairEnergy u (fiber T) ≤ E :=
        le_trans h_bad_le_all henergy
      have h1 : (2 * E / I) * ∑ T ∈ badTubes, ((fiber T).card : ℝ) ≤ E :=
        le_trans h_bad_sum h_bad_energy
      have h_coef_pos : 0 < 2 * E / I := by positivity
      have h_coef_mul_half : (2 * E / I) * (I / 2) = E := by
        have hI_ne : I ≠ 0 := hI.ne'
        field_simp [hI_ne] <;> ring
      have h2 : ∑ T ∈ badTubes, ((fiber T).card : ℝ) ≤ I / 2 := by
        have h21 : (2 * E / I) * ∑ T ∈ badTubes, ((fiber T).card : ℝ) ≤ (2 * E / I) * (I / 2) := by
          rw [h_coef_mul_half]; exact h1
        exact le_of_mul_le_mul_left h21 h_coef_pos
      have h3 : ∑ T ∈ goodTubes, ((fiber T).card : ℝ) +
            ∑ T ∈ badTubes, ((fiber T).card : ℝ) =
          ∑ T ∈ 𝒯, ((fiber T).card : ℝ) := by
        rw [← Finset.sum_union h_disj, h_union]
      have h4 : I / 2 ≤ ∑ T ∈ goodTubes, ((fiber T).card : ℝ) := by
        linarith [hincidence, h2, h3]
      have h_good_subset : goodTubes ⊆ 𝒯 := by simp [goodTubes]
      have h5 : (goodTubes.card : ℝ) ≤ L := by
        have h51 : goodTubes.card ≤ 𝒯.card := Finset.card_le_card h_good_subset
        exact le_trans (mod_cast h51) hcard
      have h_half_pos : 0 < I / 2 := by positivity
      have h_pigeonhole : ∃ T₀ ∈ goodTubes, (I / 2 : ℝ) / L ≤ ((fiber T₀).card : ℝ) := by
        by_contra h
        push Not at h
        have h_nonempty : goodTubes.Nonempty := by
          by_contra h_empty
          have h_eq : goodTubes = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
          rw [h_eq] at h4
          have h_B_le_zero : I / 2 ≤ 0 := by simpa using h4
          exact False.elim (not_le.mpr h_half_pos h_B_le_zero)
        have h_sum_lt : ∑ T ∈ goodTubes, ((fiber T).card : ℝ) < ∑ T ∈ goodTubes, ((I / 2 : ℝ) / L) :=
          Finset.sum_lt_sum_of_nonempty h_nonempty fun T hT => h T hT
        have h_sum_const : (∑ T ∈ goodTubes, ((I / 2 : ℝ) / L)) = (goodTubes.card : ℝ) * ((I / 2 : ℝ) / L) := by
          simp [Finset.sum_const] <;> ring
        have h_avg_pos : 0 < (I / 2 : ℝ) / L := by positivity
        have h_card_mul : (goodTubes.card : ℝ) * ((I / 2 : ℝ) / L) ≤ L * ((I / 2 : ℝ) / L) :=
          mul_le_mul_of_nonneg_right h5 h_avg_pos.le
        have h_N_mul : L * ((I / 2 : ℝ) / L) = I / 2 := by
          field_simp [hL.ne'] <;> ring
        have h_main2 : ∑ T ∈ goodTubes, ((fiber T).card : ℝ) < I / 2 := by
          calc
            ∑ T ∈ goodTubes, ((fiber T).card : ℝ) < ∑ T ∈ goodTubes, ((I / 2 : ℝ) / L) := h_sum_lt
            _ = (goodTubes.card : ℝ) * ((I / 2 : ℝ) / L) := h_sum_const
            _ ≤ L * ((I / 2 : ℝ) / L) := h_card_mul
            _ = I / 2 := h_N_mul
        exact lt_irrefl (I / 2) (h4.trans_lt h_main2)
      rcases h_pigeonhole with ⟨T₀, hT₀_good, h_card_ge⟩
      have hT₀_in_𝒯 : T₀ ∈ 𝒯 := h_good_subset hT₀_good
      have h_good_T₀ : good T₀ := (Finset.mem_filter.mp hT₀_good).2
      have h_final_card : (I / (2 * L) : ℝ) ≤ ((fiber T₀).card : ℝ) := by
        have h_eq : (I / 2 : ℝ) / L = I / (2 * L) := by ring
        rw [h_eq] at h_card_ge
        exact h_card_ge
      exact ⟨T₀, hT₀_in_𝒯, h_good_T₀, h_final_card⟩
    rcases h_main with ⟨T₀, hT₀in𝒯, h_avg, h_card⟩
    let P := fiber T₀
    let Q₀ := P.filter fun q => pointEnergy u P q ≤ 4 * E / I
    have hQ₀subP : Q₀ ⊆ P := Finset.filter_subset _ _
    have hQ₀card : (P.card : ℝ) / 2 ≤ (Q₀.card : ℝ) := by
      let bad := P.filter (fun q => ¬ pointEnergy u P q ≤ 4 * E / I)
      have h_pos : 0 < 4 * E / I := by positivity
      have h_card : Q₀.card + bad.card = P.card :=
        Finset.card_filter_add_card_filter_not (fun q => pointEnergy u P q ≤ 4 * E / I)
      have h_card' : (P.card : ℝ) = (Q₀.card : ℝ) + (bad.card : ℝ) := by
        have h : (Q₀.card + bad.card : ℝ) = (P.card : ℝ) := by exact_mod_cast h_card
        linarith
      by_cases h_bad_empty : bad = ∅
      · have h : (bad.card : ℝ) = 0 := by simp [h_bad_empty]
        have h' : (Q₀.card : ℝ) = (P.card : ℝ) := by linarith
        dsimp only [Q₀]
        rw [h'] <;> simp <;> linarith
      · have h_bad_nonempty : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_bad_empty
        have h_bad_gt : ∀ q ∈ bad, 4 * E / I < pointEnergy u P q := by
          intro q hq
          have h₂ : ¬ pointEnergy u P q ≤ 4 * E / I := (Finset.mem_filter.mp hq).2
          exact lt_of_not_ge h₂
        have h_sum_gt : (4 * E / I) * (bad.card : ℝ) < ∑ q ∈ bad, pointEnergy u P q := by
          have h₃ : ∑ q ∈ bad, (4 * E / I) < ∑ q ∈ bad, pointEnergy u P q :=
            Finset.sum_lt_sum_of_nonempty h_bad_nonempty h_bad_gt
          have h₄ : ∑ q ∈ bad, (4 * E / I) = (bad.card : ℝ) * (4 * E / I) := by
            simp [Finset.sum_const] <;> ring
          rw [h₄] at h₃
          linarith
        have h_bad_sub_P : bad ⊆ P := Finset.filter_subset _ _
        have h_energy_le : ∑ q ∈ bad, pointEnergy u P q ≤ pairEnergy u P :=
          Finset.sum_le_sum_of_subset_of_nonneg h_bad_sub_P
            (fun q _ _ => h_pe_nonneg P q)
        have h_main2 : (4 * E / I) * (bad.card : ℝ) < (2 * E / I) * (P.card : ℝ) := by
          calc
            (4 * E / I) * (bad.card : ℝ) < ∑ q ∈ bad, pointEnergy u P q := h_sum_gt
            _ ≤ pairEnergy u P := h_energy_le
            _ ≤ (2 * E / I) * (P.card : ℝ) := h_avg
        have h_bad_lt : (bad.card : ℝ) < (P.card : ℝ) / 2 := by
          have h₅ : (4 * E / I) * (bad.card : ℝ) < (2 * E / I) * (P.card : ℝ) := h_main2
          calc
            (bad.card : ℝ)
              = ((4 * E / I) * (bad.card : ℝ)) / (4 * E / I) := by field_simp [h_pos.ne'] <;> ring
            _ < ((2 * E / I) * (P.card : ℝ)) / (4 * E / I) := by gcongr
            _ = (P.card : ℝ) / 2 := by
              field_simp [hI.ne', hE_pos.ne'] <;> ring
        dsimp only [Q₀]
        have h_final : (P.card : ℝ) / 2 ≤ (Q₀.card : ℝ) := by
          have h₈ : (Q₀.card : ℝ) = (P.card : ℝ) - (bad.card : ℝ) := by linarith
          rw [h₈]
          linarith
        exact h_final
    have h1 : (P.card : ℝ) ≥ I / (2 * L) := by simpa [P] using h_card
    have h2 : (Q₀.card : ℝ) ≥ (P.card : ℝ) / 2 := hQ₀card
    have h3 : (Q₀.card : ℝ) ≥ I / (4 * L) := by
      calc
        (Q₀.card : ℝ) ≥ (P.card : ℝ) / 2 := h2
        _ ≥ (I / (2 * L)) / 2 := by gcongr
        _ = I / (4 * L) := by ring
    have hQ₀_lower : I ≤ 4 * L * (Q₀.card : ℝ) := by
      have h_pos : 0 < L := hL
      have h' : 4 * L * (Q₀.card : ℝ) ≥ 4 * L * (I / (4 * L)) := by gcongr
      have h'' : 4 * L * (I / (4 * L)) = I := by
        field_simp [h_pos.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have h_energy : ∀ q ∈ Q₀, pointEnergy u Q₀ q ≤ 4 * E / I := by
      intro q hq
      have h1 : pointEnergy u P q ≤ 4 * E / I := (Finset.mem_filter.mp hq).2
      have h2 : pointEnergy u Q₀ q ≤ pointEnergy u P q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.erase_subset_erase q hQ₀subP
        · intro y _ _
          exact Real.rpow_nonneg dist_nonneg _
      exact le_trans h2 h1
    have h_ball : ∀ q ∈ Q₀, ∀ r : ℝ, δ ≤ r →
        ((Q₀.filter fun q' => dist q q' ≤ r).card : ℝ) ≤
          1 + (4 * E / I) * Real.rpow r u := by
      intro q hq r hr
      have hr_pos : 0 < r := by linarith
      have hC : pointEnergy u Q₀ q ≤ 4 * E / I := h_energy q hq
      let A := Q₀.filter fun q' => dist q q' ≤ r
      have hqA : q ∈ A := by
        simp only [A, Finset.mem_filter]
        exact ⟨hq, by simp [hr_pos.le]⟩
      have hA_sub_Q₀ : A ⊆ Q₀ := Finset.filter_subset _ _
      have h1 : A.erase q ⊆ Q₀.erase q := by
        intro x hx
        simp only [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, hA_sub_Q₀ hx.2⟩
      have h2 : ∀ y ∈ A.erase q, Real.rpow r (-u) ≤ Real.rpow (dist q y) (-u) := by
        intro y hy
        have hne : y ≠ q := (Finset.mem_erase.mp hy).1
        have hdist_pos : 0 < dist q y := by exact dist_pos.mpr hne.symm
        have hdist_le : dist q y ≤ r := by
          have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
          exact (Finset.mem_filter.mp hyA).2
        exact Real.rpow_le_rpow_of_nonpos hdist_pos hdist_le (by linarith)
      have h3 : ∀ y ∈ Q₀.erase q, 0 ≤ Real.rpow (dist q y) (-u) := by
        intro y _
        exact Real.rpow_nonneg dist_nonneg _
      have h4 : ∑ y ∈ A.erase q, Real.rpow (dist q y) (-u) ≤ pointEnergy u Q₀ q := by
        have h5 : ∑ y ∈ A.erase q, Real.rpow (dist q y) (-u) ≤ ∑ y ∈ Q₀.erase q, Real.rpow (dist q y) (-u) :=
          Finset.sum_le_sum_of_subset_of_nonneg h1 fun i _ _ => h3 i ‹_›
        exact h5
      have h6 : ((A.erase q).card : ℝ) * Real.rpow r (-u) ≤ ∑ y ∈ A.erase q, Real.rpow (dist q y) (-u) := by
        have h7 : ∑ y ∈ A.erase q, Real.rpow r (-u) ≤ ∑ y ∈ A.erase q, Real.rpow (dist q y) (-u) :=
          Finset.sum_le_sum h2
        have h8 : ∑ y ∈ A.erase q, Real.rpow r (-u) = ((A.erase q).card : ℝ) * Real.rpow r (-u) := by
          simp [Finset.sum_const] <;> ring
        rw [h8] at h7
        exact h7
      have h9 : ((A.erase q).card : ℝ) * Real.rpow r (-u) ≤ 4 * E / I := by
        linarith [hC, h4, h6]
      have hrpow_u_pos : 0 < Real.rpow r u := Real.rpow_pos_of_pos hr_pos u
      have h10 : Real.rpow r (-u) * Real.rpow r u = 1 := by
        have h101 : Real.rpow r ((-u) + u) = Real.rpow r (-u) * Real.rpow r u :=
          Real.rpow_add hr_pos (-u) u
        have h102 : (-u) + u = 0 := by ring
        rw [h102] at h101
        have h103 : Real.rpow r 0 = 1 := Real.rpow_zero r
        rw [h103] at h101
        exact h101.symm
      have h12 : ((A.erase q).card : ℝ) ≤ (4 * E / I) * Real.rpow r u := by
        have h13 : ((A.erase q).card : ℝ) * Real.rpow r (-u) * Real.rpow r u ≤ (4 * E / I) * Real.rpow r u :=
          mul_le_mul_of_nonneg_right h9 hrpow_u_pos.le
        have h14 : ((A.erase q).card : ℝ) * Real.rpow r (-u) * Real.rpow r u = ((A.erase q).card : ℝ) := by
          have h141 : ((A.erase q).card : ℝ) * Real.rpow r (-u) * Real.rpow r u =
              ((A.erase q).card : ℝ) * (Real.rpow r (-u) * Real.rpow r u) := by ring
          rw [h141, h10] <;> ring
        rw [h14] at h13
        exact h13
      have h15 : (A.card : ℝ) = ((A.erase q).card : ℝ) + 1 := by
        have h151 : (A.erase q).card = A.card - 1 := Finset.card_erase_of_mem hqA
        have h152 : (A.erase q).card + 1 = A.card := by
          rw [h151]
          have h153 : 0 < A.card := Finset.card_pos.mpr ⟨q, hqA⟩
          omega
        norm_cast <;> linarith
      have h_main3 : (A.card : ℝ) ≤ 1 + (4 * E / I) * Real.rpow r u := by
        rw [h15] <;> linarith
      exact h_main3
    exact ⟨T₀, hT₀in𝒯, Q₀, hQ₀subP, hQ₀_lower, h_energy, h_ball⟩
  · -- Case E = 0
    have hE0 : E = 0 := by linarith
    have h_all_zero : ∀ T ∈ 𝒯, pairEnergy u (fiber T) = 0 := by
      intro T hT
      have h_nonneg : 0 ≤ pairEnergy u (fiber T) := h_pairEnergy_nonneg (fiber T)
      have h_le : pairEnergy u (fiber T) ≤ ∑ T' ∈ 𝒯, pairEnergy u (fiber T') := by
        apply Finset.single_le_sum (fun T' _ => h_pairEnergy_nonneg (fiber T')) hT
      have h' : pairEnergy u (fiber T) ≤ 0 := by linarith
      have h'' : 0 ≤ pairEnergy u (fiber T) := h_nonneg
      linarith
    have h_fiber_le_one : ∀ T ∈ 𝒯, (fiber T).card ≤ 1 := by
      intro T hT
      have h : pairEnergy u (fiber T) = 0 := h_all_zero T hT
      by_contra h2
      have h3 : 1 < (fiber T).card := by linarith
      have h4 : ∃ (x : X), x ∈ fiber T ∧ ∃ (y : X), y ∈ fiber T ∧ x ≠ y :=
        Finset.one_lt_card.mp h3
      rcases h4 with ⟨x, hx, y, hy, hxy⟩
      have hxQ : x ∈ (Q : Set X) := hfiber T hT hx
      have hyQ : y ∈ (Q : Set X) := hfiber T hT hy
      have hdist : δ ≤ dist x y := hQsep hxQ hyQ hxy
      have hpos : 0 < dist x y := by linarith
      have h5 : y ∈ (fiber T).erase x := by
        exact Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
      have h6 : 0 < Real.rpow (dist x y) (-u) := by
        apply Real.rpow_pos_of_pos
        exact hpos
      have h7 : Real.rpow (dist x y) (-u) ≤ pointEnergy u (fiber T) x := by
        apply Finset.single_le_sum (fun y _ => Real.rpow_nonneg dist_nonneg _) h5
      have h8 : 0 < pointEnergy u (fiber T) x := by linarith
      have h9 : pointEnergy u (fiber T) x ≤ pairEnergy u (fiber T) := by
        apply Finset.single_le_sum (fun z _ => h_pe_nonneg (fiber T) z) hx
      have h10 : 0 < pairEnergy u (fiber T) := by linarith
      rw [h] at h10
      linarith
    have h_sum_card : ∑ T ∈ 𝒯, (fiber T).card ≤ 𝒯.card := by
      calc
        ∑ T ∈ 𝒯, (fiber T).card ≤ ∑ T ∈ 𝒯, 1 := Finset.sum_le_sum (fun T hT => h_fiber_le_one T hT)
        _ = 𝒯.card := by simp
    have hI_le_L : I ≤ L := by
      calc
        I ≤ ∑ T ∈ 𝒯, ((fiber T).card : ℝ) := hincidence
        _ ≤ (𝒯.card : ℝ) := by exact_mod_cast h_sum_card
        _ ≤ L := hcard
    have h_pos_sum' : (0 : ℝ) < ∑ T ∈ 𝒯, ((fiber T).card : ℝ) := by
      calc (0 : ℝ) < I := hI
           _ ≤ ∑ T ∈ 𝒯, ((fiber T).card : ℝ) := hincidence
    have h_pos_sum : 0 < ∑ T ∈ 𝒯, (fiber T).card := by
      exact_mod_cast h_pos_sum'
    have h_exists : ∃ T₀ ∈ 𝒯, 0 < (fiber T₀).card := by
      by_contra h
      push Not at h
      have h' : ∑ T ∈ 𝒯, (fiber T).card = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        have hle : (fiber T).card ≤ 0 := h T hT
        have hnot : ¬ 0 < (fiber T).card := by
          intro hpos
          linarith
        exact Nat.eq_zero_of_not_pos hnot
      rw [h'] at h_pos_sum
      simp at h_pos_sum
    rcases h_exists with ⟨T₀, hT₀, hcard_pos⟩
    have hcard_one : (fiber T₀).card = 1 := by
      have h_le : (fiber T₀).card ≤ 1 := h_fiber_le_one T₀ hT₀
      omega
    let Q₀ := fiber T₀
    have hQ₀_card : Q₀.card = 1 := hcard_one
    have hQ₀sub : Q₀ ⊆ fiber T₀ := rfl.subset
    have hcard_bound : I ≤ 4 * L * (Q₀.card : ℝ) := by
      rw [hQ₀_card]
      norm_num <;> linarith
    have hE0' : 4 * E / I = 0 := by
      rw [hE0] <;> field_simp [hI.ne'] <;> ring
    have henergy_bound : ∀ q ∈ Q₀, pointEnergy u Q₀ q ≤ 0 := by
      intro q hq
      have h_erase : Q₀.erase q = ∅ := by
        have h_card_erase : (Q₀.erase q).card = 0 := by
          rw [Finset.card_erase_of_mem hq, hQ₀_card] <;> norm_num
        exact Finset.card_eq_zero.mp h_card_erase
      have h_pe : pointEnergy u Q₀ q = 0 := by
        rw [pointEnergy, h_erase] <;> simp
      rw [h_pe] <;> norm_num
    have h_energy : ∀ q ∈ Q₀, pointEnergy u Q₀ q ≤ 4 * E / I := by
      rw [hE0']
      exact henergy_bound
    have hball_bound : ∀ q ∈ Q₀, ∀ r : ℝ, δ ≤ r →
        ((Q₀.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 := by
      intro q _ r _
      have h_filter_subset : (Q₀.filter fun q' => dist q q' ≤ r) ⊆ Q₀ := Finset.filter_subset _ _
      have h_card_le : (Q₀.filter fun q' => dist q q' ≤ r).card ≤ Q₀.card := Finset.card_le_card h_filter_subset
      rw [hQ₀_card] at h_card_le
      exact_mod_cast h_card_le
    have h_ball : ∀ q ∈ Q₀, ∀ r : ℝ, δ ≤ r →
        ((Q₀.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + (4 * E / I) * Real.rpow r u := by
      intro q hq r hr
      rw [hE0']
      <;> simpa using hball_bound q hq r hr
    exact ⟨T₀, hT₀, Q₀, hQ₀sub, hcard_bound, h_energy, h_ball⟩

end
