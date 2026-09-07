import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.WeightBinning
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.TCore
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.HeavyColorClass
import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Simultaneous degree regularization for m-partite hypergraphs

Given finite coordinate maps `parent k : I → J k` and `ENNReal` edge weights,
extract a subfamily `S` such that:
1. At every scale `k`, all nonempty vertex degrees are within factor
   `16 * m * L^m` of each other, where `L = Nat.log 2 (2 * |I|) + 1`.
2. The retained mass satisfies `total ≤ 8 * L^(m+1) * mass(S)`.
-/

noncomputable section

open Classical Finset

namespace Kakeya.Assouad

lemma simultaneous_degree_regularization_with_support_and_weight_band
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (J : Fin m → Type _)
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (w : I → ENNReal) :
    ∃ (S : Finset I),
      (∀ k, ∀ (j j' : J k),
        0 < (S.filter (fun i => parent k i = j)).card →
        0 < (S.filter (fun i => parent k i = j')).card →
        ((S.filter (fun i => parent k i = j)).card : ENNReal) ≤
          (16 * (m : ENNReal) * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^m) *
          ((S.filter (fun i => parent k i = j')).card : ENNReal)) ∧
      (∑ i : I, w i) ≤
        (8 : ENNReal) * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^(m + 1) *
          (∑ i ∈ S, w i) ∧
      (∀ i ∈ S, 0 < w i) ∧
      (0 < m →
        ∀ i ∈ S,
          (∑ source : I, w source) /
              (2 * Fintype.card I : ENNReal) ≤
            w i) ∧
      (0 < m →
        ∃ weightLevel : ENNReal,
          0 < weightLevel ∧
          ∀ i ∈ S,
            weightLevel ≤ w i ∧
            w i ≤ 2 * weightLevel) := by
  classical
  let n := Fintype.card I
  let L : ℕ := Nat.log 2 (2 * n) + 1
  let total : ENNReal := ∑ i, w i

  -- Case 1: total = 0
  by_cases h_total_zero : total = 0
  · refine ⟨∅, ?_, ?_, ?_, ?_, ?_⟩
    · intro k j j' hpos _; simp at hpos <;> tauto
    · have h9 : (∑ i : I, w i) = 0 := by simpa [total] using h_total_zero
      rw [h9]; simp
    · simp
    · simp
    · intro _
      exact ⟨1, by norm_num, by simp⟩
  have h_total_pos : 0 < total := by
    by_cases h : 0 < total
    · exact h
    · have h' : total = 0 := by simpa [not_lt] using h
      exact False.elim (h_total_zero h')

  -- Case 2: m = 0
  by_cases h_m0 : m = 0
  · subst h_m0
    let S := Finset.univ.filter fun i => 0 < w i
    have hsum : ∑ i ∈ S, w i = total := by
      simp only [S, Finset.sum_filter]
      rw [show total = ∑ i ∈ Finset.univ, w i by simp [total]]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hwi : 0 < w i
      · simp [hwi]
      · have hw0 : w i = 0 := by simpa [not_lt] using hwi
        simp [hwi, hw0]
    refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; exfalso; fin_cases k
    · have hL_pos : 0 < L := by simp [L] <;> omega
      have h10 : total ≤ (8 : ENNReal) * (L : ENNReal) * total := by
        have h11 : (1 : ENNReal) ≤ (8 : ENNReal) * (L : ENNReal) := by
          have h12 : (1 : ENNReal) ≤ (L : ENNReal) := by exact_mod_cast hL_pos
          have h13 : (1 : ENNReal) ≤ (8 : ENNReal) := by norm_num
          have h14 : (L : ENNReal) ≤ (8 : ENNReal) * (L : ENNReal) := by
            have h15 : (1 : ENNReal) * (L : ENNReal) ≤ (8 : ENNReal) * (L : ENNReal) :=
              mul_le_mul_of_nonneg_right h13 (by positivity)
            simpa using h15
          exact le_trans h12 h14
        calc
          total = 1 * total := by simp
          _ ≤ (8 : ENNReal) * (L : ENNReal) * total := by gcongr
      have h_final : (∑ i : I, w i) ≤ (8 : ENNReal) * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (0 + 1) * (∑ i ∈ S, w i) := by
        rw [hsum]
        simpa [L, total, pow_succ] using h10
      exact h_final
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · simp
    · simp

  have h_m_pos : 0 < m := by omega

  -- Case 3: some w i = ⊤
  by_cases h_top : ∃ i, w i = ⊤
  · rcases h_top with ⟨i, hi⟩
    have h_singleton_filter : ∀ (p : I → Prop) [DecidablePred p],
        (Finset.filter p ({i} : Finset I)).Nonempty →
        Finset.filter p ({i} : Finset I) = ({i} : Finset I) := by
      intro p _ hp
      rcases hp with ⟨x, hx⟩
      have hxi : x = i := by
        have h : x ∈ ({i} : Finset I) := (Finset.mem_filter.mp hx).1
        simpa using h
      have hpi : p i := by
        rw [hxi] at hx
        exact (Finset.mem_filter.mp hx).2
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h; exact h.1
      · intro hz; rw [hz]; exact ⟨by simp, hpi⟩
    refine ⟨{i}, ?_, ?_, ?_, ?_, ?_⟩
    · intro k j j' hpos hpos'
      have h1 : (Finset.filter (fun i => parent k i = j) ({i} : Finset I)).card = 1 := by
        have hne : (Finset.filter (fun i => parent k i = j) ({i} : Finset I)).Nonempty :=
          Finset.card_pos.mp hpos
        rw [h_singleton_filter (fun i => parent k i = j) hne]; simp
      have h2 : (Finset.filter (fun i => parent k i = j') ({i} : Finset I)).card = 1 := by
        have hne : (Finset.filter (fun i => parent k i = j') ({i} : Finset I)).Nonempty :=
          Finset.card_pos.mp hpos'
        rw [h_singleton_filter (fun i => parent k i = j') hne]; simp
      rw [h1, h2]
      have h4 : 1 ≤ m := by exact_mod_cast h_m_pos
      have h5 : 1 ≤ L := by simp [L] <;> omega
      have h6 : (1 : ENNReal) ≤ (m : ENNReal) := by exact_mod_cast h4
      have h7 : (1 : ENNReal) ≤ (L : ENNReal)^m := by
        have h71 : (1 : ENNReal) ≤ (L : ENNReal) := by exact_mod_cast h5
        have h72 : ∀ n : ℕ, (1 : ENNReal) ≤ (L : ENNReal)^n := by
          intro n; induction n with
          | zero => norm_num
          | succ n ih => calc
            (1 : ENNReal) ≤ (1 : ENNReal) * (1 : ENNReal) := by norm_num
            _ ≤ (L : ENNReal)^n * (L : ENNReal) := by gcongr
            _ = (L : ENNReal)^(n + 1) := by ring
        exact h72 m
      have h8 : (1 : ENNReal) ≤ (16 : ENNReal) := by norm_num
      have h9 : (1 : ENNReal) ≤ (16 : ENNReal) * (m : ENNReal) := by
        have h91 : (1 : ENNReal) * (1 : ENNReal) ≤ (16 : ENNReal) * (m : ENNReal) :=
          mul_le_mul h8 h6 (by positivity) (by positivity)
        have h92 : (1 : ENNReal) * (1 : ENNReal) = (1 : ENNReal) := by norm_num
        rw [h92] at h91
        exact h91
      have h_goal : (1 : ENNReal) ≤ (16 * (m : ENNReal) * (L : ENNReal)^m) := by
        have h10 : (1 : ENNReal) * (1 : ENNReal) ≤ ((16 : ENNReal) * (m : ENNReal)) * (L : ENNReal)^m :=
          mul_le_mul h9 h7 (by positivity) (by positivity)
        have h11 : (1 : ENNReal) * (1 : ENNReal) = (1 : ENNReal) := by norm_num
        rw [h11] at h10
        simpa [mul_assoc] using h10
      have hL_unfold : (L : ENNReal) = (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) := by
        simp [L, n] <;> rfl
      have h_goal2 : (1 : ENNReal) ≤ (16 * (m : ENNReal) * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^m) := by
        rw [hL_unfold] at h_goal
        exact h_goal
      simpa [mul_one] using h_goal2
    · have h7 : w i = ⊤ := hi
      have h8 : ∑ i ∈ ({i} : Finset I), w i = ⊤ := by
        simp [h7, Finset.sum_singleton]
      rw [h8]; simp
    · intro z hz
      have hzi : z = i := by simpa using hz
      subst z
      simp [hi]
    · intro _ z hz
      have hzi : z = i := by simpa using hz
      subst z
      simp [hi]
    · intro _
      refine ⟨⊤, by simp, ?_⟩
      intro z hz
      have hzi : z = i := by simpa using hz
      subst z
      simp [hi]
  have h_no_top : ∀ i, w i ≠ ⊤ := by
    intro i; by_contra h; exact h_top ⟨i, h⟩
  have h_total_lt_top : total ≠ ⊤ := by
    have h : (∑ i : I, w i) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => h_no_top i)
    simpa [total] using h

  have hL_pos : 0 < L := by simp [L] <;> omega

  -- Step 1: Weight binning
  rcases ennreal_dyadic_bin w total rfl h_total_lt_top h_total_pos with
    ⟨bins, I'', h_bins_eq, hI''_nonempty, h_mass_I'',
      h_weight_floor, ⟨c, hc_pos, hc_ratio⟩⟩
  have hL_eq : L = bins := by
    have h : L = Nat.log 2 (2 * n) + 1 := by
      simp only [L, n]
      <;> rfl
    have h5 : n = Fintype.card I := by simp [n]
    rw [h, h5, h_bins_eq]
  have h_wmin : ∀ i ∈ I'', c ≤ w i := fun i hi => (hc_ratio i hi).1
  have h_wmax : ∀ i ∈ I'', w i ≤ 2 * c := fun i hi => (hc_ratio i hi).2
  have hc_ne_top : c ≠ ⊤ := by
    rcases hI''_nonempty with ⟨i, hi⟩
    have h2 : c ≤ w i := h_wmin i hi
    have h3 : w i ≠ ⊤ := h_no_top i
    exact ne_top_of_le_ne_top h3 h2
  have h_total_mass : total ≤ (2 : ENNReal) * (L : ENNReal) * (∑ i ∈ I'', w i) := by
    have h1 : (∑ i ∈ I'', w i) * (bins : ENNReal) ≥ total / 2 := h_mass_I''
    have h1' : (∑ i ∈ I'', w i) * (L : ENNReal) ≥ total / 2 := by
      have h_eq : (L : ENNReal) = (bins : ENNReal) := by exact_mod_cast hL_eq
      rw [h_eq]; exact h1
    have h2 : total / 2 * (2 : ENNReal) = total := by
      have h3 : total / 2 + total / 2 = total := ENNReal.add_halves total
      have h4 : total / 2 * (2 : ENNReal) = total / 2 + total / 2 := by ring
      rw [h4, h3]
    calc
      total = total / 2 * (2 : ENNReal) := h2.symm
      _ ≤ ((∑ i ∈ I'', w i) * (L : ENNReal)) * (2 : ENNReal) := by gcongr
      _ = (2 : ENNReal) * (L : ENNReal) * (∑ i ∈ I'', w i) := by ring

  -- Step 2: Degree vector binning
  let deg (k : Fin m) (i : I) : ℕ :=
    (I''.filter (fun i' => parent k i' = parent k i)).card
  have h_deg_pos : ∀ i ∈ I'', ∀ k : Fin m, 0 < deg k i := by
    intro i hi k
    have h : i ∈ I''.filter (fun i' => parent k i' = parent k i) := by
      simp [deg, Finset.mem_filter, hi]
    exact Finset.card_pos.mpr ⟨i, h⟩
  have h_deg_le_n : ∀ (i : I) (k : Fin m), deg k i ≤ n := by
    intro i k
    have h : I''.filter (fun i' => parent k i' = parent k i) ⊆ Finset.univ := by
      apply Finset.Subset.trans (Finset.filter_subset _ _)
      exact Finset.subset_univ _
    exact Finset.card_le_card h
  have h_bins_pos : 0 < bins := by
    have h : bins = L := h_bins_eq
    rw [h]; simp [L] <;> omega
  have h_log_lt_bins : ∀ (i : I) (k : Fin m), Nat.log 2 (deg k i) < bins := by
    intro i k
    by_cases h : 0 < deg k i
    · have h1 : deg k i ≤ n := h_deg_le_n i k
      have h2 : Nat.log 2 (deg k i) ≤ Nat.log 2 n :=
        Nat.log_mono (show 1 < 2 from by norm_num) (show (2 : ℕ) ≤ 2 from by norm_num) h1
      have h3 : Nat.log 2 n ≤ Nat.log 2 (2 * n) :=
        Nat.log_mono (show 1 < 2 from by norm_num) (show (2 : ℕ) ≤ 2 from by norm_num) (by omega)
      have h4 : Nat.log 2 (2 * n) + 1 = bins := by
        have h5 : n = Fintype.card I := by simp [n]
        rw [h5]
        exact h_bins_eq.symm
      have h5 : Nat.log 2 (deg k i) < Nat.log 2 (2 * n) + 1 := by linarith
      rw [h4] at h5; exact h5
    · have h5 : deg k i = 0 := by omega
      rw [h5]
      exact h_bins_pos
  let degreeVec (i : I) : Fin m → Fin bins := fun k =>
    ⟨Nat.log 2 (deg k i), h_log_lt_bins i k⟩
  let e : (Fin m → Fin bins) ≃ Fin (bins ^ m) := by
    simpa [Fintype.card_fun] using Fintype.equivFin (Fin m → Fin bins)
  let color (i : I) : Fin (bins ^ m) := e (degreeVec i)
  have h_binsm_pos : 0 < bins ^ m := by positivity
  rcases exists_heavy_color_class I'' (bins ^ m) h_binsm_pos color w with ⟨c_vec, hmass⟩
  let S0 := I''.filter (fun i => color i = c_vec)
  have h_mass_S0 : (∑ i ∈ I'', w i) ≤ (bins ^ m : ENNReal) * (∑ i ∈ S0, w i) := by
    simpa [S0] using hmass
  have h_S0_nonempty : S0.Nonempty := by
    by_contra h
    have h' : S0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h_sum0 : (∑ i ∈ S0, w i) = 0 := by
      rw [h']; simp
    have h_contra : (∑ i ∈ I'', w i) ≤ 0 := by
      rw [h_sum0] at h_mass_S0
      simpa using h_mass_S0
    have h_sum_pos : 0 < ∑ i ∈ I'', w i := by
      rcases hI''_nonempty with ⟨i, hi⟩
      have h1 : c ≤ w i := h_wmin i hi
      have h2 : 0 < w i := lt_of_lt_of_le hc_pos h1
      have h3 : w i ≤ ∑ j ∈ I'', w j := Finset.single_le_sum (fun _ _ => by positivity) hi
      exact lt_of_lt_of_le h2 h3
    exact not_le.mpr h_sum_pos h_contra
  rcases h_S0_nonempty with ⟨i0, hi0⟩
  have hi0_I'' : i0 ∈ I'' := (Finset.mem_filter.mp hi0).1
  let b : Fin m → ℕ := fun k => Nat.log 2 (deg k i0)
  have h_common_bin : ∀ i ∈ S0, ∀ k : Fin m, Nat.log 2 (deg k i) = b k := by
    intro i hi k
    have hci1 : color i = c_vec := (Finset.mem_filter.mp hi).2
    have hci0 : color i0 = c_vec := (Finset.mem_filter.mp hi0).2
    have hci : color i = color i0 := by rw [hci1, hci0]
    have hvec : degreeVec i = degreeVec i0 := by
      have h : e (degreeVec i) = e (degreeVec i0) := hci
      exact e.injective h
    have h := congr_fun hvec k
    simpa [degreeVec, b] using h
  have h_degree_range : ∀ i ∈ S0, ∀ k : Fin m,
      2 ^ b k ≤ deg k i ∧ deg k i < 2 ^ (b k + 1) := by
    intro i hi k
    have h_eq : Nat.log 2 (deg k i) = b k := h_common_bin i hi k
    have h_pos : 0 < deg k i := h_deg_pos i ((Finset.mem_filter.mp hi).1) k
    have h_ne_zero : deg k i ≠ 0 := by linarith
    have h1 : 2 ^ (Nat.log 2 (deg k i)) ≤ deg k i := Nat.pow_log_le_self 2 h_ne_zero
    have h2 : deg k i < 2 ^ (Nat.log 2 (deg k i) + 1) := Nat.lt_pow_succ_log_self (show 1 < 2 from by norm_num) (deg k i)
    rw [h_eq] at h1 h2
    exact ⟨h1, h2⟩

  -- Vertex bound: |S0.image(parent k)| * 2^b_k ≤ I''.card
  have h_vertex_bound : ∀ k : Fin m,
      (S0.image (parent k)).card * 2 ^ b k ≤ I''.card := by
    intro k
    let fibers : Finset (J k) := S0.image (parent k)
    have h_disj : ∀ j1 ∈ fibers, ∀ j2 ∈ fibers, j1 ≠ j2 →
        Disjoint (I''.filter (fun i => parent k i = j1))
                 (I''.filter (fun i => parent k i = j2)) := by
      intro j1 _ j2 _ hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : parent k x = j1 := (Finset.mem_filter.mp hx1).2
      have h2 : parent k x = j2 := (Finset.mem_filter.mp hx2).2
      rw [h1] at h2; exact hne h2
    have h_sub : ∀ j ∈ fibers, (I''.filter (fun i => parent k i = j)).card ≥ 2 ^ b k := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      exact (h_degree_range i hi k).1
    have h_sum : ∑ j ∈ fibers, (I''.filter (fun i => parent k i = j)).card ≤ I''.card := by
      have h_union : (Finset.biUnion fibers (fun j => I''.filter (fun i => parent k i = j))) ⊆ I'' := by
        intro i hi
        rcases Finset.mem_biUnion.mp hi with ⟨j, _, hji⟩
        exact (Finset.mem_filter.mp hji).1
      calc
        ∑ j ∈ fibers, (I''.filter (fun i => parent k i = j)).card
          = (Finset.biUnion fibers (fun j => I''.filter (fun i => parent k i = j))).card :=
          (Finset.card_biUnion h_disj).symm
        _ ≤ I''.card := Finset.card_le_card h_union
    have h_card_sum : fibers.card * 2 ^ b k = ∑ j ∈ fibers, (2 ^ b k) := by
      simp [Finset.sum_const] <;> ring
    calc
      fibers.card * 2 ^ b k
        = ∑ j ∈ fibers, (2 ^ b k) := h_card_sum
      _ ≤ ∑ j ∈ fibers, (I''.filter (fun i => parent k i = j)).card := by
          apply Finset.sum_le_sum
          intro j hj
          exact h_sub j hj
      _ ≤ I''.card := h_sum

  -- Bound I''.card ≤ 2 * bins^m * S0.card (in ENNReal)
  have h_mass_I''_lower : c * (I''.card : ENNReal) ≤ (∑ i ∈ I'', w i) := by
    calc
      c * (I''.card : ENNReal)
        = ∑ i ∈ I'', c := by simp [Finset.sum_const] <;> ring
      _ ≤ ∑ i ∈ I'', w i := Finset.sum_le_sum (fun i hi => h_wmin i hi)
  have h_mass_S0_upper : (∑ i ∈ S0, w i) ≤ 2 * c * (S0.card : ENNReal) := by
    calc
      (∑ i ∈ S0, w i)
        ≤ ∑ i ∈ S0, (2 * c) := Finset.sum_le_sum (fun i hi => h_wmax i ((Finset.mem_filter.mp hi).1))
      _ = 2 * c * (S0.card : ENNReal) := by simp [Finset.sum_const] <;> ring
  have h1 : c * (I''.card : ENNReal) ≤
      c * (2 * (bins ^ m : ENNReal) * (S0.card : ENNReal)) := by
    calc
      c * (I''.card : ENNReal)
        ≤ (∑ i ∈ I'', w i) := h_mass_I''_lower
      _ ≤ (bins ^ m : ENNReal) * (∑ i ∈ S0, w i) := h_mass_S0
      _ ≤ (bins ^ m : ENNReal) * (2 * c * (S0.card : ENNReal)) := by gcongr
      _ = c * (2 * (bins ^ m : ENNReal) * (S0.card : ENNReal)) := by ring
  have h1' : (I''.card : ENNReal) * c ≤ (2 * (bins ^ m : ENNReal) * (S0.card : ENNReal)) * c := by
    have h_comm1 : c * (I''.card : ENNReal) = (I''.card : ENNReal) * c := by ring
    have h_comm2 : c * (2 * (bins ^ m : ENNReal) * (S0.card : ENNReal)) =
        (2 * (bins ^ m : ENNReal) * (S0.card : ENNReal)) * c := by ring
    rw [h_comm1, h_comm2] at h1
    exact h1
  have h_card_bound : (I''.card : ENNReal) ≤ 2 * (bins ^ m : ENNReal) * (S0.card : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hc_pos.ne' hc_ne_top).mp h1'
  have h_card_bound_nat : I''.card ≤ 2 * bins ^ m * S0.card := by
    exact_mod_cast h_card_bound

  -- Step 3: T-core pruning
  let D : ℕ := 4 * m * bins ^ m
  let T : Fin m → ℕ := fun k => (2 ^ b k) / D
  rcases t_core_existence parent T S0 with ⟨S', hS'_sub, hS'_core, h_removed⟩

  -- Helper: (a / D) * b ≤ (a * b) / D
  have h_div_mul : ∀ (a b : ℕ), (a / D) * b ≤ (a * b) / D := by
    intro a b
    have hq : (a / D) * D ≤ a := Nat.div_mul_le_self a D
    have h : (a / D) * b * D ≤ a * b := by
      calc
        (a / D) * b * D = b * ((a / D) * D) := by ring
        _ ≤ b * a := by gcongr
        _ = a * b := by ring
    have h_posD : 0 < D := by positivity
    have h2 : (a / D) * b ≤ (a * b) / D := by
      rw [Nat.le_div_iff_mul_le h_posD]
      exact h
    exact h2

  -- Bound removed edges: (S0 \ S').card ≤ S0.card / 2
  have h_per_k : ∀ k : Fin m,
      T k * (S0.image (parent k)).card ≤ I''.card / D := by
    intro k
    have h1 : T k * (S0.image (parent k)).card ≤
        (2 ^ b k * (S0.image (parent k)).card) / D := h_div_mul (2 ^ b k) (S0.image (parent k)).card
    have h2 : 2 ^ b k * (S0.image (parent k)).card ≤ I''.card := by
      have h3 := h_vertex_bound k
      ring_nf at h3 ⊢ <;> exact h3
    have h4 : (2 ^ b k * (S0.image (parent k)).card) / D ≤ I''.card / D := Nat.div_le_div_right h2
    exact le_trans h1 h4
  have h_sum_removed : (S0 \ S').card ≤ ∑ k : Fin m, I''.card / D := by
    calc
      (S0 \ S').card
        ≤ ∑ k : Fin m, T k * (S0.image (parent k)).card := h_removed
      _ ≤ ∑ k : Fin m, I''.card / D := Finset.sum_le_sum (fun k _ => h_per_k k)
  have h_m_div : ∑ k : Fin m, I''.card / D = m * (I''.card / D) := by
    simp [Finset.sum_const, Fintype.card_fin] <;> ring
  rw [h_m_div] at h_sum_removed
  have h_m_div2 : m * (I''.card / D) ≤ I''.card / (4 * bins ^ m) := by
    let q := I''.card / D
    have hq : q * D ≤ I''.card := Nat.div_mul_le_self I''.card D
    have h : m * q * (4 * bins ^ m) ≤ I''.card := by
      calc
        m * q * (4 * bins ^ m) = q * D := by
          simp [D, mul_assoc] <;> ring
        _ ≤ I''.card := hq
    have h_pos2 : 0 < 4 * bins ^ m := by positivity
    exact (Nat.le_div_iff_mul_le h_pos2).mpr h
  have h_removed_le : (S0 \ S').card ≤ I''.card / (4 * bins ^ m) :=
    le_trans h_sum_removed h_m_div2
  have h_removed_le2 : (S0 \ S').card ≤ S0.card / 2 := by
    calc
      (S0 \ S').card
        ≤ I''.card / (4 * bins ^ m) := h_removed_le
      _ ≤ (2 * bins ^ m * S0.card) / (4 * bins ^ m) := Nat.div_le_div_right h_card_bound_nat
      _ = S0.card / 2 := by
        let a := 2 * bins ^ m
        have ha_pos : 0 < a := by positivity
        have h_eq : a * S0.card / (a * 2) = S0.card / 2 := by
          apply Nat.div_eq_of_lt_le
          · -- lower bound
            have h5 : (S0.card / 2) * 2 ≤ S0.card := Nat.div_mul_le_self S0.card 2
            calc
              (S0.card / 2) * (a * 2) = a * ((S0.card / 2) * 2) := by ring
              _ ≤ a * S0.card := by gcongr
          · -- upper bound
            have h5 : S0.card < (S0.card / 2 + 1) * 2 := by omega
            calc
              a * S0.card < a * ((S0.card / 2 + 1) * 2) := by gcongr
              _ = (S0.card / 2 + 1) * (a * 2) := by ring
        simpa [a, mul_assoc, mul_comm, mul_left_comm] using h_eq
  have hS0_sub_I'' : S0 ⊆ I'' := Finset.filter_subset _ _
  have hS'_card_lower : 2 * S'.card ≥ S0.card := by
    have h1 : (S0 \ S').card = S0.card - S'.card := Finset.card_sdiff_of_subset hS'_sub
    have h2 : (S0 \ S').card ≤ S0.card / 2 := h_removed_le2
    rw [h1] at h2
    omega
  have hS'_nonempty : S'.Nonempty := by
    have hS0_card_pos : 0 < S0.card := by
      rcases hI''_nonempty with ⟨i, hi⟩
      have h1 : c ≤ w i := h_wmin i hi
      have h2 : 0 < w i := lt_of_lt_of_le hc_pos h1
      have h3 : w i ≤ ∑ j ∈ I'', w j := Finset.single_le_sum (fun _ _ => by positivity) hi
      have h4 : 0 < ∑ j ∈ I'', w j := lt_of_lt_of_le h2 h3
      by_contra h5
      have h6 : S0 = ∅ := by simpa using h5
      have h7 : ∑ i ∈ S0, w i = 0 := by rw [h6]; simp
      rw [h7] at h_mass_S0
      have h8 : ∑ i ∈ I'', w i ≤ 0 := by simpa using h_mass_S0
      exact not_le.mpr h4 h8
    have h2 : 0 < S'.card := by omega
    exact Finset.card_pos.mp h2

  -- Step 4: Mass retention
  have h_mass_S'_lower : c * (S'.card : ENNReal) ≤ (∑ i ∈ S', w i) := by
    calc
      c * (S'.card : ENNReal)
        = ∑ i ∈ S', c := by simp [Finset.sum_const] <;> ring
      _ ≤ ∑ i ∈ S', w i := Finset.sum_le_sum (fun i hi => h_wmin i (hS0_sub_I'' (hS'_sub hi)))
  have h4 : (S0.card : ENNReal) ≤ 2 * (S'.card : ENNReal) := by
    exact_mod_cast hS'_card_lower
  have h5 : (∑ i ∈ S0, w i) ≤ 4 * (∑ i ∈ S', w i) := by
    calc
      (∑ i ∈ S0, w i)
        ≤ 2 * c * (S0.card : ENNReal) := h_mass_S0_upper
      _ ≤ 2 * c * (2 * (S'.card : ENNReal)) := by gcongr
      _ = 4 * (c * (S'.card : ENNReal)) := by ring
      _ ≤ 4 * (∑ i ∈ S', w i) := by gcongr <;> exact h_mass_S'_lower
  have hL_eq' : (L : ENNReal) = (bins : ENNReal) := by exact_mod_cast hL_eq
  have h6 : total ≤ (8 : ENNReal) * (L : ENNReal) ^ (m + 1) * (∑ i ∈ S', w i) := by
    calc
      total
        ≤ (2 : ENNReal) * (L : ENNReal) * (∑ i ∈ I'', w i) := h_total_mass
      _ ≤ (2 : ENNReal) * (L : ENNReal) * ((bins ^ m : ENNReal) * (∑ i ∈ S0, w i)) := by gcongr
      _ = (2 : ENNReal) * (L : ENNReal) ^ (m + 1) * (∑ i ∈ S0, w i) := by
        simp [pow_succ, hL_eq'] <;> ring
      _ ≤ (2 : ENNReal) * (L : ENNReal) ^ (m + 1) * (4 * (∑ i ∈ S', w i)) := by gcongr
      _ = (8 : ENNReal) * (L : ENNReal) ^ (m + 1) * (∑ i ∈ S', w i) := by ring

  -- Step 5: Uniformity
  have h_uniformity : ∀ (k : Fin m) (j j' : J k),
      0 < (S'.filter (fun i => parent k i = j)).card →
      0 < (S'.filter (fun i => parent k i = j')).card →
      ((S'.filter (fun i => parent k i = j)).card : ENNReal) ≤
        (16 * (m : ENNReal) * (L : ENNReal)^m) *
        ((S'.filter (fun i => parent k i = j')).card : ENNReal) := by
    intro k j j' hj_pos hj'_pos
    let d := (S'.filter (fun i => parent k i = j)).card
    let d' := (S'.filter (fun i => parent k i = j')).card
    have h_d_max : d < 2 ^ (b k + 1) := by
      have hS'_sub_I''2 : S' ⊆ I'' := Finset.Subset.trans hS'_sub hS0_sub_I''
      have h1 : d ≤ (I''.filter (fun i => parent k i = j)).card :=
        Finset.card_le_card (Finset.filter_subset_filter (fun i => parent k i = j) hS'_sub_I''2)
      by_cases h_j_in : j ∈ S'.image (parent k)
      · rcases Finset.mem_image.mp h_j_in with ⟨i, hi, rfl⟩
        have h_i_in_S0 : i ∈ S0 := hS'_sub hi
        have h2 : (I''.filter (fun i' => parent k i' = parent k i)).card = deg k i := by rfl
        have h3 : deg k i < 2 ^ (b k + 1) := (h_degree_range i h_i_in_S0 k).2
        rw [h2] at h1
        exact lt_of_le_of_lt h1 h3
      · have h5 : d = 0 := by
          by_contra h51
          have h51' : 0 < d := Nat.pos_of_ne_zero h51
          have h52 : (S'.filter (fun i => parent k i = j)).Nonempty := Finset.card_pos.mp h51'
          rcases h52 with ⟨i, hi⟩
          have h53 : i ∈ S' := (Finset.mem_filter.mp hi).1
          have h54 : parent k i = j := (Finset.mem_filter.mp hi).2
          have h55 : j ∈ S'.image (parent k) := Finset.mem_image.mpr ⟨i, h53, h54⟩
          exact h_j_in h55
        rw [h5] <;> positivity
    have h_d'_min : T k ≤ d' := hS'_core k j' hj'_pos
    by_cases hT : T k = 0
    · -- Case T k = 0
      have h_b_small : 2 ^ b k < D := by
        have h_posD : 0 < D := by positivity
        have h : (2 ^ b k) / D = 0 := hT
        have h_iff : (2 ^ b k) / D = 0 ↔ D = 0 ∨ 2 ^ b k < D := Nat.div_eq_zero_iff
        have h_or : D = 0 ∨ 2 ^ b k < D := h_iff.mp h
        cases h_or with
        | inl hD0 => exfalso; linarith
        | inr hlt => exact hlt
      have h_d_max2 : d < 8 * m * bins ^ m := by
        calc
          d < 2 ^ (b k + 1) := h_d_max
          _ = 2 * 2 ^ b k := by ring
          _ < 2 * D := by gcongr
          _ = 8 * m * bins ^ m := by simp [D] <;> ring
      have h_d'_pos : 0 < d' := hj'_pos
      have h_ineq : (d : ENNReal) ≤ (16 * (m : ENNReal) * (L : ENNReal)^m) * (d' : ENNReal) := by
        have h6 : (d : ENNReal) < (8 * (m : ENNReal) * (bins : ENNReal)^m) := by exact_mod_cast h_d_max2
        have h7 : (8 * (m : ENNReal) * (L : ENNReal)^m) = (8 * (m : ENNReal) * (bins : ENNReal)^m) := by
          rw [hL_eq']
        have h9 : (8 * (m : ENNReal) * (bins : ENNReal)^m) ≤
            (16 * (m : ENNReal) * (L : ENNReal)^m) * (d' : ENNReal) := by
          rw [hL_eq']
          have h10 : (1 : ENNReal) ≤ (d' : ENNReal) := by exact_mod_cast h_d'_pos
          calc
            (8 * (m : ENNReal) * (bins : ENNReal)^m)
              ≤ (16 * (m : ENNReal) * (bins : ENNReal)^m) := by
                have h11 : (8 : ENNReal) ≤ (16 : ENNReal) := by norm_num
                gcongr <;> positivity
            _ = (16 * (m : ENNReal) * (bins : ENNReal)^m) * 1 := by ring
            _ ≤ (16 * (m : ENNReal) * (bins : ENNReal)^m) * (d' : ENNReal) := by gcongr
        exact le_of_lt (lt_of_lt_of_le h6 h9)
      exact h_ineq
    · -- Case T k > 0
      have hT_pos : 0 < T k := Nat.pos_of_ne_zero hT
      have h1 : 2 ^ b k < 2 * D * T k := by
        have h_posD : 0 < D := by positivity
        have h21 : T k < T k + 1 := by omega
        have h22 : (2 ^ b k) / D < T k + 1 := by simpa [T] using h21
        have h2 : 2 ^ b k < D * (T k + 1) := by
          have h23 : 2 ^ b k < (T k + 1) * D := (Nat.div_lt_iff_lt_mul h_posD).mp h22
          have h24 : (T k + 1) * D = D * (T k + 1) := by ring
          rw [h24] at h23
          exact h23
        have h3 : D * (T k + 1) ≤ 2 * D * T k := by
          have h4 : T k + 1 ≤ 2 * T k := by omega
          have h5 : D * (T k + 1) ≤ D * (2 * T k) := by gcongr
          have h6 : D * (2 * T k) = 2 * D * T k := by ring
          rw [h6] at h5
          exact h5
        exact lt_of_lt_of_le h2 h3
      have h_d_max3 : d < 16 * m * bins ^ m * T k := by
        calc
          d < 2 ^ (b k + 1) := h_d_max
          _ = 2 * 2 ^ b k := by ring
          _ < 2 * (2 * D * T k) := by gcongr
          _ = 16 * m * bins ^ m * T k := by simp [D] <;> ring
      have h_ineq : (d : ENNReal) ≤ (16 * (m : ENNReal) * (L : ENNReal)^m) * (d' : ENNReal) := by
        have h6 : (d : ENNReal) < (16 * (m : ENNReal) * (bins : ENNReal)^m) * (T k : ENNReal) := by
          exact_mod_cast h_d_max3
        have h7 : (T k : ENNReal) ≤ (d' : ENNReal) := by exact_mod_cast h_d'_min
        have h8 : (16 * (m : ENNReal) * (L : ENNReal)^m) = (16 * (m : ENNReal) * (bins : ENNReal)^m) := by
          rw [hL_eq']
        rw [h8]
        have h9 : (16 * (m : ENNReal) * (bins : ENNReal)^m) * (T k : ENNReal) ≤
            (16 * (m : ENNReal) * (bins : ENNReal)^m) * (d' : ENNReal) := by gcongr
        exact le_of_lt (lt_of_lt_of_le h6 h9)
      exact h_ineq

  have hL_unfold_final : (L : ENNReal) = (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) := by
    simp [L, n] <;> rfl
  have h_uniformity' : ∀ (k : Fin m) (j j' : J k),
      0 < (S'.filter (fun i => parent k i = j)).card →
      0 < (S'.filter (fun i => parent k i = j')).card →
      ((S'.filter (fun i => parent k i = j)).card : ENNReal) ≤
        (16 * (m : ENNReal) * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^m) *
        ((S'.filter (fun i => parent k i = j')).card : ENNReal) := by
    intro k j j' hj_pos hj'_pos
    have h := h_uniformity k j j' hj_pos hj'_pos
    rw [hL_unfold_final] at *
    exact h
  have h6' : total ≤ (8 : ENNReal) * (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal) ^ (m + 1) * (∑ i ∈ S', w i) := by
    rw [hL_unfold_final] at h6
    exact h6
  have h_support :
      ∀ i ∈ S', 0 < w i := by
    intro i hi
    exact
      lt_of_lt_of_le hc_pos
        (h_wmin i (hS0_sub_I'' (hS'_sub hi)))
  have h_support_floor :
      0 < m →
        ∀ i ∈ S',
          (∑ source : I, w source) /
              (2 * Fintype.card I : ENNReal) ≤
            w i := by
    intro _ i hi
    exact
      h_weight_floor i
        (hS0_sub_I'' (hS'_sub hi))
  exact
    ⟨S', h_uniformity', h6', h_support,
      h_support_floor, fun _ =>
        ⟨c, hc_pos, fun i hi =>
          ⟨h_wmin i (hS0_sub_I'' (hS'_sub hi)),
            h_wmax i (hS0_sub_I'' (hS'_sub hi))⟩⟩⟩

lemma simultaneous_degree_regularization_with_support
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (J : Fin m → Type _)
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (w : I → ENNReal) :
    ∃ (S : Finset I),
      (∀ k, ∀ (j j' : J k),
        0 < (S.filter (fun i => parent k i = j)).card →
        0 < (S.filter (fun i => parent k i = j')).card →
        ((S.filter (fun i => parent k i = j)).card : ENNReal) ≤
          (16 * (m : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^m) *
          ((S.filter (fun i => parent k i = j')).card : ENNReal)) ∧
      (∑ i : I, w i) ≤
        (8 : ENNReal) *
          (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^(m + 1) *
          (∑ i ∈ S, w i) ∧
      (∀ i ∈ S, 0 < w i) ∧
      (0 < m →
        ∀ i ∈ S,
          (∑ source : I, w source) /
              (2 * Fintype.card I : ENNReal) ≤
            w i) := by
  rcases
      simultaneous_degree_regularization_with_support_and_weight_band
        m J parent w
    with ⟨S, h_uniform, h_retained, h_support, h_floor, _⟩
  exact ⟨S, h_uniform, h_retained, h_support, h_floor⟩

lemma simultaneous_degree_regularization
    {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (J : Fin m → Type _)
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (parent : ∀ k, I → J k) (w : I → ENNReal) :
    ∃ (S : Finset I),
      (∀ k, ∀ (j j' : J k),
        0 < (S.filter (fun i => parent k i = j)).card →
        0 < (S.filter (fun i => parent k i = j')).card →
        ((S.filter (fun i => parent k i = j)).card : ENNReal) ≤
          (16 * (m : ENNReal) *
            (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^m) *
          ((S.filter (fun i => parent k i = j')).card : ENNReal)) ∧
      (∑ i : I, w i) ≤
        (8 : ENNReal) *
          (Nat.log 2 (2 * Fintype.card I) + 1 : ENNReal)^(m + 1) *
          (∑ i ∈ S, w i) := by
  rcases
      simultaneous_degree_regularization_with_support
        m J parent w
    with ⟨S, h_uniform, h_retained, _, _⟩
  exact ⟨S, h_uniform, h_retained⟩

end Kakeya.Assouad
