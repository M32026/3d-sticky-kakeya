import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaAssemblyHelpers

/-!
# Separated points extraction from a tube carrier with volume lower bound

Given a δ-tube carrier subset `S` inside a ball of radius `tau` with volume
lower bound `V`, extract a finite set `P` of points that are `d`-separated,
lie in `S`, cover `S` by `d`-balls, and satisfy a cardinality lower bound
derived from the volume bound.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya MeasureTheory Metric Set Finset

/-- Extract a maximal `2*ε`-separated subset from a finite set `N`. -/
lemma exists_maximal_separated_subset
    {α : Type*} [DecidableEq α] [PseudoMetricSpace α]
    (N : Finset α) (ε : ℝ) (_ : 0 ≤ ε) :
    ∃ (P : Finset α),
      P ⊆ N ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → dist x y ≥ 2 * ε) ∧
      (∀ n ∈ N, n ∈ P ∨ ∃ p ∈ P, dist n p < 2 * ε) := by
  classical
  let valid : Finset α → Prop := fun s =>
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → dist x y ≥ 2 * ε
  let valid_sets : Finset (Finset α) := N.powerset.filter valid
  have h_nonempty : valid_sets.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [valid_sets, mem_filter, Finset.mem_powerset]
    <;> simp [valid]
  have h_max : ∃ P ∈ valid_sets, ∀ Q ∈ valid_sets, Q.card ≤ P.card :=
    Finset.exists_max_image valid_sets (fun s : Finset α => s.card) h_nonempty
  rcases h_max with ⟨P, hP_in, hP_max⟩
  have hP_sub : P ⊆ N := by
    have h : P ∈ N.powerset := (mem_filter.mp hP_in).1
    exact (Finset.mem_powerset.mp h)
  have hP_valid : valid P := (mem_filter.mp hP_in).2
  refine ⟨P, hP_sub, hP_valid, ?_⟩
  intro n hn
  by_cases h_n_in : n ∈ P
  · exact Or.inl h_n_in
  · by_cases h_sep : ∀ p ∈ P, dist n p ≥ 2 * ε
    · let Q := insert n P
      have hQ_sub : Q ⊆ N := by
        intro x hx
        have h : x = n ∨ x ∈ P := by simpa [Q] using hx
        rcases h with (rfl | hx) <;> tauto
      have hQ_valid : valid Q := by
        intro x hx y hy hne
        have hx' : x = n ∨ x ∈ P := by simpa [Q] using hx
        have hy' : y = n ∨ y ∈ P := by simpa [Q] using hy
        rcases hx' with (h_x_eq_n | hxP)
        · rcases hy' with (h_y_eq_n | hyP)
          · exfalso; exact hne (by rw [h_x_eq_n, h_y_eq_n])
          · rw [h_x_eq_n]; exact h_sep y hyP
        · rcases hy' with (h_y_eq_n | hyP)
          · rw [h_y_eq_n]
            have h : dist n x ≥ 2 * ε := h_sep x hxP
            exact dist_comm n x ▸ h
          · exact hP_valid x hxP y hyP hne
      have hQ_in : Q ∈ valid_sets := by
        simp only [valid_sets, mem_filter]
        exact ⟨Finset.mem_powerset.mpr hQ_sub, hQ_valid⟩
      have hQ_card : Q.card = P.card + 1 := by
        rw [card_insert_of_notMem h_n_in]
      have h_contra : Q.card ≤ P.card := hP_max Q hQ_in
      rw [hQ_card] at h_contra <;> omega
    · have h_exists : ∃ p ∈ P, dist n p < 2 * ε := by
        simpa [not_forall] using h_sep
      exact Or.inr h_exists

/-- Extract a `(2*d/3)`-separated, `d`-covering finite subset from a bounded set `S`. -/
lemma exists_separated_cover
    (S : Set Point3) (_q : Point3) (tau d : ℝ)
    (hS_bounded : Bornology.IsBounded S) (hd : 0 < d) :
    ∃ (P : Finset Point3),
      (P : Set Point3) ⊆ S ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → dist x y ≥ 2 * d / 3) ∧
      (S ⊆ ⋃ p ∈ P, closedBall p d) := by
  let ε : ℝ := d / 3
  have hε_pos : 0 < ε := by positivity
  have hε_nonneg : 0 ≤ ε := by positivity
  let εnn : NNReal := ⟨ε, hε_nonneg⟩
  have hεnn_ne_zero : εnn ≠ 0 := by
    intro h
    have h9 : (εnn : ℝ) = 0 := by exact_mod_cast h
    have h10 : (εnn : ℝ) = ε := by rfl
    rw [h10] at h9
    exact (ne_of_gt hε_pos) h9
  have h_closure_bounded : Bornology.IsBounded (closure S) :=
    hS_bounded.closure
  have h_closure_closed : IsClosed (closure S) := isClosed_closure
  have h_closure_compact : IsCompact (closure S) :=
    Metric.isCompact_of_isClosed_isBounded h_closure_closed h_closure_bounded
  have h_cover : ∃ (N : Set Point3), N ⊆ S ∧ N.Finite ∧
      Metric.IsCover εnn S N :=
    Metric.exists_finite_isCover_of_isCompact_closure hεnn_ne_zero h_closure_compact
  rcases h_cover with ⟨N, hN_sub, hN_finite, hN_cover⟩
  let N' : Finset Point3 := hN_finite.toFinset
  have hN'_eq : (N' : Set Point3) = N := hN_finite.coe_toFinset
  rcases exists_maximal_separated_subset N' ε hε_nonneg with
    ⟨P, hP_sub, hP_sep, hP_max_cover⟩
  have hP_sub_S : (P : Set Point3) ⊆ S := by
    calc (P : Set Point3) ⊆ (N' : Set Point3) := hP_sub
      _ = N := hN'_eq
      _ ⊆ S := hN_sub
  have hP_cover_N : ∀ n ∈ N', ∃ p ∈ P, dist n p ≤ 2 * ε := by
    intro n hn
    rcases hP_max_cover n hn with (h_n_in_P | ⟨p, hp_in_P, hdist⟩)
    · exact ⟨n, h_n_in_P, by simp [dist_self] <;> positivity⟩
    · exact ⟨p, hp_in_P, by linarith⟩
  have hP_cover_S : S ⊆ ⋃ p ∈ P, closedBall p d := by
    intro x hx
    have h1 : ∃ n ∈ N', dist x n ≤ ε := by
      have h3 : x ∈ S := hx
      have h4 := hN_cover h3
      rcases h4 with ⟨n, hn_in_N, hdist⟩
      have hn_in_N' : n ∈ N' := by
        have h5 : n ∈ (N' : Set Point3) := by
          rw [hN'_eq] <;> exact hn_in_N
        exact h5
      have h6 : dist x n ≤ ε := by
        have h7 : (nndist x n : ℝ) ≤ (εnn : ℝ) := by exact_mod_cast hdist
        have h8 : (nndist x n : ℝ) = dist x n := by simp
        have h9 : (εnn : ℝ) = ε := by rfl
        rw [h8, h9] at h7
        exact h7
      exact ⟨n, hn_in_N', h6⟩
    rcases h1 with ⟨n, hn_in_N', hdist_xn⟩
    rcases hP_cover_N n hn_in_N' with ⟨p, hp_in_P, hdist_np⟩
    have hdist_xp : dist x p ≤ dist x n + dist n p := dist_triangle x n p
    have h5 : dist x p ≤ ε + 2 * ε := by linarith
    have h6 : ε + 2 * ε = d := by ring
    rw [h6] at h5
    have h_goal : x ∈ ⋃ p ∈ P, closedBall p d := by
      simpa using ⟨p, hp_in_P, h5⟩
    exact h_goal
  have h_sep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → dist x y ≥ 2 * d / 3 := by
    intro x hx y hy hne
    have h7 : dist x y ≥ 2 * ε := hP_sep x hx y hy hne
    have h8 : 2 * ε = 2 * d / 3 := by ring
    rw [h8] at h7
    exact h7
  exact ⟨P, hP_sub_S, h_sep, hP_cover_S⟩

/-- Cardinality lower bound for a separated cover of a tube carrier subset. -/
lemma separated_cover_card_lower_bound
    {δ d : ℝ} (hδ : 0 < δ) (hd : 0 < d)
    (T : DeltaTube δ) (S : Set Point3) (hS_sub_T : S ⊆ T.carrier)
    (P : Finset Point3) (hP_cover : S ⊆ ⋃ p ∈ P, closedBall p d)
    {V : ENNReal} (hV : volume S ≥ V) :
    (P.card : ENNReal) ≥ V / ENNReal.ofReal (8 * δ^2 * d) := by
  have h1 : volume S ≤ ∑ p ∈ P, volume (S ∩ closedBall p d) := by
    let f : Point3 → Set Point3 := fun p => S ∩ closedBall p d
    have h_union : S ⊆ ⋃ p ∈ P, f p := by
      intro x hx
      have h2 : x ∈ S := hx
      have h3 : x ∈ ⋃ p ∈ P, closedBall p d := hP_cover h2
      have h4 : ∃ (p : Point3), p ∈ P ∧ x ∈ closedBall p d := by
        simpa [Finset.mem_sup] using h3
      rcases h4 with ⟨p, hp, h5⟩
      have h6 : x ∈ f p := ⟨h2, h5⟩
      simpa [Finset.mem_sup] using ⟨p, hp, h6⟩
    calc volume S
      ≤ volume (⋃ p ∈ P, f p) := MeasureTheory.measure_mono h_union
    _ ≤ ∑ p ∈ P, volume (f p) := MeasureTheory.measure_biUnion_finset_le P f
  have h2 : ∀ p ∈ P, volume (S ∩ closedBall p d) ≤
      ENNReal.ofReal (8 * δ^2 * d) := by
    intro p _
    have h3 : S ∩ closedBall p d ⊆ T.carrier ∩ closedBall p d :=
      Set.inter_subset_inter_left _ hS_sub_T
    have h4 := tube_ball_intersection_volume_simple hδ (by linarith) T p
    exact le_trans (MeasureTheory.measure_mono h3) h4
  have h3 : ∑ p ∈ P, volume (S ∩ closedBall p d) ≤
      (P.card : ENNReal) * ENNReal.ofReal (8 * δ^2 * d) := by
    calc ∑ p ∈ P, volume (S ∩ closedBall p d)
      ≤ ∑ p ∈ P, ENNReal.ofReal (8 * δ^2 * d) :=
        Finset.sum_le_sum fun i _ => h2 i ‹_›
    _ = (P.card : ENNReal) * ENNReal.ofReal (8 * δ^2 * d) := by
        simp [Finset.sum_const] <;> ring
  have h4 : volume S ≤ (P.card : ENNReal) * ENNReal.ofReal (8 * δ^2 * d) :=
    le_trans h1 h3
  have h5 : V ≤ ENNReal.ofReal (8 * δ^2 * d) * (P.card : ENNReal) := by
    rw [mul_comm] at h4
    exact le_trans hV h4
  exact ENNReal.div_le_of_le_mul' h5

end Kakeya.Assouad
