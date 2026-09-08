import MyLeanRepo.Kakeya.Streamlined.MultiplicityPigeonhole
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers

/-!
# Helper lemmas for factoring multiplicity regularization

1. Weighted dyadic pigeonhole
2. Fiber shading and per-fiber pigeonholing
3. Subfamily/refinement/factoring restriction utilities
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-! ### Weighted dyadic pigeonhole -/

/--
Weighted dyadic pigeonholing: given a measurable natural-valued function `f`
bounded by `N` and a measurable weight `w` supported on `{x | f x > 0}`,
there exists a dyadic bin whose weighted mass, times the number of bins,
is at least the total weighted mass.
-/
lemma weighted_dyadic_pigeonhole {N : ℕ} (hN : 0 < N)
    (f : Point3 → ℕ) (hf : Measurable f) (h_bound : ∀ x, f x ≤ N)
    (w : Point3 → ENNReal) (hw : Measurable w)
    (h_support : ∀ x, w x ≠ 0 → 0 < f x) :
    ∃ (k : ℕ) (S : Set Point3) (hS : MeasurableSet S),
      (∀ x ∈ S, 2 ^ k ≤ f x ∧ f x < 2 ^ (k + 1)) ∧
      (∫⁻ x in S, w x) * (Nat.log 2 N + 1 : ENNReal) ≥ ∫⁻ x, w x := by
  classical
  let K := Nat.log 2 N + 1
  let bins : Finset ℕ := Finset.range K
  let S (k : ℕ) : Set Point3 :=
    {x | 2 ^ k ≤ f x ∧ f x < 2 ^ (k + 1)}
  have hS_meas : ∀ k, MeasurableSet (S k) := by
    intro k
    have h1 : MeasurableSet {x : Point3 | 2 ^ k ≤ f x} := hf measurableSet_Ici
    have h2 : MeasurableSet {x : Point3 | f x < 2 ^ (k + 1)} := hf measurableSet_Iio
    exact h1.inter h2
  have h_disj : ∀ k1 ∈ bins, ∀ k2 ∈ bins, k1 ≠ k2 → Disjoint (S k1) (S k2) := by
    intro k1 _ k2 _ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : 2 ^ k1 ≤ f x := hx1.1
    have h2 : f x < 2 ^ (k1 + 1) := hx1.2
    have h3 : 2 ^ k2 ≤ f x := hx2.1
    have h4 : f x < 2 ^ (k2 + 1) := hx2.2
    by_cases h : k1 < k2
    · have h5 : 2 ^ (k1 + 1) ≤ 2 ^ k2 := by gcongr <;> omega
      linarith
    · have h6 : k2 < k1 := by omega
      have h7 : 2 ^ (k2 + 1) ≤ 2 ^ k1 := by gcongr <;> omega
      linarith
  have h_pointwise : ∀ (x : Point3), w x = ∑ k ∈ bins, Set.indicator (S k) w x := by
    intro x
    by_cases hwx : w x = 0
    · have h_all_zero : ∀ k ∈ bins, Set.indicator (S k) w x = 0 := by
        intro k _
        simp [hwx]
      have h_sum : ∑ k ∈ bins, Set.indicator (S k) w x = 0 := by
        rw [Finset.sum_congr rfl h_all_zero] <;> simp
      rw [h_sum, hwx]
    · have h_pos : 0 < f x := h_support x hwx
      have h_le : f x ≤ N := h_bound x
      let k0 := Nat.log 2 (f x)
      have hk1 : 2 ^ k0 ≤ f x := Nat.pow_log_le_self 2 (by omega)
      have hk2 : f x < 2 ^ (k0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h_log_mono : k0 ≤ Nat.log 2 N := Nat.log_mono_right h_le
      have hk3 : k0 < K := by simp only [K] <;> omega
      have hk0_in : k0 ∈ bins := Finset.mem_range.mpr hk3
      have hx0 : x ∈ S k0 := ⟨hk1, hk2⟩
      have h_unique : ∀ k ∈ bins, x ∈ S k → k = k0 := by
        intro k hk_in hxk
        by_contra hne
        have h_disj' : Disjoint (S k) (S k0) := h_disj k hk_in k0 hk0_in hne
        exact Set.disjoint_left.mp h_disj' hxk hx0
      have h_sum : ∑ k ∈ bins, Set.indicator (S k) w x = w x := by
        rw [Finset.sum_eq_single_of_mem k0 hk0_in]
        · simp [hx0]
        · intro j _ hjne
          have h_not : x ∉ S j := by
            intro h
            exact hjne (h_unique j ‹_› h)
          simp [h_not]
      exact h_sum.symm
  let m (k : ℕ) : ENNReal := ∫⁻ x in S k, w x
  have h_mass_eq : (∫⁻ x, w x) = ∑ k ∈ bins, m k := by
    have h2 : ∫⁻ x, w x = ∫⁻ x, ∑ k ∈ bins, Set.indicator (S k) w x := by
      congr with x
      exact h_pointwise x
    have h3 : ∫⁻ x, ∑ k ∈ bins, Set.indicator (S k) w x =
        ∑ k ∈ bins, ∫⁻ x, Set.indicator (S k) w x := by
      apply MeasureTheory.lintegral_finsetSum
      intro k _
      exact hw.indicator (hS_meas k)
    have h4 : ∑ k ∈ bins, ∫⁻ x, Set.indicator (S k) w x = ∑ k ∈ bins, m k := by
      apply Finset.sum_congr rfl
      intro k _
      exact MeasureTheory.lintegral_indicator (hS_meas k) w
    calc (∫⁻ x, w x)
      = ∫⁻ x, ∑ k ∈ bins, Set.indicator (S k) w x := h2
    _ = ∑ k ∈ bins, ∫⁻ x, Set.indicator (S k) w x := h3
    _ = ∑ k ∈ bins, m k := h4
  have h_exists : ∃ k ∈ bins, ∀ j ∈ bins, m j ≤ m k := by
    exact Finset.exists_max_image bins m
      (Finset.nonempty_iff_ne_empty.mpr (by simp [bins, K]))
  rcases h_exists with ⟨k, hk, hmax⟩
  have h_sum : ∑ j ∈ bins, m j ≤ ∑ j ∈ bins, m k := by
    apply Finset.sum_le_sum
    intro j hj
    exact hmax j hj
  have h_count : ∑ j ∈ bins, m k = (bins.card : ENNReal) * m k := by
    rw [Finset.sum_const, mul_comm] <;> ring
  have h_final : (bins.card : ENNReal) * m k ≥ ∫⁻ x, w x := by
    calc (∫⁻ x, w x)
      = ∑ j ∈ bins, m j := h_mass_eq
    _ ≤ ∑ j ∈ bins, m k := h_sum
    _ = (bins.card : ENNReal) * m k := h_count
  have h_K : (bins.card : ENNReal) = (K : ENNReal) := by
    simp [bins, Finset.card_range]
  have h_final2 : (K : ENNReal) * m k ≥ ∫⁻ x, w x := by
    rw [← h_K]
    exact h_final
  have h_comm : m k * (K : ENNReal) = (K : ENNReal) * m k := by ring
  have h_final3 : m k * (K : ENNReal) ≥ ∫⁻ x, w x := by
    rw [h_comm]
    exact h_final2
  have h_Kdef : (K : ENNReal) = (Nat.log 2 N + 1 : ENNReal) := by
    simp [K]
  rw [h_Kdef] at h_final3
  exact ⟨k, S k, hS_meas k, fun x hx => hx, h_final3⟩

/-! ### Fiber shading -/

/-- Restrict a shading to the fiber over a single coarse parent `j`. -/
def Factoring.fiberShading {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (j : Fin coarse.card) : Shading fine :=
  { carrier := fun i => if P.parent i = j then Y.carrier i else ∅
    measurable_carrier := by
      intro i
      by_cases h : P.parent i = j
      · rw [if_pos h]
        exact Y.measurable_carrier i
      · rw [if_neg h]
        exact MeasurableSet.empty
    subset_body := by
      intro i
      by_cases h : P.parent i = j
      · rw [if_pos h]
        exact Y.subset_body i
      · rw [if_neg h]
        exact Set.empty_subset _ }

/-- The pointwise multiplicity of the fiber shading equals the fiber point multiplicity. -/
lemma Factoring.fiberShading_pointMultiplicity {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (j : Fin coarse.card) (x : Point3) :
    (P.fiberShading Y j).pointMultiplicity x = P.fiberPointMultiplicity Y j x := by
  classical
  have h1 : (Finset.univ.filter fun i : Fin fine.card =>
        x ∈ (P.fiberShading Y j).carrier i) =
      (P.fiberIndices j).filter fun i => x ∈ Y.carrier i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h2 : x ∈ (P.fiberShading Y j).carrier i ↔
        P.parent i = j ∧ x ∈ Y.carrier i := by
      simp [Factoring.fiberShading]
    rw [h2]
    simp [Factoring.fiberIndices]
  have h_main : (Finset.univ.filter fun i : Fin fine.card =>
        x ∈ (P.fiberShading Y j).carrier i).card =
      ((P.fiberIndices j).filter fun i => x ∈ Y.carrier i).card := by
    rw [h1]
  simpa [Shading.pointMultiplicity, Factoring.fiberPointMultiplicity] using h_main

/-- The mass of the fiber shading equals the fiber shaded mass. -/
lemma Factoring.fiberShading_mass {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (j : Fin coarse.card) :
    (P.fiberShading Y j).mass = P.fiberShadedMass Y j := by
  classical
  have h1 : ∑ i : Fin fine.card, volume ((P.fiberShading Y j).carrier i) =
      ∑ i ∈ P.fiberIndices j, volume (Y.carrier i) := by
    have h2 : ∀ i : Fin fine.card, volume ((P.fiberShading Y j).carrier i) =
        if P.parent i = j then volume (Y.carrier i) else 0 := by
      intro i
      by_cases h : P.parent i = j
      · have h4 : (P.fiberShading Y j).carrier i = Y.carrier i := by
          simp [Factoring.fiberShading, h]
        rw [h4, if_pos h]
      · have h4 : (P.fiberShading Y j).carrier i = ∅ := by
          simp [Factoring.fiberShading, h]
        rw [h4, if_neg h] <;> simp
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    rw [Finset.sum_ite] <;> simp [Factoring.fiberIndices]
  exact h1

/--
Apply the dyadic multiplicity pigeonhole to each fiber shading.
-/
lemma Factoring.fiber_multiplicity_pigeonhole {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (h_card : 0 < fine.card) (j : Fin coarse.card) :
    ∃ (k_j : ℕ) (Ω_j : Set Point3) (hΩ_j : MeasurableSet Ω_j),
      k_j ≤ Nat.log 2 fine.card ∧
      (∀ x ∈ Ω_j, 2 ^ k_j ≤ P.fiberPointMultiplicity Y j x ∧
                    P.fiberPointMultiplicity Y j x < 2 ^ (k_j + 1)) ∧
      (∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j)) *
        (Nat.log 2 fine.card + 1 : ENNReal) ≥ P.fiberShadedMass Y j := by
  let Y_j := P.fiberShading Y j
  rcases multiplicity_pigeonhole Y_j h_card with
    ⟨k_j, Ω_j, hΩ_j, h_mult, h_mass⟩
  have h_max_mult : ∀ x : Point3, Y_j.pointMultiplicity x ≤ fine.card := by
    classical
    intro x
    have h : (Finset.univ.filter fun i : Fin fine.card => x ∈ Y_j.carrier i) ⊆
        (Finset.univ : Finset (Fin fine.card)) := Finset.filter_subset _ _
    have h' : (Finset.univ.filter fun i : Fin fine.card => x ∈ Y_j.carrier i).card ≤
        Finset.univ.card := Finset.card_le_card h
    have h_univ_card : (Finset.univ : Finset (Fin fine.card)).card = fine.card :=
      Finset.card_fin fine.card
    rw [h_univ_card] at h'
    exact h'
  by_cases h_nonempty : Ω_j.Nonempty
  · rcases h_nonempty with ⟨x, hx⟩
    have h1 : 2 ^ k_j ≤ Y_j.pointMultiplicity x := (h_mult x hx).1
    have h2 : Y_j.pointMultiplicity x ≤ fine.card := h_max_mult x
    have h3 : k_j ≤ Nat.log 2 fine.card := by
      have h4 : 2 ^ k_j ≤ fine.card := by exact_mod_cast h1.trans h2
      exact Nat.le_log_of_pow_le (by norm_num) h4
    refine ⟨k_j, Ω_j, hΩ_j, h3, ?_, ?_⟩
    · intro x hx
      have h := h_mult x hx
      have h_eq : Y_j.pointMultiplicity x = P.fiberPointMultiplicity Y j x :=
        P.fiberShading_pointMultiplicity Y j x
      rw [h_eq] at h
      exact h
    · have h_restrict : (Y_j.restrict Ω_j hΩ_j).mass =
          ∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j) := by
        classical
        have h1 : ∑ i : Fin fine.card, volume ((Y_j.carrier i) ∩ Ω_j) =
            ∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j) := by
          have h2 : ∀ i : Fin fine.card, volume ((Y_j.carrier i) ∩ Ω_j) =
              if P.parent i = j then volume (Y.carrier i ∩ Ω_j) else 0 := by
            intro i
            by_cases h : P.parent i = j
            · have h4 : Y_j.carrier i = Y.carrier i := by
                dsimp only [Y_j, Factoring.fiberShading]
                rw [if_pos h]
              rw [h4, if_pos h]
            · have h4 : Y_j.carrier i = ∅ := by
                dsimp only [Y_j, Factoring.fiberShading]
                rw [if_neg h]
              rw [h4, if_neg h] <;> simp
          rw [Finset.sum_congr rfl (fun i _ => h2 i)]
          rw [Finset.sum_ite] <;> simp [Factoring.fiberIndices]
        exact h1
      have h_fmass : Y_j.mass = P.fiberShadedMass Y j := P.fiberShading_mass Y j
      rw [h_restrict, h_fmass] at h_mass
      exact h_mass
  · have hΩ_empty : Ω_j = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_nonempty
    refine ⟨0, Ω_j, hΩ_j, by omega, ?_, ?_⟩
    · rw [hΩ_empty]
      simp
    · have h_restrict : (Y_j.restrict Ω_j hΩ_j).mass =
          ∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j) := by
        classical
        have h1 : ∑ i : Fin fine.card, volume ((Y_j.carrier i) ∩ Ω_j) =
            ∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j) := by
          have h2 : ∀ i : Fin fine.card, volume ((Y_j.carrier i) ∩ Ω_j) =
              if P.parent i = j then volume (Y.carrier i ∩ Ω_j) else 0 := by
            intro i
            by_cases h : P.parent i = j
            · have h4 : Y_j.carrier i = Y.carrier i := by
                dsimp only [Y_j, Factoring.fiberShading]
                rw [if_pos h]
              rw [h4, if_pos h]
            · have h4 : Y_j.carrier i = ∅ := by
                dsimp only [Y_j, Factoring.fiberShading]
                rw [if_neg h]
              rw [h4, if_neg h] <;> simp
          rw [Finset.sum_congr rfl (fun i _ => h2 i)]
          rw [Finset.sum_ite] <;> simp [Factoring.fiberIndices]
        exact h1
      have h_fmass : Y_j.mass = P.fiberShadedMass Y j := P.fiberShading_mass Y j
      rw [h_restrict, h_fmass] at h_mass
      exact h_mass

/-! ### Dominant level selection across fibers -/

/--
Given a dyadic level `k j` and a mass `m j` for each coarse parent, where
each `k j < K`, there exists a level `kfiber` such that the total mass of
fibers at that level, times `K`, is at least the grand total mass.
-/
lemma dominant_level_selection {fine coarse : BodyFamily}
    (k : Fin coarse.card → ℕ) (m : Fin coarse.card → ENNReal)
    (hk : ∀ j, k j < Nat.log 2 fine.card + 1) :
    ∃ kfiber : ℕ,
      (Nat.log 2 fine.card + 1 : ENNReal) *
        (∑ j ∈ Finset.univ.filter (fun j => k j = kfiber), m j) ≥
      ∑ j : Fin coarse.card, m j := by
  let K := Nat.log 2 fine.card + 1
  have h_main := pigeonhole_bins (s := Finset.univ) (a := m) (bin := k)
  rcases h_main with ⟨kfiber, h_ineq⟩
  have h_image_subset : Finset.image k Finset.univ ⊆ Finset.range K := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    exact Finset.mem_range.mpr (hk j)
  have h_image_card : (Finset.image k Finset.univ).card ≤ K := by
    have h : (Finset.image k Finset.univ).card ≤ (Finset.range K).card :=
      Finset.card_le_card h_image_subset
    have h2 : (Finset.range K).card = K := Finset.card_range K
    rw [h2] at h
    exact h
  have h3 : ((Finset.image k Finset.univ).card : ENNReal) ≤ (K : ENNReal) := by
    exact_mod_cast h_image_card
  have h4 : (K : ENNReal) *
      (∑ j ∈ Finset.univ.filter (fun j => k j = kfiber), m j) ≥
      ((Finset.image k Finset.univ).card : ENNReal) *
        (∑ j ∈ Finset.univ.filter (fun j => k j = kfiber), m j) := by
    gcongr
  have h5 : ((∑ j ∈ Finset.univ.filter (fun j => k j = kfiber), m j) *
        (Finset.image k Finset.univ).card : ENNReal) =
      ((Finset.image k Finset.univ).card : ENNReal) *
        (∑ j ∈ Finset.univ.filter (fun j => k j = kfiber), m j) := by
    ring
  rw [h5] at h_ineq
  let S := ∑ j ∈ Finset.univ.filter (fun j => k j = kfiber), m j
  have hK : (K : ENNReal) = (Nat.log 2 fine.card + 1 : ENNReal) := by simp [K]
  have h6 : ((Finset.image k Finset.univ).card : ENNReal) * S ≤
      (Nat.log 2 fine.card + 1 : ENNReal) * S := by
    rw [← hK]
    exact h4
  have h7 : (∑ j : Fin coarse.card, m j) ≤
      ((Finset.image k Finset.univ).card : ENNReal) * S := h_ineq
  refine ⟨kfiber, ?_⟩
  exact le_trans h7 h6

/-! ### Refinement and factoring restriction utilities -/

namespace Refinement

/-- Construct a refinement by restricting each member's shading to a measurable set `Ω`. -/
def mkRestricted {F : BodyFamily} {Y : Shading F}
    (S : Subfamily F) (Ω : Set Point3) (hΩ : MeasurableSet Ω) :
    Refinement Y :=
  { subfamily := S
    shading :=
      { carrier := fun i => Y.carrier (S.embedding i) ∩ Ω
        measurable_carrier := fun i =>
          (Y.measurable_carrier (S.embedding i)).inter hΩ
        subset_body := fun i =>
          Set.inter_subset_left.trans <|
            (Y.subset_body (S.embedding i)).trans_eq (S.carrier_eq i).symm }
    shading_subset := fun _ => Set.inter_subset_left }

end Refinement

namespace Factoring

/--
Given a factoring `P` and compatible fine and coarse subfamilies, construct
a factoring on the subfamilies.
-/
def restrict {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (S_fine : Subfamily fine) (S_coarse : Subfamily coarse)
    (h_map : ∀ i : Fin S_fine.family.card,
      P.parent (S_fine.embedding i) ∈ Set.range S_coarse.embedding)
    (h_surj : ∀ j : Fin S_coarse.family.card,
      ∃ i : Fin S_fine.family.card,
        P.parent (S_fine.embedding i) = S_coarse.embedding j) :
    Factoring S_fine.family S_coarse.family :=
  let parent' : Fin S_fine.family.card → Fin S_coarse.family.card :=
    fun i => Classical.choose (h_map i)
  have h_compat : ∀ i,
      S_coarse.embedding (parent' i) = P.parent (S_fine.embedding i) := by
    intro i
    exact Classical.choose_spec (h_map i)
  { parent := parent'
    parent_surjective := by
      intro j
      rcases h_surj j with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have h_inj : S_coarse.embedding (parent' i) = S_coarse.embedding j := by
        rw [h_compat i, hi]
      exact S_coarse.embedding.inj' h_inj
    contained := by
      intro i
      have h1 : (S_fine.family.body i).carrier =
          (fine.body (S_fine.embedding i)).carrier := S_fine.carrier_eq i
      have h2 : (fine.body (S_fine.embedding i)).carrier ⊆
          (coarse.body (P.parent (S_fine.embedding i))).carrier :=
        P.contained (S_fine.embedding i)
      have h3 : (S_coarse.family.body (parent' i)).carrier =
          (coarse.body (S_coarse.embedding (parent' i))).carrier :=
        S_coarse.carrier_eq (parent' i)
      rw [h1, h3]
      rw [h_compat i]
      exact h2 }

/-- The restricted factoring is compatible with the original. -/
lemma restrict_compatible {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (S_fine : Subfamily fine) (S_coarse : Subfamily coarse)
    (h_map h_surj) :
    ∀ i : Fin S_fine.family.card,
      S_coarse.embedding ((P.restrict S_fine S_coarse h_map h_surj).parent i) =
        P.parent (S_fine.embedding i) := by
  intro i
  dsimp only [restrict]
  exact Classical.choose_spec (h_map i)

end Factoring

end Kakeya.Streamlined
