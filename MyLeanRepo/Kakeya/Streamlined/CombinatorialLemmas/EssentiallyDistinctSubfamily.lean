import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Essentially-distinct subfamily extraction

Given a tube family with a bound on pairwise intersection volumes, extract a
large pairwise essentially-distinct subfamily using a maximal-subfamily
charging argument.

## Main result

`exists_essentially_distinct_subfamily`: if for every tube T_j the total
intersection volume with all tubes is ≤ C · |T_j|, and all tubes have the
same positive finite volume V, then there exists an essentially-distinct
subfamily of size ≥ |G| / (2C + 1).
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- EssentiallyDistinct is symmetric. -/
lemma essentiallyDistinct_symm {δ : ℝ} {T U : Kakeya.DeltaTube δ} :
    T.EssentiallyDistinct U ↔ U.EssentiallyDistinct T := by
  simp [Kakeya.DeltaTube.EssentiallyDistinct, Set.inter_comm, max_comm]

/-- If P holds on I and i is essentially distinct from every j ∈ I,
then P holds on insert i I. -/
private lemma insert_preserves_P {δ : ℝ} {G : TubeFamily δ}
    {I : Finset (Fin G.card)} {i : Fin G.card}
    (hPI : ∀ k ∈ I, ∀ l ∈ I, k ≠ l → (G.tube k).EssentiallyDistinct (G.tube l))
    (hi : i ∉ I)
    (h : ∀ j ∈ I, (G.tube i).EssentiallyDistinct (G.tube j)) :
    ∀ k ∈ insert i I, ∀ l ∈ insert i I, k ≠ l →
      (G.tube k).EssentiallyDistinct (G.tube l) := by
  intro k hk l hl hne
  by_cases hki : k = i
  · -- k = i
    have h_lI : l ∈ I := by
      have h_nei : l ≠ i := by
        intro h_eq; apply hne; rw [hki, h_eq]
      have : l ∈ insert i I := hl
      simp only [Finset.mem_insert] at this
      tauto
    have h_goal : (G.tube k).EssentiallyDistinct (G.tube l) := by
      rw [hki]; exact h l h_lI
    exact h_goal
  · -- k ≠ i
    have hkI : k ∈ I := by
      simp only [Finset.mem_insert] at hk <;> tauto
    by_cases hli : l = i
    · -- l = i
      have h_goal : (G.tube k).EssentiallyDistinct (G.tube l) := by
        rw [hli]
        have h' := h k hkI
        exact essentiallyDistinct_symm.mp h'
      exact h_goal
    · -- l ≠ i
      have hlI : l ∈ I := by
        simp only [Finset.mem_insert] at hl <;> tauto
      exact hPI k hkI l hlI hne

/-- **Maximal essentially-distinct subfamily.**

Given any tube family `G`, there exists a finset `I` of indices such that:
1. The tubes indexed by `I` are pairwise essentially distinct.
2. Every index not in `I` conflicts with (is not essentially distinct from)
   at least one index in `I`.

This is proved by taking a maximum-cardinality pairwise essentially-distinct
subfamily; if an outside index could be added while preserving the property,
the resulting subfamily would have larger cardinality, a contradiction. -/
theorem exists_maximal_essentially_distinct_subfamily
    {δ : ℝ} (G : TubeFamily δ) :
    ∃ (I : Finset (Fin G.card)),
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → (G.tube i).EssentiallyDistinct (G.tube j)) ∧
      (∀ i, i ∉ I → ∃ j ∈ I, ¬(G.tube i).EssentiallyDistinct (G.tube j)) := by
  classical
  let P : Finset (Fin G.card) → Prop := fun I =>
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (G.tube i).EssentiallyDistinct (G.tube j)

  let candidates : Finset (Finset (Fin G.card)) :=
    (Finset.powerset Finset.univ).filter P
  have h_empty_in : ∅ ∈ candidates := by simp [candidates, P]
  have h_candidates_nonempty : candidates.Nonempty := ⟨∅, h_empty_in⟩

  obtain ⟨I, hI_in, hI_max⟩ :=
    Finset.exists_max_image candidates Finset.card h_candidates_nonempty
  have hPI : P I := (Finset.mem_filter.mp hI_in).2
  have hI_max' : ∀ J ∈ candidates, J.card ≤ I.card := fun J hJ => hI_max J hJ

  have h_maximal : ∀ (i : Fin G.card), i ∉ I →
      ∃ (j : Fin G.card), j ∈ I ∧ ¬(G.tube i).EssentiallyDistinct (G.tube j) := by
    intro i hi
    by_cases h : (∃ j ∈ I, ¬(G.tube i).EssentiallyDistinct (G.tube j))
    · exact h
    · have h' : ∀ j ∈ I, (G.tube i).EssentiallyDistinct (G.tube j) := by simpa using h
      have h_insert : P (insert i I) := insert_preserves_P hPI hi h'
      have h_sub : insert i I ⊆ (Finset.univ : Finset (Fin G.card)) := Finset.subset_univ _
      have h_insert_in : insert i I ∈ candidates := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr h_sub, h_insert⟩
      have h9 : i ∉ I := hi
      have h10 : insert i I = ({i} : Finset (Fin G.card)) ∪ I := by
        ext x; simp [Finset.mem_insert]
      have h_card : (insert i I).card = I.card + 1 := by
        rw [h10]
        rw [Finset.card_union_of_disjoint
          (show Disjoint ({i} : Finset (Fin G.card)) I from by simp [h9])]
        simp [add_comm]
      have h_contra : (insert i I).card ≤ I.card := hI_max' (insert i I) h_insert_in
      rw [h_card] at h_contra
      omega

  exact ⟨I, hPI, h_maximal⟩

/-- **Essentially-distinct subfamily extraction.**

Given a tube family `G` where all tubes have the same positive finite volume `V`,
and for every tube `T_j` the total intersection volume with all tubes is at most
`C · V`, there exists an essentially-distinct subfamily `S` with
`|S| ≥ |G| / (2C + 1)`. -/
theorem exists_essentially_distinct_subfamily
    {δ : ℝ} (G : TubeFamily δ) (C V : ENNReal)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V) :
    ∃ (S : TubeSubfamily G),
      S.family.IsEssentiallyDistinct ∧
      (S.family.enncard : ENNReal) ≥ G.enncard / (2 * C + 1) := by
  classical
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'

  let P : Finset (Fin G.card) → Prop := fun I =>
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (G.tube i).EssentiallyDistinct (G.tube j)

  let candidates : Finset (Finset (Fin G.card)) :=
    (Finset.powerset Finset.univ).filter P
  have h_empty_in : ∅ ∈ candidates := by simp [candidates, P]
  have h_candidates_nonempty : candidates.Nonempty := ⟨∅, h_empty_in⟩

  obtain ⟨I, hI_in, hI_max⟩ :=
    Finset.exists_max_image candidates Finset.card h_candidates_nonempty
  have hPI : P I := (Finset.mem_filter.mp hI_in).2
  have hI_max' : ∀ J ∈ candidates, J.card ≤ I.card := fun J hJ => hI_max J hJ

  have h_maximal : ∀ (i : Fin G.card), i ∉ I →
      ∃ (j : Fin G.card), j ∈ I ∧ ¬(G.tube i).EssentiallyDistinct (G.tube j) := by
    intro i hi
    by_cases h : (∃ j ∈ I, ¬(G.tube i).EssentiallyDistinct (G.tube j))
    · exact h
    · have h' : ∀ j ∈ I, (G.tube i).EssentiallyDistinct (G.tube j) := by simpa using h
      have h_insert : P (insert i I) := insert_preserves_P hPI hi h'
      have h_sub : insert i I ⊆ (Finset.univ : Finset (Fin G.card)) := Finset.subset_univ _
      have h_insert_in : insert i I ∈ candidates := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr h_sub, h_insert⟩
      have h9 : i ∉ I := hi
      have h10 : insert i I = ({i} : Finset (Fin G.card)) ∪ I := by
        ext x; simp [Finset.mem_insert] <;> tauto
      have h_card : (insert i I).card = I.card + 1 := by
        rw [h10]
        rw [Finset.card_union_of_disjoint (show Disjoint ({i} : Finset (Fin G.card)) I from by simp [h9])]
        <;> simp [add_comm]
      have h_contra : (insert i I).card ≤ I.card := hI_max' (insert i I) h_insert_in
      rw [h_card] at h_contra
      omega

  choose f hf using fun i (hi : i ∉ I) => h_maximal i hi

  let f' : Fin G.card → Fin G.card := fun i =>
    if h : i ∉ I then f i h else i

  have h_f'_prop : ∀ (i : Fin G.card), i ∉ I →
      f' i ∈ I ∧ ¬(G.tube i).EssentiallyDistinct (G.tube (f' i)) := by
    intro i hi
    have h1 : f' i = f i hi := by simp [f', hi]
    rw [h1]; exact hf i hi

  let removed : Finset (Fin G.card) := Finset.univ \ I
  let A : Fin G.card → Finset (Fin G.card) := fun j =>
    removed.filter (fun i => f' i = j)

  have hA_subset : ∀ j, A j ⊆ removed := fun j => Finset.filter_subset _ _

  have hA_disjoint : ∀ j1 ∈ I, ∀ j2 ∈ I, j1 ≠ j2 → Disjoint (A j1) (A j2) := by
    intro j1 _ j2 _ hne
    simp only [A, Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : f' i = j1 := (Finset.mem_filter.mp hi1).2
    have h2 : f' i = j2 := (Finset.mem_filter.mp hi2).2
    rw [h1] at h2; exact hne h2

  have h_union : removed = Finset.biUnion I A := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_biUnion, A, Finset.mem_filter]
    constructor
    · intro hi
      have h_i_notin : i ∉ I := by
        simp only [removed, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi <;> exact hi
      have h_f'i_in_I : f' i ∈ I := (h_f'_prop i h_i_notin).1
      exact ⟨f' i, h_f'i_in_I, ⟨hi, rfl⟩⟩
    · rintro ⟨j, hj, ⟨h_i_removed, _⟩⟩
      exact h_i_removed

  have h_card_sum : removed.card = ∑ j ∈ I, (A j).card := by
    rw [h_union, Finset.card_biUnion hA_disjoint] <;> rfl

  have h_bound : ∀ j ∈ I, ((A j).card : ENNReal) ≤ 2 * C := by
    intro j hj
    have h1 : ∀ i ∈ A j,
        volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≥ V / 2 := by
      intro i hi
      have h_i_notin : i ∉ I := by
        have h2 : i ∈ removed := hA_subset j hi
        simp only [removed, Finset.mem_sdiff, Finset.mem_univ, true_and] at h2 <;> exact h2
      have h_f'_eq : f' i = j := (Finset.mem_filter.mp hi).2
      have h_orig : ¬(G.tube i).EssentiallyDistinct (G.tube (f' i)) := (h_f'_prop i h_i_notin).2
      have h_nd : ¬(G.tube i).EssentiallyDistinct (G.tube j) := by
        rw [h_f'_eq] at h_orig; exact h_orig
      have h_max : max (G.tube i).volume (G.tube j).volume = V := by
        rw [h_vol_eq i, h_vol_eq j] <;> simp
      have h_gt : (2 : ENNReal)⁻¹ * V < volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
        simpa [Kakeya.DeltaTube.EssentiallyDistinct, h_max] using h_nd
      have h_eq : V / 2 = (2 : ENNReal)⁻¹ * V := by
        simp [div_eq_mul_inv] <;> ring
      rw [h_eq]
      exact le_of_lt h_gt
    have h2 : ∑ i ∈ A j, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≥
        ((A j).card : ENNReal) * (V / 2) := by
      calc
        ∑ i ∈ A j, volume ((G.tube i).carrier ∩ (G.tube j).carrier)
          ≥ ∑ i ∈ A j, (V / 2) := Finset.sum_le_sum h1
        _ = ((A j).card : ENNReal) * (V / 2) := by
          simp [Finset.sum_const] <;> ring
    have h4 : ∑ i ∈ A j, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤
        ∑ i : Fin G.card, volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact (hA_subset j).trans (Finset.subset_univ _)
      · intro _ _ _; positivity
    have h5 : ∑ i : Fin G.card, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V := h_inter j
    have h6 : ((A j).card : ENNReal) * (V / 2) ≤ C * V := by
      calc
        ((A j).card : ENNReal) * (V / 2)
          ≤ ∑ i ∈ A j, volume ((G.tube i).carrier ∩ (G.tube j).carrier) := h2
        _ ≤ C * V := le_trans h4 h5
    have h9 : (2 : ENNReal)⁻¹ * 2 = 1 := by
      rw [ENNReal.inv_mul_cancel] <;> norm_num
    have h10 : (V / 2) * 2 = V := by
      have h11 : V / 2 = V * (2 : ENNReal)⁻¹ := by
        simp [div_eq_mul_inv] <;> rfl
      rw [h11]
      calc
        V * (2 : ENNReal)⁻¹ * 2
          = V * ((2 : ENNReal)⁻¹ * 2) := by rw [mul_assoc]
        _ = V * 1 := by rw [h9]
        _ = V := by simp
    have h7 : ((A j).card : ENNReal) * V ≤ (2 * C) * V := by
      calc
        ((A j).card : ENNReal) * V
          = ((A j).card : ENNReal) * ((V / 2) * 2) := by rw [h10]
        _ = (((A j).card : ENNReal) * (V / 2)) * 2 := by rw [mul_assoc]
        _ ≤ (C * V) * 2 := by gcongr
        _ = (2 * C) * V := by
          rw [mul_comm (C * V) (2 : ENNReal), mul_assoc]
    by_contra h8
    have h9 : 2 * C < ((A j).card : ENNReal) := by exact lt_of_not_ge h8
    have h10 : (2 * C) * V < ((A j).card : ENNReal) * V := by
      exact ENNReal.mul_lt_mul_left hV_pos.ne' hV_ne_top h9
    have h11 : (2 * C) * V < (2 * C) * V := lt_of_lt_of_le h10 h7
    exact lt_irrefl ((2 * C) * V) h11

  have h_removed_bound : (removed.card : ENNReal) ≤ (I.card : ENNReal) * (2 * C) := by
    calc
      (removed.card : ENNReal)
        = ∑ j ∈ I, ((A j).card : ENNReal) := by exact_mod_cast h_card_sum
      _ ≤ ∑ j ∈ I, (2 * C) := Finset.sum_le_sum h_bound
      _ = (I.card : ENNReal) * (2 * C) := by
        simp [Finset.sum_const] <;> ring

  have h_sub : I ⊆ (Finset.univ : Finset (Fin G.card)) := Finset.subset_univ I
  have h_univ_card : (Finset.univ : Finset (Fin G.card)).card = G.card := by simp
  have h2 : removed.card = G.card - I.card := by
    rw [Finset.card_sdiff_of_subset h_sub, h_univ_card]
  have h3 : I.card ≤ G.card := by
    have h31 : I.card ≤ (Finset.univ : Finset (Fin G.card)).card := Finset.card_le_card h_sub
    rw [h_univ_card] at h31
    exact h31
  have h4 : G.card = I.card + removed.card := by
    rw [h2]
    exact (Nat.add_sub_of_le h3).symm
  have h1 : (G.card : ENNReal) = (I.card : ENNReal) + (removed.card : ENNReal) := by
    exact_mod_cast h4

  have hI_card : (G.card : ENNReal) ≤ (I.card : ENNReal) * (2 * C + 1) := by
    rw [h1]
    have h5 : (I.card : ENNReal) + (removed.card : ENNReal) ≤
        (I.card : ENNReal) + (I.card : ENNReal) * (2 * C) := by
      exact add_le_add (le_refl (I.card : ENNReal)) h_removed_bound
    have h6 : (I.card : ENNReal) + (I.card : ENNReal) * (2 * C) =
        (I.card : ENNReal) * (2 * C + 1) := by
      rw [mul_add, mul_one] <;> ring
    rw [h6] at h5
    exact h5

  let S : TubeSubfamily G := TubeSubfamily.fromFinset G I

  have hS_distinct : S.family.IsEssentiallyDistinct := by
    intro i j hne
    let i' := S.embedding i
    let j' := S.embedding j
    have hi' : i' ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj' : j' ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have h_ne' : i' ≠ j' := by
      intro h; have : i = j := S.embedding.inj' h; exact hne this
    exact hPI i' hi' j' hj' h_ne'

  have hS_card : (S.family.enncard : ENNReal) = (I.card : ENNReal) := by
    simp [S, TubeSubfamily.fromFinset, TubeFamily.enncard] <;> rfl

  refine ⟨S, hS_distinct, ?_⟩
  rw [hS_card]
  by_cases hC_top : C = ⊤
  · -- C = ⊤, then denominator is ⊤ and division is 0
    have h14 : (2 * C + 1 : ENNReal) = ⊤ := by
      rw [hC_top] <;> simp
    rw [h14]
    simp
  · -- C ≠ ⊤
    have h12 : (2 * C + 1 : ENNReal) ≠ 0 := by positivity
    have h13 : (2 * C + 1 : ENNReal) ≠ ⊤ := by
      simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, hC_top] <;> tauto
    have h14 : G.enncard / (2 * C + 1) ≤ (I.card : ENNReal) := by
      rw [ENNReal.div_le_iff_le_mul (Or.inl h12) (Or.inl h13)]
      exact hI_card
    exact h14

/--
If every tube has at most `D` non-essentially-distinct neighbors, then one
can select an essentially-distinct subfamily retaining at least a
`1 / (D + 1)` share of any prescribed `ENNReal` index weight.
-/
theorem exists_weighted_essentially_distinct_subfamily_of_degree
    {δ : ℝ} (G : TubeFamily δ) (D : ℕ)
    (weight : Fin G.card → ENNReal)
    (hdegree :
      ∀ j : Fin G.card,
        ∃ neighbors : Finset (Fin G.card),
          neighbors.card ≤ D ∧
          ∀ i, i ≠ j →
            ¬(G.tube i).EssentiallyDistinct (G.tube j) →
            i ∈ neighbors) :
    ∃ (S : TubeSubfamily G),
      S.family.IsEssentiallyDistinct ∧
      (∑ i : Fin G.card, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) *
          ∑ i : Fin S.family.card, weight (S.embedding i) := by
  classical
  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => ¬(G.tube i).EssentiallyDistinct (G.tube j)
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j hij hji
    exact hij (essentiallyDistinct_symm.mpr hji)
  have hdegree' :
      ∀ j ∈ (Finset.univ : Finset (Fin G.card)),
        (Finset.univ.filter fun i => i ≠ j ∧ conflict j i).card ≤ D := by
    intro j _
    rcases hdegree j with ⟨neighbors, hneighbors_card, hneighbors⟩
    apply le_trans (Finset.card_le_card ?_) hneighbors_card
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact hneighbors i hi'.2.1 fun hdist =>
      hi'.2.2 (essentiallyDistinct_symm.mp hdist)
  rcases exists_heavy_bounded_conflict_free_class
      (Finset.univ : Finset (Fin G.card)) D weight conflict hsymm hdegree' with
    ⟨I, _hI_subset, hI_free, hmass⟩
  let S : TubeSubfamily G := TubeSubfamily.fromFinset G I
  have hS_distinct : S.family.IsEssentiallyDistinct := by
    intro i j hij
    have hi : S.embedding i ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj : S.embedding j ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have hne : S.embedding i ≠ S.embedding j := fun h => hij (S.embedding.injective h)
    rw [S.tube_eq i, S.tube_eq j]
    exact Classical.byContradiction fun hconflict =>
      hI_free (S.embedding i) hi (S.embedding j) hj hne hconflict
  have hweight :
      ∑ i ∈ I, weight i =
        ∑ i : Fin S.family.card, weight (S.embedding i) := by
    symm
    calc
      ∑ i : Fin S.family.card, weight (S.embedding i)
          = ∑ i ∈ Finset.map S.embedding Finset.univ, weight i := by
            rw [Finset.sum_map]
      _ = ∑ i ∈ I, weight i := by
        have himage :
            Finset.map S.embedding Finset.univ = I :=
          Finset.map_orderEmbOfFin_univ I rfl
        rw [himage]
  refine ⟨S, hS_distinct, ?_⟩
  simpa [hweight] using hmass

/-- Bounded-degree bicriteria form: the same essentially-distinct subfamily
retains both cardinality and an arbitrary nonnegative weight. -/
theorem exists_bicriteria_essentially_distinct_subfamily_of_degree
    {δ : ℝ} (G : TubeFamily δ) (D : ℕ)
    (weight : Fin G.card → ENNReal)
    (hdegree :
      ∀ j : Fin G.card,
        ∃ neighbors : Finset (Fin G.card),
          neighbors.card ≤ D ∧
          ∀ i, i ≠ j →
            ¬(G.tube i).EssentiallyDistinct (G.tube j) →
            i ∈ neighbors) :
    ∃ (S : TubeSubfamily G),
      S.family.IsEssentiallyDistinct ∧
      G.card ≤ (D + 1) * S.family.card ∧
      (∑ i : Fin G.card, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) *
          ∑ i : Fin S.family.card, weight (S.embedding i) := by
  classical
  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => ¬(G.tube i).EssentiallyDistinct (G.tube j)
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j hij hji
    exact hij (essentiallyDistinct_symm.mpr hji)
  have hdegree' :
      ∀ j ∈ (Finset.univ : Finset (Fin G.card)),
        (Finset.univ.filter fun i => i ≠ j ∧ conflict j i).card ≤ D := by
    intro j _
    rcases hdegree j with ⟨neighbors, hneighborsCard, hneighbors⟩
    apply le_trans (Finset.card_le_card ?_) hneighborsCard
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact hneighbors i hi'.2.1 fun hdist =>
      hi'.2.2 (essentiallyDistinct_symm.mp hdist)
  rcases exists_bicriteria_bounded_conflict_free_class
      (Finset.univ : Finset (Fin G.card)) D weight conflict hsymm hdegree' with
    ⟨I, _hsubset, hfree, hcard, hmass⟩
  let S : TubeSubfamily G := TubeSubfamily.fromFinset G I
  have hdistinct : S.family.IsEssentiallyDistinct := by
    intro i j hij
    have hi : S.embedding i ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj : S.embedding j ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have hne : S.embedding i ≠ S.embedding j :=
      fun h => hij (S.embedding.injective h)
    rw [S.tube_eq i, S.tube_eq j]
    exact Classical.byContradiction fun hconflict =>
      hfree (S.embedding i) hi (S.embedding j) hj hne hconflict
  have hweight :
      ∑ i ∈ I, weight i =
        ∑ i : Fin S.family.card, weight (S.embedding i) := by
    symm
    calc
      ∑ i : Fin S.family.card, weight (S.embedding i) =
          ∑ i ∈ Finset.map S.embedding Finset.univ, weight i := by
            rw [Finset.sum_map]
      _ = ∑ i ∈ I, weight i := by
        have himage : Finset.map S.embedding Finset.univ = I := by
          exact Finset.map_orderEmbOfFin_univ I rfl
        rw [himage]
  refine ⟨S, hdistinct, ?_, ?_⟩
  · change G.card ≤ (D + 1) * I.card
    simpa using hcard
  · simpa [hweight] using hmass

/--
An intersection-sum bound gives a finite conflict-neighborhood bound.  The
factor `2` comes from the definition of essential distinctness: every
conflicting tube contributes more than `V / 2` to the intersection sum.
-/
lemma nonDistinct_neighbors_card_le
    {δ : ℝ} (G : TubeFamily δ) (C V : ENNReal) (D : ℕ)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card,
        volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V)
    (hD : 2 * C ≤ (D : ENNReal)) :
    ∀ j : Fin G.card,
      ∃ neighbors : Finset (Fin G.card),
        neighbors.card ≤ D ∧
        ∀ i, i ≠ j →
          ¬(G.tube i).EssentiallyDistinct (G.tube j) →
          i ∈ neighbors := by
  classical
  intro j
  let neighbors : Finset (Fin G.card) :=
    Finset.univ.filter fun i =>
      i ≠ j ∧ ¬(G.tube i).EssentiallyDistinct (G.tube j)
  have hinter_lower :
      ((neighbors.card : ENNReal) * (V / 2)) ≤
        ∑ i ∈ neighbors,
          volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
    calc
      (neighbors.card : ENNReal) * (V / 2)
          = ∑ _i ∈ neighbors, V / 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ neighbors,
          volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_filter.mp hi
        have hmax :
            max (G.tube i).volume (G.tube j).volume = V := by
          rw [h_vol_eq i, h_vol_eq j]
          simp
        have hgt :
            (2 : ENNReal)⁻¹ * V <
              volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
          simpa [Kakeya.DeltaTube.EssentiallyDistinct, hmax] using hi'.2.2
        have heq : V / 2 = (2 : ENNReal)⁻¹ * V := by
          simp [div_eq_mul_inv]
          ring
        rw [heq]
        exact le_of_lt hgt
  have hinter_upper :
      ∑ i ∈ neighbors,
          volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V := by
    calc
      ∑ i ∈ neighbors,
          volume ((G.tube i).carrier ∩ (G.tube j).carrier)
          ≤ ∑ i : Fin G.card,
              volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_univ _
            · intro _ _ _
              positivity
      _ ≤ C * V := h_inter j
  have hhalf :
      (neighbors.card : ENNReal) * (V / 2) ≤ C * V :=
    hinter_lower.trans hinter_upper
  have htwo_inv : (2 : ENNReal)⁻¹ * 2 = 1 := by
    rw [ENNReal.inv_mul_cancel] <;> norm_num
  have hhalf_mul : (V / 2) * 2 = V := by
    have heq : V / 2 = V * (2 : ENNReal)⁻¹ := by
      simp [div_eq_mul_inv]
    rw [heq, mul_assoc, htwo_inv, mul_one]
  have hmul :
      (neighbors.card : ENNReal) * V ≤ (2 * C) * V := by
    calc
      (neighbors.card : ENNReal) * V
          = ((neighbors.card : ENNReal) * (V / 2)) * 2 := by
            rw [mul_assoc, hhalf_mul]
      _ ≤ (C * V) * 2 := by
            gcongr
      _ = (2 * C) * V := by ring
  have hcard : (neighbors.card : ENNReal) ≤ 2 * C := by
    by_contra h
    have hlt : 2 * C < (neighbors.card : ENNReal) := lt_of_not_ge h
    have hmul_lt :
        (2 * C) * V < (neighbors.card : ENNReal) * V :=
      ENNReal.mul_lt_mul_left hV_pos.ne' hV_ne_top hlt
    exact (not_lt_of_ge hmul) hmul_lt
  have hcardD : (neighbors.card : ENNReal) ≤ (D : ENNReal) :=
    hcard.trans hD
  refine ⟨neighbors, ?_, ?_⟩
  · exact_mod_cast hcardD
  · intro i hij hconflict
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hij, hconflict⟩

/--
Weighted essentially-distinct extraction from an intersection-sum bound.
-/
theorem exists_weighted_essentially_distinct_subfamily
    {δ : ℝ} (G : TubeFamily δ) (C V : ENNReal) (D : ℕ)
    (weight : Fin G.card → ENNReal)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card,
        volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V)
    (hD : 2 * C ≤ (D : ENNReal)) :
    ∃ (S : TubeSubfamily G),
      S.family.IsEssentiallyDistinct ∧
      (∑ i : Fin G.card, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) *
          ∑ i : Fin S.family.card, weight (S.embedding i) := by
  apply exists_weighted_essentially_distinct_subfamily_of_degree G D weight
  exact nonDistinct_neighbors_card_le G C V D
    hV_pos hV_ne_top h_vol_eq h_inter hD

/--
Shading-mass form of weighted essentially-distinct extraction.
-/
theorem exists_shading_heavy_essentially_distinct_subfamily
    {δ : ℝ} (G : TubeFamily δ) (C V : ENNReal) (D : ℕ)
    (Y : TubeShading G)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card,
        volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V)
    (hD : 2 * C ≤ (D : ENNReal)) :
    ∃ (S : TubeSubfamily G),
      S.family.IsEssentiallyDistinct ∧
      Y.mass ≤
        ((D + 1 : ℕ) : ENNReal) * (S.restrictShading Y).mass := by
  rcases exists_weighted_essentially_distinct_subfamily
      G C V D (fun i => volume (Y.carrier i))
      hV_pos hV_ne_top h_vol_eq h_inter hD with
    ⟨S, hS_distinct, hmass⟩
  refine ⟨S, hS_distinct, ?_⟩
  change
    (∑ i : Fin G.card, volume (Y.carrier i)) ≤
      ((D + 1 : ℕ) : ENNReal) *
        ∑ i : Fin S.family.card, volume (Y.carrier (S.embedding i))
  exact hmass

/--
Simultaneous cardinality and shading-mass retention from an intersection-sum
bound.  The same essentially-distinct subfamily satisfies both estimates.
-/
theorem exists_bicriteria_essentially_distinct_subfamily
    {δ : ℝ} (G : TubeFamily δ) (C V : ENNReal) (D : ℕ)
    (Y : TubeShading G)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card,
        volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V)
    (hD : 2 * C ≤ (D : ENNReal)) :
    ∃ (S : TubeSubfamily G),
      S.family.IsEssentiallyDistinct ∧
      G.card ≤ (D + 1) * S.family.card ∧
      Y.mass ≤
        ((D + 1 : ℕ) : ENNReal) * (S.restrictShading Y).mass := by
  classical
  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => ¬(G.tube i).EssentiallyDistinct (G.tube j)
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j hij hji
    exact hij (essentiallyDistinct_symm.mpr hji)
  have hdegree_cover := nonDistinct_neighbors_card_le
    G C V D hV_pos hV_ne_top h_vol_eq h_inter hD
  have hdegree :
      ∀ j ∈ (Finset.univ : Finset (Fin G.card)),
        (Finset.univ.filter fun i => i ≠ j ∧ conflict j i).card ≤ D := by
    intro j _
    rcases hdegree_cover j with ⟨neighbors, hneighbors_card, hneighbors⟩
    apply le_trans (Finset.card_le_card ?_) hneighbors_card
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact hneighbors i hi'.2.1 fun hdist =>
      hi'.2.2 (essentiallyDistinct_symm.mp hdist)
  rcases exists_bicriteria_bounded_conflict_free_class
      (Finset.univ : Finset (Fin G.card)) D
      (fun i => volume (Y.carrier i)) conflict hsymm hdegree with
    ⟨I, _hI_subset, hI_free, hcard, hmass⟩
  let S : TubeSubfamily G := TubeSubfamily.fromFinset G I
  have hS_distinct : S.family.IsEssentiallyDistinct := by
    intro i j hij
    have hi : S.embedding i ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj : S.embedding j ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have hne : S.embedding i ≠ S.embedding j := fun h =>
      hij (S.embedding.injective h)
    rw [S.tube_eq i, S.tube_eq j]
    exact Classical.byContradiction fun hconflict =>
      hI_free (S.embedding i) hi (S.embedding j) hj hne hconflict
  have hS_card : S.family.card = I.card := rfl
  have hS_mass :
      (S.restrictShading Y).mass =
        ∑ i ∈ I, volume (Y.carrier i) := by
    dsimp only [TubeSubfamily.restrictShading, Shading.mass]
    calc
      ∑ i : Fin S.family.card, volume (Y.carrier (S.embedding i))
          = ∑ i ∈ Finset.map S.embedding Finset.univ,
              volume (Y.carrier i) := by
            rw [Finset.sum_map]
      _ = ∑ i ∈ I, volume (Y.carrier i) := by
        have himage :
            Finset.map S.embedding Finset.univ = I :=
          Finset.map_orderEmbOfFin_univ I rfl
        rw [himage]
  refine ⟨S, hS_distinct, ?_, ?_⟩
  · simpa [hS_card] using hcard
  · rw [hS_mass]
    exact hmass

end Kakeya.Streamlined
