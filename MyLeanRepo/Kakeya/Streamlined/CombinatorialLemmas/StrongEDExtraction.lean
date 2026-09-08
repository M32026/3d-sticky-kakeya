import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring

/-!
# K-strong essentially-distinct subfamily extraction

Given a tube family with an intersection-sum bound, extract a subfamily that is
K-strongly essentially distinct: pairwise intersection volume ≤ V / K.

This generalizes `EssentiallyDistinctSubfamily` (which handles K = 2) to
arbitrary K ≥ 1. The mass retention factor is `1 / (⌈C * K⌉ + 1)`.

## Main result

- `exists_strong_ed_subfamily`: intersection-sum bound → K-strong ED subfamily
  with weighted mass retention.
-/

noncomputable section

open MeasureTheory Finset Classical

namespace Kakeya.Streamlined

/-- Two tubes are K-strongly essentially distinct if their intersection volume
is at most `V / K`, where `V` is the common tube volume. -/
def IsKStrongEssentiallyDistinct {δ : ℝ} (T U : Kakeya.DeltaTube δ)
    (V : ENNReal) (K : ENNReal) : Prop :=
  volume (T.carrier ∩ U.carrier) ≤ V / K

/-- Extract a K-strong ED subfamily from a direct K-strong conflict degree bound.

Given that every tube has at most `D` K-strong conflicts (tubes with
`vol(T_i ∩ T_j) > V / K`), apply the bounded-conflict weighted extraction
to obtain a K-strong ED subfamily retaining at least `1 / (D + 1)` of any
prescribed weight. -/
theorem exists_strong_ed_subfamily_of_degree
    {δ : ℝ} (G : TubeFamily δ)
    (V K : ENNReal) (D : ℕ)
    (weight : Fin G.card → ENNReal)
    (hdegree : ∀ (j : Fin G.card),
      ∃ (neighbors : Finset (Fin G.card)),
        neighbors.card ≤ D ∧
        ∀ (i : Fin G.card), i ≠ j →
          volume ((G.tube i).carrier ∩ (G.tube j).carrier) > V / K → i ∈ neighbors) :
    ∃ (S : TubeSubfamily G),
      (∀ i j, i ≠ j →
        IsKStrongEssentiallyDistinct (S.family.tube i) (S.family.tube j) V K) ∧
      (∑ i : Fin G.card, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) *
          ∑ i : Fin S.family.card, weight (S.embedding i) := by
  classical
  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => volume ((G.tube i).carrier ∩ (G.tube j).carrier) > V / K
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j h
    have h_comm : (G.tube i).carrier ∩ (G.tube j).carrier =
        (G.tube j).carrier ∩ (G.tube i).carrier := by
      ext x; simp [and_comm]
    simpa [conflict, h_comm] using h
  have hdegree' :
      ∀ j ∈ (Finset.univ : Finset (Fin G.card)),
        (Finset.univ.filter fun i => i ≠ j ∧ conflict j i).card ≤ D := by
    intro j _
    rcases hdegree j with ⟨neighbors, hneighbors_card, hneighbors⟩
    apply le_trans (Finset.card_le_card ?_) hneighbors_card
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hconf : conflict j i := hi'.2.2
    have h_comm : (G.tube j).carrier ∩ (G.tube i).carrier =
        (G.tube i).carrier ∩ (G.tube j).carrier := by
      ext x; simp [and_comm]
    have hgt : volume ((G.tube i).carrier ∩ (G.tube j).carrier) > V / K := by
      simpa [conflict, h_comm] using hconf
    exact hneighbors i hi'.2.1 hgt
  rcases exists_heavy_bounded_conflict_free_class
      (Finset.univ : Finset (Fin G.card)) D weight conflict hsymm hdegree' with
    ⟨I, _hI_subset, hI_free, hmass⟩
  let S : TubeSubfamily G := TubeSubfamily.fromFinset G I
  have hS_strong_ed :
      ∀ i j, i ≠ j →
        IsKStrongEssentiallyDistinct (S.family.tube i) (S.family.tube j) V K := by
    intro i j hij
    have hi : S.embedding i ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj : S.embedding j ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have hne : S.embedding i ≠ S.embedding j := fun h => hij (S.embedding.injective h)
    have h : ¬ conflict (S.embedding i) (S.embedding j) :=
      hI_free (S.embedding i) hi (S.embedding j) hj hne
    have h' : ¬ (volume ((G.tube (S.embedding i)).carrier ∩
        (G.tube (S.embedding j)).carrier) > V / K) := h
    have h_le : volume ((G.tube (S.embedding i)).carrier ∩
        (G.tube (S.embedding j)).carrier) ≤ V / K := le_of_not_gt h'
    have h_tube_eq1 : S.family.tube i = G.tube (S.embedding i) := S.tube_eq i
    have h_tube_eq2 : S.family.tube j = G.tube (S.embedding j) := S.tube_eq j
    rw [h_tube_eq1, h_tube_eq2]
    exact h_le
  have hweight :
      ∑ i ∈ I, weight i =
        ∑ i : Fin S.family.card, weight (S.embedding i) := by
    symm
    calc
      ∑ i : Fin S.family.card, weight (S.embedding i)
          = ∑ i ∈ Finset.map S.embedding Finset.univ, weight i := by
            rw [Finset.sum_map]
      _ = ∑ i ∈ I, weight i := by
        have himage : Finset.map S.embedding Finset.univ = I :=
          Finset.map_orderEmbOfFin_univ I rfl
        rw [himage]
  refine ⟨S, hS_strong_ed, ?_⟩
  simpa [hweight] using hmass

/-- Extract a K-strong ED subfamily from an intersection-sum bound.

Given `∑_i vol(T_i ∩ T_j) ≤ C * V` for every j, the number of tubes with
`vol(T_i ∩ T_j) > V / K` is at most `C * K`. Applying the bounded-conflict
weighted extraction gives a K-strong ED subfamily retaining at least
`1 / (⌈C * K⌉ + 1)` of any prescribed weight. -/
theorem exists_strong_ed_subfamily
    {δ : ℝ} (G : TubeFamily δ)
    (V C K : ENNReal) (D : ℕ)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (hK_pos : 0 < K) (hK_ne_top : K ≠ ⊤)
    (_h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V)
    (hD : C * K ≤ (D : ENNReal))
    (weight : Fin G.card → ENNReal) :
    ∃ (S : TubeSubfamily G),
      (∀ i j, i ≠ j →
        IsKStrongEssentiallyDistinct (S.family.tube i) (S.family.tube j) V K) ∧
      (∑ i : Fin G.card, weight i) ≤
        ((D + 1 : ℕ) : ENNReal) *
          ∑ i : Fin S.family.card, weight (S.embedding i) := by
  classical
  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => volume ((G.tube i).carrier ∩ (G.tube j).carrier) > V / K
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j h
    have h_comm : (G.tube i).carrier ∩ (G.tube j).carrier =
        (G.tube j).carrier ∩ (G.tube i).carrier := by
      ext x; simp [and_comm]
    simpa [conflict, h_comm] using h
  have hdegree :
      ∀ j ∈ (Finset.univ : Finset (Fin G.card)),
        (Finset.univ.filter fun i => i ≠ j ∧ conflict j i).card ≤ D := by
    intro j _
    let neighbors : Finset (Fin G.card) :=
      Finset.univ.filter fun i => i ≠ j ∧ conflict j i
    have hinter_lower :
        ((neighbors.card : ENNReal) * (V / K)) ≤
          ∑ i ∈ neighbors, volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
      calc
        (neighbors.card : ENNReal) * (V / K)
          = ∑ _i ∈ neighbors, V / K := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ neighbors, volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_filter.mp hi
          have hconf : conflict j i := hi'.2.2
          have h_comm : (G.tube j).carrier ∩ (G.tube i).carrier =
              (G.tube i).carrier ∩ (G.tube j).carrier := by
            ext x; simp [and_comm]
          have hgt : volume ((G.tube i).carrier ∩ (G.tube j).carrier) > V / K := by
            simpa [conflict, h_comm] using hconf
          exact le_of_lt hgt
    have hinter_upper :
        ∑ i ∈ neighbors, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V := by
      calc
        ∑ i ∈ neighbors, volume ((G.tube i).carrier ∩ (G.tube j).carrier)
          ≤ ∑ i : Fin G.card, volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.subset_univ _
            · intro _ _ _; positivity
        _ ≤ C * V := h_inter j
    have hhalf :
        (neighbors.card : ENNReal) * (V / K) ≤ C * V :=
      hinter_lower.trans hinter_upper
    have hK_ne_zero : K ≠ 0 := hK_pos.ne'
    have h_div_mul : (V / K) * K = V := by
      have h1 : V / K = V * K⁻¹ := by simp [div_eq_mul_inv]
      rw [h1, mul_assoc]
      have h2 : K⁻¹ * K = 1 := ENNReal.inv_mul_cancel hK_ne_zero hK_ne_top
      rw [h2, mul_one]
    have hmul :
        (neighbors.card : ENNReal) * V ≤ (C * K) * V := by
      calc
        (neighbors.card : ENNReal) * V
          = ((neighbors.card : ENNReal) * (V / K)) * K := by
            rw [mul_assoc, h_div_mul]
        _ ≤ (C * V) * K := by gcongr
        _ = (C * K) * V := by ring
    have hcard : (neighbors.card : ENNReal) ≤ C * K := by
      by_contra h
      have hlt : C * K < (neighbors.card : ENNReal) := lt_of_not_ge h
      have hmul_lt : (C * K) * V < (neighbors.card : ENNReal) * V :=
        ENNReal.mul_lt_mul_left hV_pos.ne' hV_ne_top hlt
      exact (not_lt_of_ge hmul) hmul_lt
    have hcardD : (neighbors.card : ENNReal) ≤ (D : ENNReal) :=
      hcard.trans hD
    exact_mod_cast hcardD
  rcases exists_heavy_bounded_conflict_free_class
      (Finset.univ : Finset (Fin G.card)) D weight conflict hsymm hdegree with
    ⟨I, _hI_subset, hI_free, hmass⟩
  let S : TubeSubfamily G := TubeSubfamily.fromFinset G I
  have hS_strong_ed :
      ∀ i j, i ≠ j →
        IsKStrongEssentiallyDistinct (S.family.tube i) (S.family.tube j) V K := by
    intro i j hij
    have hi : S.embedding i ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj : S.embedding j ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have hne : S.embedding i ≠ S.embedding j := fun h => hij (S.embedding.injective h)
    have h : ¬ conflict (S.embedding i) (S.embedding j) :=
      hI_free (S.embedding i) hi (S.embedding j) hj hne
    have h' : ¬ (volume ((G.tube (S.embedding i)).carrier ∩
        (G.tube (S.embedding j)).carrier) > V / K) := h
    have h_le : volume ((G.tube (S.embedding i)).carrier ∩
        (G.tube (S.embedding j)).carrier) ≤ V / K := le_of_not_gt h'
    have h_tube_eq1 : S.family.tube i = G.tube (S.embedding i) := S.tube_eq i
    have h_tube_eq2 : S.family.tube j = G.tube (S.embedding j) := S.tube_eq j
    rw [h_tube_eq1, h_tube_eq2]
    exact h_le
  have hweight :
      ∑ i ∈ I, weight i =
        ∑ i : Fin S.family.card, weight (S.embedding i) := by
    symm
    calc
      ∑ i : Fin S.family.card, weight (S.embedding i)
          = ∑ i ∈ Finset.map S.embedding Finset.univ, weight i := by
            rw [Finset.sum_map]
      _ = ∑ i ∈ I, weight i := by
        have himage : Finset.map S.embedding Finset.univ = I :=
          Finset.map_orderEmbOfFin_univ I rfl
        rw [himage]
  refine ⟨S, hS_strong_ed, ?_⟩
  simpa [hweight] using hmass

/-- Shading-mass form of K-strong ED extraction. -/
theorem exists_strong_ed_shading_subfamily
    {δ : ℝ} (G : TubeFamily δ)
    (V C K : ENNReal) (D : ℕ)
    (hV_pos : 0 < V) (hV_ne_top : V ≠ ⊤)
    (hK_pos : 0 < K) (hK_ne_top : K ≠ ⊤)
    (_h_vol_eq : ∀ i, (G.tube i).volume = V)
    (h_inter : ∀ (j : Fin G.card),
      ∑ i : Fin G.card, volume ((G.tube i).carrier ∩ (G.tube j).carrier) ≤ C * V)
    (hD : C * K ≤ (D : ENNReal))
    (Y : TubeShading G) :
    ∃ (S : TubeSubfamily G),
      (∀ i j, i ≠ j →
        IsKStrongEssentiallyDistinct (S.family.tube i) (S.family.tube j) V K) ∧
      Y.mass ≤ ((D + 1 : ℕ) : ENNReal) * (S.restrictShading Y).mass := by
  rcases exists_strong_ed_subfamily G V C K D hV_pos hV_ne_top hK_pos hK_ne_top
      _h_vol_eq h_inter hD (fun i => volume (Y.carrier i)) with
    ⟨S, hS_strong_ed, hmass⟩
  refine ⟨S, hS_strong_ed, ?_⟩
  change (∑ i : Fin G.card, volume (Y.carrier i)) ≤
      ((D + 1 : ℕ) : ENNReal) *
        ∑ i : Fin S.family.card, volume (Y.carrier (S.embedding i))
  exact hmass

end Kakeya.Streamlined
