module

public import MyLeanRepo.Compat
public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound

@[expose] public section

/-!
# Cardinality lower bound for T_y

## Main result

`cardinality_lower_bound`: |T_y| ≥ δ^{-2s}/(3C²)

## Proof route

1. `covering_lower_bound` gives |X| ≥ C^{-1}δ^{-s} and |T_x| ≥ C^{-1}δ^{-s}.
2. Sum over x: Σ|T_x| ≥ C^{-2}δ^{-2s}.
3. Double counting with overlap ≤ 3: Σ|T_x| ≤ 3|T_y|.
4. Hence |T_y| ≥ δ^{-2s}/(3C²).

## Whiteprint node

`cardinality_lower_bound`
-/

namespace ProductLikeIncidence

noncomputable section


open scoped ENNReal

-- ======================================================================
-- Helper: finiteness from ENNReal encard bound
-- ======================================================================

private lemma finite_of_ennreal_encard_bound {α : Type*} {S : Set α} {r : ℝ}
    (h : ENat.toENNReal S.encard ≤ ENNReal.ofReal r) : S.Finite := by
  have h1 : ENat.toENNReal S.encard ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have h2 : S.encard ≠ ⊤ := by
    intro h3
    rw [h3] at h1
    simp at h1
  have h3 : S.encard < ⊤ := lt_top_iff_ne_top.mpr h2
  exact Set.encard_lt_top_iff.mp h3

-- ======================================================================
-- Dyadic cube facts
-- ======================================================================

private lemma dyadicCubes_disjoint {d : ℕ} {δ : ℝ} (hpos : 0 < δ) {k1 k2 : Fin d → ℤ}
    (h : k1 ≠ k2) : Disjoint (dyadicCube δ k1) (dyadicCube δ k2) := by
  have h' : ∃ i : Fin d, k1 i ≠ k2 i := by
    by_contra h''
    push Not at h''
    have : k1 = k2 := by funext i; exact h'' i
    exact h this
  rcases h' with ⟨i, hi⟩
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have h1 : x i ∈ Set.Ico (δ * (k1 i : ℝ)) (δ * ((k1 i : ℝ) + 1)) := hx1 i
  have h2 : x i ∈ Set.Ico (δ * (k2 i : ℝ)) (δ * ((k2 i : ℝ) + 1)) := hx2 i
  by_cases h_lt : k1 i < k2 i
  · have h3 : (k1 i : ℝ) + 1 ≤ (k2 i : ℝ) := by exact_mod_cast h_lt
    have h4 : δ * ((k1 i : ℝ) + 1) ≤ δ * (k2 i : ℝ) := by gcongr
    have h5 : x i < δ * ((k1 i : ℝ) + 1) := h1.2
    have h6 : δ * (k2 i : ℝ) ≤ x i := h2.1
    have h7 : x i < x i := by
      calc x i < δ * ((k1 i : ℝ) + 1) := h5
           _ ≤ δ * (k2 i : ℝ) := h4
           _ ≤ x i := h6
    exact False.elim (lt_irrefl (x i) h7)
  · have h_gt : k2 i < k1 i := by omega
    have h3 : (k2 i : ℝ) + 1 ≤ (k1 i : ℝ) := by exact_mod_cast h_gt
    have h4 : δ * ((k2 i : ℝ) + 1) ≤ δ * (k1 i : ℝ) := by gcongr
    have h5 : x i < δ * ((k2 i : ℝ) + 1) := h2.2
    have h6 : δ * (k1 i : ℝ) ≤ x i := h1.1
    have h7 : x i < x i := by
      calc x i < δ * ((k2 i : ℝ) + 1) := h5
           _ ≤ δ * (k1 i : ℝ) := h4
           _ ≤ x i := h6
    exact False.elim (lt_irrefl (x i) h7)

/-- General: δ-covering number ≤ cardinality (pick one point per disjoint cube). -/
lemma covering_number_le_encard {d : ℕ} {δ : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin d))} (hδ : 0 < δ) :
    ENat.toENNReal (dyadicCoveringNumber δ P) ≤ ENat.toENNReal P.encard := by
  let S := dyadicCubesMeeting δ P
  have h_main : ∀ Q ∈ S, (Q ∩ P).Nonempty := fun Q hQ => hQ.2
  classical
  let f : Set (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) := fun Q =>
    if hQ : Q ∈ S then Classical.choose (h_main Q hQ) else Classical.arbitrary _
  have hf1 : ∀ Q ∈ S, f Q ∈ Q ∩ P := by
    intro Q hQ
    have h : f Q = Classical.choose (h_main Q hQ) := by simp [f, hQ]
    rw [h]; exact Classical.choose_spec (h_main Q hQ)
  have h_disj : ∀ Q1 ∈ S, ∀ Q2 ∈ S, Q1 ≠ Q2 → Disjoint Q1 Q2 := by
    intro Q1 hQ1 Q2 hQ2 hne
    rcases hQ1.1 with ⟨k1, rfl⟩
    rcases hQ2.1 with ⟨k2, rfl⟩
    have h : k1 ≠ k2 := by intro h'; apply hne; congr
    exact dyadicCubes_disjoint hδ h
  have h_inj : Set.InjOn f S := by
    intro Q1 hQ1 Q2 hQ2 h_eq
    by_contra hne
    have h_disj' : Disjoint Q1 Q2 := h_disj Q1 hQ1 Q2 hQ2 hne
    have h1 : f Q1 ∈ Q1 := (hf1 Q1 hQ1).1
    have h2 : f Q2 ∈ Q2 := (hf1 Q2 hQ2).1
    rw [h_eq] at h1
    exact Set.disjoint_left.mp h_disj' h1 h2
  have h_image_subset : f '' S ⊆ P := by
    rintro y ⟨Q, hQ, rfl⟩
    exact (hf1 Q hQ).2
  have h4 : (f '' S).encard = S.encard := h_inj.encard_image
  have h5 : S.encard ≤ P.encard := by
    rw [←h4]; exact Set.encard_mono h_image_subset
  exact_mod_cast h5

lemma dyadicCoveringNumber_cellRealization {α : Type*} {δ : ℝ} {S : Set α}
    {cell : α → Set (EuclideanSpace ℝ (Fin 2))}
    (hpos : 0 < δ)
    (hcell : ∀ a ∈ S, cell a ∈ dyadicCubes 2 δ)
    (hcell_inj : Set.InjOn cell S) :
    dyadicCoveringNumber δ (cellRealization cell S) = S.encard := by
  have h_main : dyadicCubesMeeting δ (cellRealization cell S) = cell '' S := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hQ_cube, ⟨p, hpQ, hpS⟩⟩
      have hpS' : ∃ (a : α), a ∈ S ∧ p ∈ cell a := by
        simpa [cellRealization, Set.mem_iUnion] using hpS
      rcases hpS' with ⟨a, haS, hpa⟩
      have hca : cell a ∈ dyadicCubes 2 δ := hcell a haS
      have h_inter : (Q ∩ cell a).Nonempty := ⟨p, ⟨hpQ, hpa⟩⟩
      have hQ_eq : Q = cell a := by
        rcases hQ_cube with ⟨kQ, hQ_cube_eq⟩
        rcases hca with ⟨ka, hca_eq⟩
        by_contra hne
        have h_kne : kQ ≠ ka := by
          intro h_eq
          rw [h_eq] at hQ_cube_eq
          exact hne (by rw [hQ_cube_eq, hca_eq])
        have h_disj : Disjoint (dyadicCube δ kQ) (dyadicCube δ ka) := dyadicCubes_disjoint hpos h_kne
        have h_empty : (dyadicCube δ kQ) ∩ (dyadicCube δ ka) = ∅ :=
          (Set.disjoint_iff_inter_eq_empty).mp h_disj
        rw [hQ_cube_eq, hca_eq] at h_inter
        rw [h_empty] at h_inter
        exact Set.not_nonempty_empty h_inter
      exact ⟨a, haS, hQ_eq.symm⟩
    · rintro ⟨a, haS, rfl⟩
      have hca : cell a ∈ dyadicCubes 2 δ := hcell a haS
      have h_nonempty : (cell a).Nonempty := by
        rcases hca with ⟨k, hca_eq⟩
        rw [hca_eq]
        exact dyadicCube_nonempty hpos k
      constructor
      · exact hca
      · let y := h_nonempty.some
        have hy1 : y ∈ cell a := h_nonempty.some_mem
        have hy2 : y ∈ cellRealization cell S := by
          have h : ∃ (x : α), x ∈ S ∧ y ∈ cell x := ⟨a, haS, hy1⟩
          simpa [cellRealization, Set.mem_iUnion] using h
        exact ⟨y, hy1, hy2⟩
  rw [dyadicCoveringNumber, h_main]
  have h_encard : (cell '' S).encard = S.encard := by exact Set.InjOn.encard_image hcell_inj
  exact h_encard

lemma dyadicCoveringNumber_realLineCopy {δ : ℝ} {X : Set ℝ}
    (hpos : 0 < δ) (hX_grid : X ⊆ deltaGrid δ) :
    dyadicCoveringNumber δ (realLineCopy X) = X.encard := by
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k => dyadicCube δ (fun _ => k)
  let KSet : Set ℤ := {k | δ * (k : ℝ) ∈ X}
  have h_f_inj : Function.Injective f := by
    intro k1 k2 h
    have h1 : (f k1).Nonempty := by
      dsimp only [f]
      exact dyadicCube_nonempty hpos (fun _ : Fin 1 => k1)
    rcases h1 with ⟨x, hx⟩
    have h2 : x ∈ f k2 := by
      have h3 : f k1 = f k2 := h
      exact h3 ▸ hx
    have h31 : δ * (k1 : ℝ) ≤ x 0 := (hx 0).1
    have h32 : x 0 < δ * ((k1 : ℝ) + 1) := (hx 0).2
    have h41 : δ * (k2 : ℝ) ≤ x 0 := (h2 0).1
    have h42 : x 0 < δ * ((k2 : ℝ) + 1) := (h2 0).2
    by_cases h_lt : k1 < k2
    · have h5 : (k1 : ℝ) + 1 ≤ (k2 : ℝ) := by exact_mod_cast h_lt
      have h6 : δ * ((k1 : ℝ) + 1) ≤ δ * (k2 : ℝ) := by gcongr
      have h_contra : x 0 < x 0 := by
        calc x 0 < δ * ((k1 : ℝ) + 1) := h32
             _ ≤ δ * (k2 : ℝ) := h6
             _ ≤ x 0 := h41
      exact False.elim (lt_irrefl (x 0) h_contra)
    · by_cases h_gt : k2 < k1
      · have h5 : (k2 : ℝ) + 1 ≤ (k1 : ℝ) := by exact_mod_cast h_gt
        have h6 : δ * ((k2 : ℝ) + 1) ≤ δ * (k1 : ℝ) := by gcongr
        have h_contra : x 0 < x 0 := by
          calc x 0 < δ * ((k2 : ℝ) + 1) := h42
               _ ≤ δ * (k1 : ℝ) := h6
               _ ≤ x 0 := h31
        exact False.elim (lt_irrefl (x 0) h_contra)
      · omega
  have h_fin1 : ∀ (i : Fin 1), i = 0 := by
    intro i
    exact Fin.ext (by simp)
  have h_main : dyadicCubesMeeting δ (realLineCopy X) = f '' KSet := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image, KSet]
    constructor
    · rintro ⟨hQ_cube, ⟨p, hpQ, hpX⟩⟩
      rcases hQ_cube with ⟨k, hQ_eq⟩
      let k0 : ℤ := k 0
      have hQ_eq2 : Q = f k0 := by
        have h_cube_eq : dyadicCube δ k = dyadicCube δ (fun _ : Fin 1 => k0) := by
          congr with i
          have h_i : i = 0 := h_fin1 i
          rw [h_i] <;> rfl
        rw [hQ_eq, h_cube_eq] <;> rfl
      have hpx0 : p 0 ∈ X := hpX
      have hpk : p 0 ∈ Set.Ico (δ * (k0 : ℝ)) (δ * ((k0 : ℝ) + 1)) := by
        have h : p ∈ dyadicCube δ k := by exact hQ_eq ▸ hpQ
        have h' := h 0
        simpa [k0] using h'
      have h_grid : p 0 ∈ deltaGrid δ := hX_grid hpx0
      rcases h_grid with ⟨j, hj⟩
      have h_eq : p 0 = δ * (j : ℝ) := hj
      have h1 : δ * (j : ℝ) ∈ Set.Ico (δ * (k0 : ℝ)) (δ * ((k0 : ℝ) + 1)) := by
        rw [← h_eq] <;> exact hpk
      have h2 : (k0 : ℝ) ≤ (j : ℝ) := by
        have h3 : δ * (k0 : ℝ) ≤ δ * (j : ℝ) := h1.1
        nlinarith
      have h4 : (j : ℝ) < (k0 : ℝ) + 1 := by
        have h5 : δ * (j : ℝ) < δ * ((k0 : ℝ) + 1) := h1.2
        nlinarith
      have h2' : k0 ≤ j := by exact_mod_cast h2
      have h4' : j < k0 + 1 := by exact_mod_cast h4
      have h_j_eq_k : j = k0 := by omega
      refine ⟨k0, ?_, hQ_eq2.symm⟩
      rw [← h_j_eq_k, ← h_eq]
      exact hpx0
    · rintro ⟨k, hk, rfl⟩
      have h1 : δ * (k : ℝ) ∈ X := hk
      let g : Fin 1 → ℝ := fun _ => δ * (k : ℝ)
      let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm g
      have hpQ : p ∈ f k := by
        intro i
        have hpi : p i = g i := by rfl
        rw [hpi]
        simp [f, g, Set.mem_Ico] <;> linarith
      have hpX : p ∈ realLineCopy X := by
        have h2 : p 0 = δ * (k : ℝ) := by rfl
        simpa [realLineCopy, h2] using h1
      exact ⟨⟨fun _ => k, rfl⟩, ⟨p, hpQ, hpX⟩⟩
  rw [dyadicCoveringNumber, h_main]
  have h_encard1 : (f '' KSet).encard = KSet.encard := by exact Function.Injective.encard_image h_f_inj KSet
  rw [h_encard1]
  let g : ℤ → ℝ := fun k => δ * (k : ℝ)
  have h_inj2 : Function.Injective g := by
    intro k1 k2 h
    have : δ * (k1 : ℝ) = δ * (k2 : ℝ) := h
    have : (k1 : ℝ) = (k2 : ℝ) := by
      apply (mul_right_inj' (ne_of_gt hpos)).mp
      exact this
    exact_mod_cast this
  have h_X_eq : X = g '' KSet := by
    ext x
    simp only [KSet, g, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hx
      have h_grid : x ∈ deltaGrid δ := hX_grid hx
      rcases h_grid with ⟨k, hk⟩
      refine ⟨k, ?_, hk.symm⟩
      simpa [g] using hk ▸ hx
    · rintro ⟨k, hk, rfl⟩
      exact hk
  have h_encard2 : X.encard = KSet.encard := by
    rw [h_X_eq]
    have h : (g '' KSet).encard = KSet.encard := by exact Function.Injective.encard_image h_inj2 KSet
    exact h
  exact h_encard2.symm

-- ======================================================================
-- Bounded overlap double counting
-- ======================================================================

private lemma bounded_overlap_finset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (T : α → Finset β) (K : ℕ)
    (h : ∀ b ∈ s.biUnion T, (s.filter (fun i => b ∈ T i)).card ≤ K) :
    ∑ i ∈ s, (T i).card ≤ K * (s.biUnion T).card := by
  let incidences := s.sigma T
  let f : (Σ _ : α, β) → β := fun p => p.2
  have h1 : incidences.card = ∑ i ∈ s, (T i).card := by rw [Finset.card_sigma]
  have h2 : Finset.image f incidences = s.biUnion T := by
    ext b; simp [incidences, f] <;> aesop
  have h3 : ∀ b ∈ Finset.image f incidences,
      (Finset.filter (fun p : Σ _ : α, β => f p = b) incidences).card ≤ K := by
    intro b hb
    rw [h2] at hb
    have h4 : (Finset.filter (fun p : Σ _ : α, β => f p = b) incidences).card =
        (s.filter (fun i => b ∈ T i)).card := by
      let g : α → (Σ _ : α, β) := fun i => ⟨i, b⟩
      have h_inj : Function.Injective g := by intro i j h; simpa [g] using h
      have h_image : Finset.image g (s.filter (fun i => b ∈ T i)) =
          Finset.filter (fun p : Σ _ : α, β => f p = b) incidences := by
        ext p; simp [g, incidences, f] <;> aesop
      rw [←h_image, Finset.card_image_of_injective _ h_inj]
    rw [h4]
    exact h b hb
  have h5 := Finset.card_le_mul_card_image incidences K h3
  rw [h1, h2] at h5
  exact h5

lemma bounded_overlap_set_3 {α β : Type*}
    (S : Set α) (T : α → Set β)
    (hS : S.Finite)
    (hT : ∀ i ∈ S, (T i).Finite)
    (h : ∀ b ∈ ⋃ i ∈ S, T i,
        {i ∈ S | b ∈ T i}.Finite ∧ {i ∈ S | b ∈ T i}.encard ≤ 3) :
    ENat.toENNReal (⋃ i ∈ S, T i).encard * 3 ≥
      ∑ᶠ i ∈ S, ENat.toENNReal (T i).encard := by
  classical
  let sFinset := hS.toFinset
  let TFinset : α → Finset β := fun i =>
    if h : i ∈ S then (hT i h).toFinset else ∅
  have hTFinset_eq : ∀ i ∈ S, (TFinset i : Set β) = T i := by
    intro i hi
    simp [TFinset, hi]
  have h_coe_s : (sFinset : Set α) = S := by exact hS.coe_toFinset
  have h_union : (⋃ i ∈ S, T i) = ↑(sFinset.biUnion TFinset) := by
    ext b
    have h1 : b ∈ (⋃ i ∈ S, T i) ↔ ∃ i ∈ S, b ∈ T i := by
      simp [Set.mem_iUnion]
    have h2 : b ∈ (↑(sFinset.biUnion TFinset) : Set β) ↔ ∃ i ∈ sFinset, b ∈ TFinset i := by
      simpa [Finset.mem_biUnion] using Iff.rfl
    rw [h1, h2]
    constructor
    · rintro ⟨i, hi, hbi⟩
      have h_i_in : i ∈ sFinset := by
        have h20 : i ∈ (sFinset : Set α) := by simpa [h_coe_s] using hi
        exact h20
      have h_b_in : b ∈ TFinset i := by
        have h_eq : (TFinset i : Set β) = T i := hTFinset_eq i hi
        have h20 : b ∈ (TFinset i : Set β) := by
          have h21 : b ∈ T i := hbi
          rw [h_eq] at *
          <;> tauto
        exact h20
      exact ⟨i, h_i_in, h_b_in⟩
    · rintro ⟨i, hi, hbi⟩
      have hi' : i ∈ S := by
        have h20 : i ∈ (sFinset : Set α) := hi
        simpa [h_coe_s] using h20
      have h_b_in : b ∈ T i := by
        have h_eq : (TFinset i : Set β) = T i := hTFinset_eq i hi'
        have h20 : b ∈ (TFinset i : Set β) := hbi
        have h21 : b ∈ T i := by
          rw [←h_eq]
          exact h20
        exact h21
      exact ⟨i, hi', h_b_in⟩
  have h_encard_T : ∀ i ∈ S, (T i).encard = ↑(TFinset i).card := by
    intro i hi
    have h6 : (T i) = ↑(TFinset i) := (hTFinset_eq i hi).symm
    rw [h6, Set.encard_coe_eq_coe_finsetCard]
  have h_overlap' : ∀ b ∈ sFinset.biUnion TFinset,
      (sFinset.filter (fun i => b ∈ TFinset i)).card ≤ 3 := by
    intro b hb
    have h7 : b ∈ ⋃ i ∈ S, T i := by rw [h_union] <;> exact hb
    have h8 := (h b h7)
    have h9 : {i ∈ S | b ∈ T i}.Finite := h8.1
    have h10 : {i ∈ S | b ∈ T i}.encard ≤ 3 := h8.2
    have h11 : (sFinset.filter (fun i => b ∈ TFinset i)) = h9.toFinset := by
      ext i
      simp only [Finset.mem_filter]
      have h_iS : i ∈ sFinset ↔ i ∈ S := by
        constructor
        · intro h
          have h20 : i ∈ (sFinset : Set α) := h
          simpa [h_coe_s] using h20
        · intro h
          have h20 : i ∈ (sFinset : Set α) := by
            simpa [h_coe_s] using h
          exact h20
      by_cases h13 : i ∈ sFinset
      · have h14 : i ∈ S := h_iS.mp h13
        have h15 : b ∈ TFinset i ↔ b ∈ T i := by
          have h16 : (TFinset i : Set β) = T i := hTFinset_eq i h14
          exact Set.ext_iff.mp h16 b
        simp [h13, h15, h14]
      · have h14 : i ∉ S := by
          intro h
          exact h13 (h_iS.mpr h)
        simp [h13, h14]
    rw [h11]
    have h13 : {i ∈ S | b ∈ T i}.encard = ↑(h9.toFinset.card) := h9.encard_eq_coe_toFinset_card
    rw [h13] at h10
    exact_mod_cast h10
  have h_main := bounded_overlap_finset sFinset TFinset 3 h_overlap'
  have h13 : ENat.toENNReal (⋃ i ∈ S, T i).encard = ↑((sFinset.biUnion TFinset).card) := by
    rw [h_union, Set.encard_coe_eq_coe_finsetCard] <;> rfl
  have h14 : (∑ᶠ i ∈ S, ENat.toENNReal (T i).encard) =
      ∑ i ∈ sFinset, ENat.toENNReal (T i).encard := by
    apply finsum_mem_eq_sum_of_subset (f := fun i => ENat.toENNReal (T i).encard)
    · intro x hx; rw [h_coe_s] at *; exact hx.1
    · rw [h_coe_s]
  rw [h14, h13]
  have h15 : ∀ i ∈ sFinset, ENat.toENNReal (T i).encard = ↑((TFinset i).card) := by
    intro i hi
    have h16 : i ∈ S := by rw [←h_coe_s] <;> exact hi
    rw [h_encard_T i h16] <;> rfl
  have h16 : ∑ i ∈ sFinset, ENat.toENNReal (T i).encard =
      ∑ i ∈ sFinset, (↑((TFinset i).card) : ENNReal) := by
    apply Finset.sum_congr rfl; intro i hi; exact h15 i hi
  rw [h16]
  have h17 : (∑ i ∈ sFinset, (↑((TFinset i).card) : ENNReal)) ≤
      (3 : ENNReal) * ↑((sFinset.biUnion TFinset).card) := by
    exact_mod_cast h_main
  have h18 : (∑ i ∈ sFinset, (↑((TFinset i).card) : ENNReal)) ≤
      ↑((sFinset.biUnion TFinset).card) * (3 : ENNReal) := by
    have h19 : (3 : ENNReal) * ↑((sFinset.biUnion TFinset).card) =
        ↑((sFinset.biUnion TFinset).card) * (3 : ENNReal) := by ring
    rw [h19] at h17
    exact h17
  exact h18

-- ======================================================================
-- Main result: cardinality lower bound
-- ======================================================================

/-- The union T_y has cardinality at least δ^{-2s}/(3C²). -/
lemma cardinality_lower_bound
    {α : Type*} {δ s C y : ℝ}
    {X : Set ℝ} {T_x : ℝ → Set α}
    {cell : α → Set (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs : 0 < s) (hC : 1 ≤ C)
    (hX_regular : IsDeltaSCSet δ s C (realLineCopy X))
    (hX_upper : ENat.toENNReal X.encard ≤ ENNReal.ofReal (δ ^ (-s)))
    (hcell : ∀ x ∈ X, ∀ a ∈ T_x x, cell a ∈ dyadicCubes 2 δ)
    (hcell_inj : Set.InjOn cell (⋃ x ∈ X, T_x x))
    (hTx_regular : ∀ x ∈ X,
      IsDeltaSCSet δ s C (cellRealization cell (T_x x)))
    (hTx_upper : ∀ x ∈ X,
      ENat.toENNReal (T_x x).encard ≤ ENNReal.ofReal (δ ^ (-s)))
    (hoverlap : ∀ a ∈ ⋃ x ∈ X, T_x x,
      {x ∈ X | a ∈ T_x x}.Finite ∧
      {x ∈ X | a ∈ T_x x}.encard ≤ 3) :
    ENNReal.ofReal (δ ^ (-2 * s) / (3 * C ^ 2)) ≤
      ENat.toENNReal (⋃ x ∈ X, T_x x).encard := by
  let T_y := ⋃ x ∈ X, T_x x
  let c : ENNReal := ENNReal.ofReal (δ ^ (-s) / C)
  have hC_pos : 0 < C := by linarith
  have hX_finite : X.Finite := finite_of_ennreal_encard_bound hX_upper
  have hTx_finite : ∀ x ∈ X, (T_x x).Finite := fun x hx =>
    finite_of_ennreal_encard_bound (hTx_upper x hx)
  have hT_y_finite : T_y.Finite := Set.Finite.biUnion hX_finite hTx_finite
  have h_c_eq : c = ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
    have h_eq : δ ^ (-s) / C = C⁻¹ * δ ^ (-s) := by
      field_simp [hC_pos.ne'] <;> ring
    exact congr_arg ENNReal.ofReal h_eq
  -- Step 1: c ≤ |X| (via covering number ≤ encard)
  have h1 : c ≤ ENat.toENNReal X.encard := by
    have hcov : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy X)) :=
      covering_lower_bound hX_regular
    rw [←h_c_eq] at hcov
    have hle : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy X)) ≤
        ENat.toENNReal (realLineCopy X).encard := covering_number_le_encard hδ
    have h_encard : (realLineCopy X).encard = X.encard := by
      let mkPoint1 : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
        (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun (_ : Fin 1) => x)
      have h_eq1 : realLineCopy X = mkPoint1 '' X := by
        ext p
        simp only [realLineCopy, Set.mem_image, Set.mem_setOf_eq]
        constructor
        · intro hp
          refine ⟨p 0, hp, ?_⟩
          exact PiLp.ext (fun i => by fin_cases i <;> rfl)
        · rintro ⟨x, hx, rfl⟩
          simpa [mkPoint1] using hx
      rw [h_eq1]
      have h_inj : Set.InjOn mkPoint1 X := by
        intro x _ y _ h
        have h' : (mkPoint1 x) 0 = (mkPoint1 y) 0 := by rw [h]
        simpa [mkPoint1] using h'
      exact h_inj.encard_image
    rw [h_encard] at hle
    exact le_trans hcov hle
  -- Step 2: ∀ x ∈ X, c ≤ |T_x x|
  have h2 : ∀ x ∈ X, c ≤ ENat.toENNReal (T_x x).encard := by
    intro x hx
    have hcov : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (cellRealization cell (T_x x))) :=
      covering_lower_bound (hTx_regular x hx)
    rw [←h_c_eq] at hcov
    have heq : dyadicCoveringNumber δ (cellRealization cell (T_x x)) = (T_x x).encard :=
      dyadicCoveringNumber_cellRealization hδ
        (fun a ha => hcell x hx a ha)
        (Set.InjOn.mono (show T_x x ⊆ T_y from fun a ha => Set.mem_iUnion₂.mpr ⟨x, hx, ha⟩) hcell_inj)
    rw [heq] at hcov
    exact hcov
  -- Step 3: Σ |T_x x| ≥ |X| * c
  let Xf := hX_finite.toFinset
  have hXf_coe : (Xf : Set ℝ) = X := hX_finite.coe_toFinset
  have h_finsum_eq : ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard =
      ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard := by
    apply finsum_mem_eq_sum_of_subset (f := fun x => ENat.toENNReal (T_x x).encard)
    · intro x hx; rw [hXf_coe] at *; exact hx.1
    · rw [hXf_coe]
  have h_sum_lower : ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥
      (Xf.card : ENNReal) * c := by
    have h_each : ∀ x ∈ Xf, c ≤ ENat.toENNReal (T_x x).encard := by
      intro x hx
      have h_x_in_X : x ∈ X := by rw [←hXf_coe] <;> exact hx
      exact h2 x h_x_in_X
    have h : ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥ ∑ x ∈ Xf, c :=
      Finset.sum_le_sum h_each
    have h2 : ∑ x ∈ Xf, c = (Xf.card : ENNReal) * c := by
      rw [Finset.sum_const]
      <;> simp [mul_comm]
      <;> ring
    rw [h2] at h
    exact h
  have h_card_eq : (Xf.card : ENNReal) = ENat.toENNReal X.encard := by
    have h : X.encard = ↑Xf.card := by
      rw [←hXf_coe, Set.encard_coe_eq_coe_finsetCard] <;> rfl
    rw [h] <;> norm_cast
  -- Step 4: Σ |T_x x| ≥ c * c
  have h4 : ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard ≥ c * c := by
    rw [h_finsum_eq]
    calc
      ∑ x ∈ Xf, ENat.toENNReal (T_x x).encard ≥ (Xf.card : ENNReal) * c := h_sum_lower
      _ = ENat.toENNReal X.encard * c := by rw [h_card_eq]
      _ ≥ c * c := by gcongr <;> exact h1
  -- Step 5: c * c = ENNReal.ofReal (δ^{-2s} / C^2)
  have h5 : c * c = ENNReal.ofReal (δ ^ (-2 * s) / C ^ 2) := by
    have hpos1 : 0 ≤ δ ^ (-s) / C := by positivity
    have hpos2 : 0 ≤ δ ^ (-2 * s) / C ^ 2 := by positivity
    have h_mul : ENNReal.ofReal (δ ^ (-s) / C) * ENNReal.ofReal (δ ^ (-s) / C) =
        ENNReal.ofReal ((δ ^ (-s) / C) * (δ ^ (-s) / C)) := by
      rw [← ENNReal.ofReal_mul hpos1] <;> rfl
    rw [h_mul]
    have h_eq : (δ ^ (-s) / C) * (δ ^ (-s) / C) = δ ^ (-2 * s) / C ^ 2 := by
      have h_exp : δ ^ (-s) * δ ^ (-s) = δ ^ (-2 * s) := by
        have h_sum : (-s) + (-s) = -2 * s := by ring
        have h : δ ^ (-s) * δ ^ (-s) = δ ^ ((-s) + (-s)) := by
          rw [← Real.rpow_add (by linarith)] <;> ring
        rw [h, h_sum]
      calc (δ ^ (-s) / C) * (δ ^ (-s) / C)
        = (δ ^ (-s) * δ ^ (-s)) / (C * C) := by ring
      _ = δ ^ (-2 * s) / (C * C) := by rw [h_exp]
      _ = δ ^ (-2 * s) / C ^ 2 := by ring
    rw [h_eq]
  -- Step 6: 3 * |T_y| ≥ Σ |T_x x|
  have h6 : ENat.toENNReal T_y.encard * 3 ≥
      ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard :=
    bounded_overlap_set_3 X T_x hX_finite hTx_finite hoverlap
  -- Step 7: |T_y| ≥ c * c / 3
  have h7 : ENat.toENNReal T_y.encard * 3 ≥ c * c := by
    calc ENat.toENNReal T_y.encard * 3
      ≥ ∑ᶠ x ∈ X, ENat.toENNReal (T_x x).encard := h6
    _ ≥ c * c := h4
  have h8 : ENat.toENNReal T_y.encard ≥ (c * c) / 3 := by
    have h9 : ENat.toENNReal T_y.encard * 3 ≥ c * c := h7
    have h10 : (ENat.toENNReal T_y.encard * 3) / 3 ≥ (c * c) / 3 := by gcongr
    have h11 : (ENat.toENNReal T_y.encard * 3) / 3 = ENat.toENNReal T_y.encard := by
      have h12 : (ENat.toENNReal T_y.encard * (3 : ENNReal)) / (3 : ENNReal) = ENat.toENNReal T_y.encard :=
        ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
      exact h12
    rw [h11] at h10
    exact h10
  rw [h5] at h8
  have h_final : (ENNReal.ofReal (δ ^ (-2 * s) / C ^ 2)) / 3 =
      ENNReal.ofReal (δ ^ (-2 * s) / (3 * C ^ 2)) := by
    have hpos : 0 ≤ δ ^ (-2 * s) / C ^ 2 := by positivity
    let x : ℝ := δ ^ (-2 * s) / C ^ 2
    have h_div : ENNReal.ofReal x / (3 : ENNReal) =
        ENNReal.ofReal x * ENNReal.ofReal (1 / 3 : ℝ) := by
      simp [div_eq_mul_inv]
      <;> rfl
    rw [h_div]
    have h_mul : ENNReal.ofReal x * ENNReal.ofReal (1 / 3 : ℝ) =
        ENNReal.ofReal (x * (1 / 3 : ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      <;> rfl
    rw [h_mul]
    have h_eq : x * (1 / 3 : ℝ) = δ ^ (-2 * s) / (3 * C ^ 2) := by
      simp only [x]
      <;> ring
    rw [h_eq]
  rw [h_final] at h8
  exact h8

end

end ProductLikeIncidence
