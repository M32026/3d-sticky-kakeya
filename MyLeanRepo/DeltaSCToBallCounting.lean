module

/-
# IsDeltaSCSet → Ball Counting Bound

Converts a planar `IsDeltaSCSet δ (2s) C P` regularity hypothesis into a
ball-counting bound for a δ-separated representative set S.

## Proof route
1. A ball B(p,r) is covered by 9 dyadic r-cubes (3×3 grid around p's cube).
2. For each r-cube Q, IsDeltaSCSet gives N(P∩Q) ≤ C·N(P)·r^{2s}.
3. For any set A, |S ∩ A| ≤ N(P∩A) because each S point lives in a distinct
   δ-cube (hS_rep uniqueness + equal cardinality hS_card).
4. Sum over 9 cubes: |S ∩ B(p,r)| ≤ 9·C·N(P)·r^{2s} = 9·C·|S|·r^{2s}.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open MeasureTheory ENNReal Finset Set Bornology Classical

namespace robust_projection

/-- Helper: x ∈ Ico (r * ⌊x/r⌋) (r * (⌊x/r⌋ + 1)). -/
lemma floor_cube_mem {r x : ℝ} (hr : 0 < r) :
    x ∈ Set.Ico (r * (⌊x / r⌋ : ℝ)) (r * ((⌊x / r⌋ : ℝ) + 1)) := by
  have h1 : (⌊x / r⌋ : ℝ) ≤ x / r := Int.floor_le (x / r)
  have h2 : x / r < (⌊x / r⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / r)
  constructor
  · calc r * (⌊x / r⌋ : ℝ) ≤ r * (x / r) := by gcongr
    _ = x := by field_simp [hr.ne'] <;> ring
  · calc x = r * (x / r) := by field_simp [hr.ne'] <;> ring
    _ < r * ((⌊x / r⌋ : ℝ) + 1) := by gcongr

/-- Coordinate bound from Euclidean distance: |x i - y i| ≤ dist x y. -/
lemma coord_dist_le (x y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |x i - y i| ≤ dist x y := by
  have h1 : ‖x - y‖ ^ 2 = ∑ j : Fin 2, ((x - y) j)^2 := by exact EuclideanSpace.real_norm_sq_eq (x - y)
  have h3 : ((x - y) i)^2 ≤ ∑ j : Fin 2, ((x - y) j)^2 := by
    apply Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h4 : ((x - y) i)^2 ≤ ‖x - y‖ ^ 2 := by
    have h5 : ‖x - y‖ ^ 2 = ∑ j : Fin 2, ((x - y) j)^2 := h1
    rw [h5]
    exact h3
  let z := x - y
  have h5 : |z i| ^ 2 = (z i)^2 := by rw [sq_abs]
  have h6 : |z i| ^ 2 ≤ ‖z‖ ^ 2 := by rw [h5]; exact h4
  have h7 : 0 ≤ |z i| := abs_nonneg _
  have h8 : 0 ≤ ‖z‖ := norm_nonneg _
  have h9 : |z i| ≤ ‖z‖ := by
    by_contra h10
    have h11 : ‖z‖ < |z i| := by linarith
    have h12 : ‖z‖ ^ 2 < |z i| ^ 2 := by nlinarith
    linarith
  have h10 : z i = x i - y i := by rfl
  have h11 : dist x y = ‖z‖ := by rfl
  have h_goal : |x i - y i| ≤ dist x y := by
    have h12 : |x i - y i| = |z i| := by rw [show z i = x i - y i from rfl]
    rw [h12, h11]
    exact h9
  exact h_goal

/-- Dyadic cubes of the same scale with different indices are disjoint. -/
lemma dyadic_cube_disjoint {d : ℕ} {r : ℝ} (hr : 0 < r) {k1 k2 : Fin d → ℤ} (h : k1 ≠ k2) :
    Disjoint (dyadicCube r k1) (dyadicCube r k2) := by
  have hi : ∃ i, k1 i ≠ k2 i := by
    by_contra h'
    push Not at h'
    have h_eq : k1 = k2 := by funext i; exact h' i
    exact h h_eq
  rcases hi with ⟨i, hne⟩
  simp only [Set.disjoint_left, dyadicCube]
  intro x hx1 hx2
  have h1 : x i ∈ Set.Ico (r * (k1 i : ℝ)) (r * ((k1 i : ℝ) + 1)) := hx1 i
  have h2 : x i ∈ Set.Ico (r * (k2 i : ℝ)) (r * ((k2 i : ℝ) + 1)) := hx2 i
  have h_cases : k1 i < k2 i ∨ k2 i < k1 i := by omega
  cases h_cases with
  | inl h_lt =>
    have h3 : (k1 i : ℝ) + 1 ≤ (k2 i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h_lt
    have h4 : x i < r * ((k1 i : ℝ) + 1) := h1.2
    have h5 : r * (k2 i : ℝ) ≤ x i := h2.1
    have h6 : r * ((k1 i : ℝ) + 1) ≤ r * (k2 i : ℝ) := by gcongr
    linarith
  | inr h_lt =>
    have h3 : (k2 i : ℝ) + 1 ≤ (k1 i : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h_lt
    have h4 : x i < r * ((k2 i : ℝ) + 1) := h2.2
    have h5 : r * (k1 i : ℝ) ≤ x i := h1.1
    have h6 : r * ((k2 i : ℝ) + 1) ≤ r * (k1 i : ℝ) := by gcongr
    linarith

/-- For any set A, the number of S-points in A is bounded by the δ-covering
    number of P ∩ A. -/
lemma s_points_le_covering
    {δ : ℝ} (hδ : 0 < δ)
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (hS_rep : ∀ Q ∈ dyadicCubesMeeting δ P,
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ S ∧ p ∈ Q ∩ P)
    (hS_card : (S.card : ENNReal) = Nplane δ P)
    {A : Set (EuclideanSpace ℝ (Fin 2))} :
    ↑(S.filter (fun q => q ∈ A)).card ≤ Nplane δ (P ∩ A) := by
  -- Finiteness of cube set
  have h_dom_finite : Set.Finite (dyadicCubesMeeting δ P) := by
    have h' : Nplane δ P ≠ ⊤ := by rw [←hS_card]; exact ENNReal.coe_ne_top
    have h'' : (dyadicCubesMeeting δ P).encard ≠ ⊤ := by
      simpa [Nplane, dyadicCoveringNumber] using h'
    by_contra h
    have h_inf : Set.Infinite (dyadicCubesMeeting δ P) := by exact Set.not_finite.mp h
    have h_top : (dyadicCubesMeeting δ P).encard = ⊤ := by exact encard_eq_top_iff.mpr h
    exact h'' h_top
  let dom : Finset (Set (EuclideanSpace ℝ (Fin 2))) := h_dom_finite.toFinset
  have h_dom_eq : (dom : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ P :=
    Set.Finite.coe_toFinset h_dom_finite
  have h_card_dom : dom.card = S.card := by
    have h_eq1 : (dyadicCubesMeeting δ P).encard = ↑(h_dom_finite.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card h_dom_finite
    have h_dom2 : dom = h_dom_finite.toFinset := by rfl
    have h1 : (S.card : ENNReal) = (dom.card : ENNReal) := by
      calc (S.card : ENNReal)
        = Nplane δ P := hS_card
      _ = ENat.toENNReal ((dyadicCubesMeeting δ P).encard) := by rfl
      _ = ENat.toENNReal (↑(h_dom_finite.toFinset.card)) := by rw [h_eq1]
      _ = ENat.toENNReal (↑dom.card) := by rw [h_dom2]
      _ = (dom.card : ENNReal) := by simp
    exact_mod_cast h1.symm
  -- Choose representative for each cube using a total function
  let f : Set (EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2) := fun Q =>
    if hQ : Q ∈ dyadicCubesMeeting δ P then Classical.choose (hS_rep Q hQ) else 0
  have hf_prop : ∀ Q ∈ dyadicCubesMeeting δ P,
      (f Q ∈ S ∧ f Q ∈ Q ∩ P) ∧
      ∀ (y : EuclideanSpace ℝ (Fin 2)), (y ∈ S ∧ y ∈ Q ∩ P) → y = f Q := by
    intro Q hQ
    have h_fQ : f Q = Classical.choose (hS_rep Q hQ) := by
      simp [f, hQ]
    rw [h_fQ]
    exact Classical.choose_spec (hS_rep Q hQ)
  -- f is injective on the cube set (by disjointness of dyadic cubes)
  have hf_inj : Set.InjOn f (dyadicCubesMeeting δ P) := by
    intro Q1 hQ1 Q2 hQ2 h_eq
    have h1 : f Q1 ∈ Q1 := (hf_prop Q1 hQ1).1.2.1
    have h2 : f Q2 ∈ Q2 := (hf_prop Q2 hQ2).1.2.1
    rw [h_eq] at h1
    have h3 : f Q2 ∈ Q1 ∩ Q2 := ⟨h1, h2⟩
    rcases hQ1.1 with ⟨k1, rfl⟩
    rcases hQ2.1 with ⟨k2, rfl⟩
    by_cases h : k1 = k2
    · subst h; rfl
    · exfalso
      have h_disj : Disjoint (dyadicCube δ k1) (dyadicCube δ k2) := dyadic_cube_disjoint hδ h
      have h_empty : (dyadicCube δ k1) ∩ (dyadicCube δ k2) = ∅ :=
        h_disj.inter_eq
      rw [h_empty] at h3
      exact h3
  -- Image of f on dom is a subset of S with same cardinality, hence equals S
  let img : Finset (EuclideanSpace ℝ (Fin 2)) := dom.image f
  have h_img_sub : img ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨Q, hQ, rfl⟩
    have hQ' : Q ∈ dyadicCubesMeeting δ P := by
      simp only [dom, Set.Finite.mem_toFinset] at hQ; exact hQ
    exact (hf_prop Q hQ').1.1
  have hf_inj' : Set.InjOn f (dom : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [h_dom_eq]
    exact hf_inj
  have h_img_card : img.card = dom.card := by
    rw [Finset.card_image_of_injOn hf_inj']
  have h_img_eq_S : img = S := by
    apply Finset.eq_of_subset_of_card_le h_img_sub
    rw [h_img_card, h_card_dom]
  -- Therefore S ⊆ P
  have hS_in_P : ∀ p ∈ S, p ∈ P := by
    intro p hp
    have h_p_in_img : p ∈ img := by rw [h_img_eq_S] <;> exact hp
    rcases Finset.mem_image.mp h_p_in_img with ⟨Q, hQ, hq⟩
    have hQ' : Q ∈ dyadicCubesMeeting δ P := by
      simp only [dom, Set.Finite.mem_toFinset] at hQ; exact hQ
    have h : f Q ∈ Q ∩ P := (hf_prop Q hQ').1.2
    rw [hq] at h; exact h.2
  -- Map each S-point in A to its floor-indexed δ-cube
  let δIndex (x : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ := fun i => ⌊x i / δ⌋
  let δCube (x : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
    dyadicCube δ (δIndex x)
  have h_in_cube : ∀ x, x ∈ δCube x := by intro x i; exact floor_cube_mem hδ
  have h_inj : Set.InjOn δCube (S.filter (fun q => q ∈ A) : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p1 hp1 p2 hp2 h_eq
    have h_p1S : p1 ∈ S := (Finset.mem_filter.mp hp1).1
    have h_p2S : p2 ∈ S := (Finset.mem_filter.mp hp2).1
    have h_p1P : p1 ∈ P := hS_in_P p1 h_p1S
    have h_p2P : p2 ∈ P := hS_in_P p2 h_p2S
    have h1 : p1 ∈ δCube p2 := by
      have h : p1 ∈ δCube p1 := h_in_cube p1
      rw [h_eq] at h; exact h
    have h2 : p2 ∈ δCube p2 := h_in_cube p2
    have h4 : δCube p2 ∈ dyadicCubesMeeting δ P := by
      have h5 : δCube p2 ∈ dyadicCubes 2 δ := ⟨δIndex p2, rfl⟩
      have h6 : (δCube p2 ∩ P).Nonempty := ⟨p2, h2, h_p2P⟩
      exact ⟨h5, h6⟩
    have h_uniq : ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ S ∧ p ∈ δCube p2 ∩ P :=
      hS_rep (δCube p2) h4
    have h5 : p1 ∈ S ∧ p1 ∈ δCube p2 ∩ P := ⟨h_p1S, h1, h_p1P⟩
    have h6 : p2 ∈ S ∧ p2 ∈ δCube p2 ∩ P := ⟨h_p2S, h2, h_p2P⟩
    exact h_uniq.unique h5 h6
  have h_cube_meets : ∀ p ∈ S.filter (fun q => q ∈ A),
      δCube p ∈ dyadicCubesMeeting δ (P ∩ A) := by
    intro p hp
    have h_pS : p ∈ S := (Finset.mem_filter.mp hp).1
    have h_pA : p ∈ A := (Finset.mem_filter.mp hp).2
    have h_pP : p ∈ P := hS_in_P p h_pS
    have h1 : δCube p ∈ dyadicCubes 2 δ := ⟨δIndex p, rfl⟩
    have h2 : (δCube p ∩ (P ∩ A)).Nonempty := ⟨p, h_in_cube p, ⟨h_pP, h_pA⟩⟩
    exact ⟨h1, h2⟩
  -- Finiteness of dyadicCubesMeeting δ (P ∩ A) as subset of dyadicCubesMeeting δ P
  have h_subset : dyadicCubesMeeting δ (P ∩ A) ⊆ dyadicCubesMeeting δ P := by
    intro Q hQ
    have h1 : Q ∈ dyadicCubes 2 δ := hQ.1
    have h2 : (Q ∩ (P ∩ A)).Nonempty := hQ.2
    have h3 : (Q ∩ P).Nonempty := h2.mono (by intro x hx; exact ⟨hx.1, hx.2.1⟩)
    exact ⟨h1, h3⟩
  have h_finite2 : Set.Finite (dyadicCubesMeeting δ (P ∩ A)) :=
    Set.Finite.subset h_dom_finite h_subset
  let SA := S.filter (fun q => q ∈ A)
  let imgFinset : Finset (Set (EuclideanSpace ℝ (Fin 2))) := SA.image δCube
  have h_imgFinset_card : imgFinset.card = SA.card :=
    Finset.card_image_of_injOn h_inj
  let imgSet := δCube '' (SA : Set (EuclideanSpace ℝ (Fin 2)))
  have h_imgFinset_coe : (imgFinset : Set (Set (EuclideanSpace ℝ (Fin 2)))) = imgSet := by
    ext x; simp [imgSet, imgFinset, Finset.mem_image]
  have h_img_sub2 : imgSet ⊆ dyadicCubesMeeting δ (P ∩ A) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_cube_meets x hx
  have h_finite_img : Set.Finite imgSet := by
    rw [←h_imgFinset_coe]; exact Finset.finite_toSet _
  have h_card_img : h_finite_img.toFinset.card = SA.card := by
    have h_eq : h_finite_img.toFinset = imgFinset := by
      ext x
      have h10 : x ∈ h_finite_img.toFinset ↔ x ∈ imgSet := by
        simp [Set.Finite.mem_toFinset]
      have h11 : x ∈ imgFinset ↔ x ∈ imgSet := by
        have h12 : x ∈ (imgFinset : Set _) ↔ x ∈ imgSet := by rw [h_imgFinset_coe]
        simpa using h12
      rw [h10, h11]
    rw [h_eq, h_imgFinset_card]
  have h_main : (S.filter (fun q => q ∈ A)).card ≤ h_finite2.toFinset.card := by
    have h_sub : h_finite_img.toFinset ⊆ h_finite2.toFinset := by
      simpa [Set.Finite.coe_toFinset] using h_img_sub2
    calc (S.filter (fun q => q ∈ A)).card
      = h_finite_img.toFinset.card := h_card_img.symm
    _ ≤ h_finite2.toFinset.card := Finset.card_le_card h_sub
  have h_encard : (dyadicCubesMeeting δ (P ∩ A)).encard = ↑(h_finite2.toFinset.card) := by
    have h1 : (dyadicCubesMeeting δ (P ∩ A)).encard = ↑((dyadicCubesMeeting δ (P ∩ A)).encard.toNat) :=
      h_finite2.encard_eq_coe
    have h2 : (dyadicCubesMeeting δ (P ∩ A)).encard.toNat = h_finite2.toFinset.card := by
      simp [Set.Finite.toFinset, Set.ncard]
      <;> rfl
    rw [h1, h2]
  have h_final : (↑(S.filter (fun q => q ∈ A)).card : ENNReal) ≤
      (dyadicCubesMeeting δ (P ∩ A)).encard := by
    rw [h_encard]
    <;> exact_mod_cast h_main
  simpa [Nplane, dyadicCoveringNumber] using h_final

/-- Convert IsDeltaSCSet regularity to a ball-counting bound for representative set S. -/
lemma delta_sc_set_to_ball_counting
    {δ s C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP_reg : IsDeltaSCSet δ (2 * s) C P)
    (hS_rep : ∀ Q ∈ dyadicCubesMeeting δ P,
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ S ∧ p ∈ Q ∩ P)
    (hS_card : (S.card : ENNReal) = Nplane δ P)
    (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hδ_pos : 0 < δ) (hδ_le_r : δ ≤ r) (hr_le_one : r ≤ 1)
    (hr_dyadic : r ∈ dyadicScales) :
    (S.filter (fun q => dist p q < r)).card ≤
      (9 * C) * (S.card : ℝ) * r ^ (2 * s) := by
  have hδ : 0 < δ := hδ_pos
  have hr_pos : 0 < r := by linarith
  rcases hP_reg with ⟨hP_bdd, hP_nonempty, _, _, hδ_pos', hs_nonneg, _, hC_pos, h_reg_prop⟩
  let k : Fin 2 → ℤ := fun i => ⌊p i / r⌋
  let e : ℤ × ℤ ↪ (Fin 2 → ℤ) :=
    ⟨fun p i => if i = 0 then p.1 else p.2, by
      intro a b h
      have h1 := congr_fun h 0
      have h2 := congr_fun h 1
      simp at h1 h2 <;> exact Prod.ext h1 h2⟩
  let nearIndices : Finset (Fin 2 → ℤ) :=
    ((Finset.Icc (k 0 - 1) (k 0 + 1)).product
      (Finset.Icc (k 1 - 1) (k 1 + 1))).image e
  have h_cardIcc0 : (Finset.Icc (k 0 - 1) (k 0 + 1)).card = 3 := by
    have h_eq : Finset.Icc (k 0 - 1) (k 0 + 1) =
        insert (k 0 - 1) (insert (k 0) ({k 0 + 1} : Finset ℤ)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      <;> omega
    rw [h_eq]
    have h2 : k 0 ∉ ({k 0 + 1} : Finset ℤ) := by simp <;> omega
    have h3 : k 0 - 1 ∉ (insert (k 0) ({k 0 + 1} : Finset ℤ)) := by simp <;> omega
    rw [Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h2] <;> simp
  have h_cardIcc1 : (Finset.Icc (k 1 - 1) (k 1 + 1)).card = 3 := by
    have h_eq : Finset.Icc (k 1 - 1) (k 1 + 1) =
        insert (k 1 - 1) (insert (k 1) ({k 1 + 1} : Finset ℤ)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      <;> omega
    rw [h_eq]
    have h2 : k 1 ∉ ({k 1 + 1} : Finset ℤ) := by simp <;> omega
    have h3 : k 1 - 1 ∉ (insert (k 1) ({k 1 + 1} : Finset ℤ)) := by simp <;> omega
    rw [Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h2] <;> simp
  have h_card9 : nearIndices.card = 9 := by
    dsimp only [nearIndices]
    have h_img : (Finset.image e ((Finset.Icc (k 0 - 1) (k 0 + 1)).product
          (Finset.Icc (k 1 - 1) (k 1 + 1)))).card =
        ((Finset.Icc (k 0 - 1) (k 0 + 1)).product
          (Finset.Icc (k 1 - 1) (k 1 + 1))).card :=
      Finset.card_image_of_injective _ e.inj'
    have h_prod : ((Finset.Icc (k 0 - 1) (k 0 + 1)).product
          (Finset.Icc (k 1 - 1) (k 1 + 1))).card = 9 := by
      have h_card_prod : ((Finset.Icc (k 0 - 1) (k 0 + 1)).product
            (Finset.Icc (k 1 - 1) (k 1 + 1))).card =
          (Finset.Icc (k 0 - 1) (k 0 + 1)).card * (Finset.Icc (k 1 - 1) (k 1 + 1)).card :=
        Finset.card_product _ _
      rw [h_card_prod, h_cardIcc0, h_cardIcc1] <;> norm_num
    rw [h_img, h_prod]
  -- Ball covering: B(p,r) ⊆ union of 9 r-cubes
  have h_cover : ∀ (q : EuclideanSpace ℝ (Fin 2)), dist p q < r →
      q ∈ ⋃ j ∈ nearIndices, dyadicCube r j := by
    intro q hq
    have h_coord : ∀ i : Fin 2, |q i - p i| < r := by
      intro i
      have h1 : |q i - p i| ≤ dist p q := by
        have h2 := coord_dist_le q p i
        rw [dist_comm] at h2
        exact h2
      exact h1.trans_lt hq
    have h_p_in_cube : ∀ i, p i ∈ Set.Ico (r * (k i : ℝ)) (r * ((k i : ℝ) + 1)) := by
      intro i; exact floor_cube_mem hr_pos
    have h_index_range : ∀ i : Fin 2,
        k i - 1 ≤ ⌊q i / r⌋ ∧ ⌊q i / r⌋ ≤ k i + 1 := by
      intro i
      have h1 : |q i - p i| < r := h_coord i
      have h2 : p i ≥ r * (k i : ℝ) := (h_p_in_cube i).1
      have h3 : p i < r * ((k i : ℝ) + 1) := (h_p_in_cube i).2
      have h4 : q i / r > (k i : ℝ) - 1 := by
        have h5 : q i > p i - r := by linarith [abs_lt.mp h1]
        calc q i / r
          > (p i - r) / r := by gcongr
        _ = p i / r - 1 := by field_simp [hr_pos.ne'] <;> ring
        _ ≥ (k i : ℝ) - 1 := by
          have h6 : p i / r ≥ (k i : ℝ) := by
            calc p i / r ≥ (r * (k i : ℝ)) / r := by gcongr
              _ = (k i : ℝ) := by field_simp [hr_pos.ne'] <;> ring
          linarith
      have h5 : q i / r < (k i : ℝ) + 2 := by
        have h6 : q i < p i + r := by linarith [abs_lt.mp h1]
        calc q i / r
          < (p i + r) / r := by gcongr
        _ = p i / r + 1 := by field_simp [hr_pos.ne'] <;> ring
        _ < (k i : ℝ) + 2 := by
          have h7 : p i / r < (k i : ℝ) + 1 := by
            calc p i / r < (r * ((k i : ℝ) + 1)) / r := by gcongr
              _ = (k i : ℝ) + 1 := by field_simp [hr_pos.ne'] <;> ring
          linarith
      have h_floor_le : (⌊q i / r⌋ : ℝ) ≤ q i / r := Int.floor_le (q i / r)
      have h_floor_gt : q i / r < (⌊q i / r⌋ : ℝ) + 1 := Int.lt_floor_add_one (q i / r)
      constructor
      · by_contra h
        have h' : ⌊q i / r⌋ ≤ k i - 2 := by omega
        have h'' : (⌊q i / r⌋ : ℝ) ≤ (k i : ℝ) - 2 := by exact_mod_cast h'
        linarith
      · by_contra h
        have h' : ⌊q i / r⌋ ≥ k i + 2 := by omega
        have h'' : (k i : ℝ) + 2 ≤ (⌊q i / r⌋ : ℝ) := by exact_mod_cast h'
        linarith
    let j : Fin 2 → ℤ := fun i => ⌊q i / r⌋
    have h_j_in : j ∈ nearIndices := by
      have h0 : j 0 ∈ Finset.Icc (k 0 - 1) (k 0 + 1) := by
        simp only [Finset.mem_Icc]; exact h_index_range 0
      have h1 : j 1 ∈ Finset.Icc (k 1 - 1) (k 1 + 1) := by
        simp only [Finset.mem_Icc]; exact h_index_range 1
      have h2 : (j 0, j 1) ∈ (Finset.Icc (k 0 - 1) (k 0 + 1)).product
          (Finset.Icc (k 1 - 1) (k 1 + 1)) := by
        exact Finset.mem_product.mpr ⟨h0, h1⟩
      have h3 : e (j 0, j 1) = j := by
        funext i; fin_cases i <;> simp [e] <;> tauto
      rw [←h3]
      exact Finset.mem_image.mpr ⟨(j 0, j 1), h2, rfl⟩
    have h_q_in : q ∈ dyadicCube r j := by
      intro i; exact floor_cube_mem hr_pos
    exact Set.mem_iUnion₂.mpr ⟨j, h_j_in, h_q_in⟩
  -- For each r-cube Q in nearIndices, bound S-points in Q
  let bound := ENNReal.ofReal C * Nplane δ P * ENNReal.ofReal (r ^ (2 * s))
  have h_per_cube : ∀ j ∈ nearIndices,
      (↑(S.filter (fun q => q ∈ dyadicCube r j)).card : ENNReal) ≤ bound := by
    intro j _
    have hQ : dyadicCube r j ∈ dyadicCubes 2 r := ⟨j, rfl⟩
    have h_bound : Nplane δ (P ∩ dyadicCube r j) ≤ bound :=
      h_reg_prop hr_dyadic hQ hδ_le_r hr_le_one
    have h_S_le : (↑(S.filter (fun q => q ∈ dyadicCube r j)).card : ENNReal) ≤
        Nplane δ (P ∩ dyadicCube r j) :=
      s_points_le_covering hδ hS_rep hS_card
    exact le_trans h_S_le h_bound
  let S_ball := S.filter (fun q => dist p q < r)
  let S_cubes : Finset (EuclideanSpace ℝ (Fin 2)) :=
    nearIndices.biUnion (fun j => S.filter (fun q => q ∈ dyadicCube r j))
  have h_sub : S_ball ⊆ S_cubes := by
    intro q hq
    have h1 : q ∈ S := (Finset.mem_filter.mp hq).1
    have h2 : dist p q < r := (Finset.mem_filter.mp hq).2
    have h3 : q ∈ ⋃ j ∈ nearIndices, dyadicCube r j := h_cover q h2
    rcases Set.mem_iUnion₂.mp h3 with ⟨j, hj, hqj⟩
    have h4 : q ∈ S.filter (fun q => q ∈ dyadicCube r j) :=
      Finset.mem_filter.mpr ⟨h1, hqj⟩
    exact Finset.mem_biUnion.mpr ⟨j, hj, h4⟩
  have h_sum : S_cubes.card ≤ ∑ j ∈ nearIndices,
      (S.filter (fun q => q ∈ dyadicCube r j)).card := by
    exact Finset.card_biUnion_le
  have h_ennreal_sum : (↑(∑ j ∈ nearIndices,
      (S.filter (fun q => q ∈ dyadicCube r j)).card) : ENNReal) ≤
      (nearIndices.card : ENNReal) * bound := by
    have h_cast : (↑(∑ j ∈ nearIndices, (S.filter (fun q => q ∈ dyadicCube r j)).card) : ENNReal) =
        ∑ j ∈ nearIndices, (↑(S.filter (fun q => q ∈ dyadicCube r j)).card : ENNReal) := by
      simp [Nat.cast_sum]
    rw [h_cast]
    calc ∑ j ∈ nearIndices, (↑(S.filter (fun q => q ∈ dyadicCube r j)).card : ENNReal)
      ≤ ∑ j ∈ nearIndices, bound := Finset.sum_le_sum h_per_cube
    _ = (nearIndices.card : ENNReal) * bound := by
        rw [Finset.sum_const] <;> ring
  have h9 : (nearIndices.card : ENNReal) = 9 := by
    rw [h_card9] <;> norm_num
  have h_final_ennreal : (↑S_ball.card : ENNReal) ≤
      (9 : ENNReal) * bound := by
    have h1 : (↑S_ball.card : ENNReal) ≤ (↑S_cubes.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h_sub
    have h2 : (↑S_cubes.card : ENNReal) ≤
        (↑(∑ j ∈ nearIndices, (S.filter (fun q => q ∈ dyadicCube r j)).card) : ENNReal) := by
      exact_mod_cast h_sum
    calc (↑S_ball.card : ENNReal)
      ≤ (↑S_cubes.card : ENNReal) := h1
    _ ≤ (↑(∑ j ∈ nearIndices, (S.filter (fun q => q ∈ dyadicCube r j)).card) : ENNReal) := h2
    _ ≤ (nearIndices.card : ENNReal) * bound := h_ennreal_sum
    _ = (9 : ENNReal) * bound := by rw [h9] <;> ring
  have h_expand : (9 : ENNReal) * bound =
      (9 : ENNReal) * ENNReal.ofReal C * Nplane δ P * ENNReal.ofReal (r ^ (2 * s)) := by
    simp [bound] <;> ring
  have h_final_ennreal2 : (↑S_ball.card : ENNReal) ≤
      (9 : ENNReal) * ENNReal.ofReal C * Nplane δ P * ENNReal.ofReal (r ^ (2 * s)) := by
    rw [←h_expand]
    exact h_final_ennreal
  rw [←hS_card] at h_final_ennreal2
  have h_ne_top : (9 : ENNReal) * ENNReal.ofReal C * (↑S.card : ENNReal) *
      ENNReal.ofReal (r ^ (2 * s)) ≠ ⊤ := by
    have h1 : (9 : ENNReal) ≠ ⊤ := by simp
    have h2 : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    have h3 : (↑S.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h4 : ENNReal.ofReal (r ^ (2 * s)) ≠ ⊤ := ENNReal.ofReal_ne_top
    simpa [mul_assoc] using ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h2) h3) h4
  have h9' : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by simp
  have h_coe : (↑S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by simp
  have h_rhs_eq : (9 : ENNReal) * ENNReal.ofReal C * (↑S.card : ENNReal) *
      ENNReal.ofReal (r ^ (2 * s)) =
      ENNReal.ofReal ((9 : ℝ) * C * (S.card : ℝ) * r ^ (2 * s)) := by
    rw [h9', h_coe]
    have h_posC : 0 ≤ C := hC_pos.le
    have h_posr : 0 ≤ r ^ (2 * s) := by positivity
    have h_pos9 : 0 ≤ (9 : ℝ) := by norm_num
    have h_posC : 0 ≤ C := hC_pos.le
    have h_posS : 0 ≤ (S.card : ℝ) := by positivity
    have h_posr : 0 ≤ r ^ (2 * s) := by positivity
    have h1 : ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((9 : ℝ) * C) := by
      have h : ENNReal.ofReal ((9 : ℝ) * C) = ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal C := by exact ofReal_mul h_pos9
      exact h.symm
    have h2 : ENNReal.ofReal ((9 : ℝ) * C) * ENNReal.ofReal (S.card : ℝ) =
        ENNReal.ofReal (((9 : ℝ) * C) * (S.card : ℝ)) := by
      have h : ENNReal.ofReal (((9 : ℝ) * C) * (S.card : ℝ)) =
          ENNReal.ofReal ((9 : ℝ) * C) * ENNReal.ofReal (S.card : ℝ) := by exact ofReal_mul' h_posS
      exact h.symm
    have h3 : ENNReal.ofReal (((9 : ℝ) * C) * (S.card : ℝ)) * ENNReal.ofReal (r ^ (2 * s)) =
        ENNReal.ofReal ((((9 : ℝ) * C) * (S.card : ℝ)) * r ^ (2 * s)) := by
      have h : ENNReal.ofReal ((((9 : ℝ) * C) * (S.card : ℝ)) * r ^ (2 * s)) =
          ENNReal.ofReal (((9 : ℝ) * C) * (S.card : ℝ)) * ENNReal.ofReal (r ^ (2 * s)) := by (expose_names; exact ofReal_mul' h_posr_1)
      exact h.symm
    calc ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal C * ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (r ^ (2 * s))
      = (ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal C) * ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (r ^ (2 * s)) := by ring
    _ = ENNReal.ofReal ((9 : ℝ) * C) * ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (r ^ (2 * s)) := by rw [h1]
    _ = (ENNReal.ofReal ((9 : ℝ) * C) * ENNReal.ofReal (S.card : ℝ)) * ENNReal.ofReal (r ^ (2 * s)) := by ring
    _ = ENNReal.ofReal (((9 : ℝ) * C) * (S.card : ℝ)) * ENNReal.ofReal (r ^ (2 * s)) := by rw [h2]
    _ = ENNReal.ofReal ((((9 : ℝ) * C) * (S.card : ℝ)) * r ^ (2 * s)) := by rw [h3]
    _ = ENNReal.ofReal ((9 : ℝ) * C * (S.card : ℝ) * r ^ (2 * s)) := by rw [show (((9 : ℝ) * C) * (S.card : ℝ)) * r ^ (2 * s) = (9 : ℝ) * C * (S.card : ℝ) * r ^ (2 * s) by ring]
  rw [h_rhs_eq] at h_final_ennreal2
  have h_cast : (↑S_ball.card : ENNReal) = ENNReal.ofReal (S_ball.card : ℝ) := by simp
  rw [h_cast] at h_final_ennreal2
  have h_pos2 : 0 ≤ (S_ball.card : ℝ) := by positivity
  have h_pos3 : 0 ≤ (9 : ℝ) * C * (S.card : ℝ) * r ^ (2 * s) := by positivity
  have h_iff : ENNReal.ofReal (S_ball.card : ℝ) ≤ ENNReal.ofReal ((9 : ℝ) * C * (S.card : ℝ) * r ^ (2 * s)) ↔
      (S_ball.card : ℝ) ≤ (9 : ℝ) * C * (S.card : ℝ) * r ^ (2 * s) := by
    exact ofReal_le_ofReal_iff h_pos3
  exact h_iff.mp h_final_ennreal2

end robust_projection
