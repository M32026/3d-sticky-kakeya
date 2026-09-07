import MyLeanRepo.Kakeya.CV.ShapeSpace
import MyLeanRepo.Kakeya.CV.GraphColouring
import Mathlib.Tactic

/-!
# Shape net: maximal separated set of ellipsoid shapes

A shape net is a maximal α-separated set of shapes.  We prove its existence
by Zorn's lemma, its covering property, and that its conflict graph
(where conflict = α²-closeness) has bounded degree.  A bounded-degree graph
admits a finite greedy colouring, which is the colouring needed for
Carbery--Valdimarsson Lemma 8.
-/

noncomputable section

open Kakeya.CV
open Kakeya.CV.ShapeSpace

namespace Kakeya.CV.ShapeNet

/-- A set of shapes is α-separated if distinct elements are not α-close. -/
def Separated (α : ℝ) (S : Set (Point 3 ≃ₗ[ℝ] Point 3)) : Prop :=
  ∀ A₁ ∈ S, ∀ A₂ ∈ S, A₁ ≠ A₂ → ¬ ShapeClose α A₁ A₂

/-- Existence of a maximal α-separated set by Zorn's lemma. -/
lemma exists_maximal_separated_set (α : ℝ) :
    ∃ (S : Set (Point 3 ≃ₗ[ℝ] Point 3)),
      Separated α S ∧
      ∀ (T : Set (Point 3 ≃ₗ[ℝ] Point 3)), Separated α T → S ⊆ T → S = T := by
  let P : Set (Set (Point 3 ≃ₗ[ℝ] Point 3)) := {S | Separated α S}
  have h1 : ∀ (c : Set (Set (Point 3 ≃ₗ[ℝ] Point 3))),
      c ⊆ P → IsChain (· ⊆ ·) c → ∃ (ub : Set (Point 3 ≃ₗ[ℝ] Point 3)), ub ∈ P ∧ ∀ x ∈ c, x ⊆ ub := by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun x hx => Set.subset_sUnion_of_mem hx⟩
    intro A1 hA1 A2 hA2 hne
    rcases Set.mem_sUnion.mp hA1 with ⟨S1, hS1c, hA1S1⟩
    rcases Set.mem_sUnion.mp hA2 with ⟨S2, hS2c, hA2S2⟩
    have hS1P : Separated α S1 := hc hS1c
    have hS2P : Separated α S2 := hc hS2c
    by_cases h : S1 = S2
    · rw [h] at hA1S1; exact hS2P A1 hA1S1 A2 hA2S2 hne
    · have h_chain : S1 ⊆ S2 ∨ S2 ⊆ S1 := hchain hS1c hS2c h
      cases h_chain with
      | inl hsub => exact hS2P A1 (hsub hA1S1) A2 hA2S2 hne
      | inr hsub => exact hS1P A1 hA1S1 A2 (hsub hA2S2) hne
  have h_zorn := zorn_subset P h1
  rcases h_zorn with ⟨S, hS_in_P, hS_max⟩
  have hSP : Separated α S := hS_in_P
  have hSmax : ∀ (T : Set (Point 3 ≃ₗ[ℝ] Point 3)), Separated α T → S ⊆ T → S = T := by
    intro T hT hST
    have h : T ⊆ S := hS_max hT hST
    exact Set.Subset.antisymm hST h
  exact ⟨S, hSP, hSmax⟩

/-- Maximal α-separated set of shapes. -/
noncomputable def shapeNet (α : ℝ) : Set (Point 3 ≃ₗ[ℝ] Point 3) :=
  Classical.choose (exists_maximal_separated_set α)

/-- shapeNet is α-separated. -/
lemma shapeNet_separated (α : ℝ) : Separated α (shapeNet α) :=
  (Classical.choose_spec (exists_maximal_separated_set α)).1

/-- shapeNet is maximal. -/
lemma shapeNet_maximal (α : ℝ) (T : Set (Point 3 ≃ₗ[ℝ] Point 3))
    (hT : Separated α T) (h : shapeNet α ⊆ T) : shapeNet α = T :=
  (Classical.choose_spec (exists_maximal_separated_set α)).2 T hT h

/-- Covering property: every shape is α-close to some element of shapeNet. -/
lemma shapeNet_covering (α : ℝ) (hα : 1 < α) (A : Point 3 ≃ₗ[ℝ] Point 3) :
    ∃ (A' : Point 3 ≃ₗ[ℝ] Point 3), A' ∈ shapeNet α ∧ ShapeClose α A A' := by
  by_cases hA : A ∈ shapeNet α
  · exact ⟨A, hA, shapeClose_refl (by linarith)⟩
  · by_contra h
    have h' : ∀ (X : Point 3 ≃ₗ[ℝ] Point 3), X ∈ shapeNet α → ¬ ShapeClose α A X := by
      intro X hX
      intro hsc
      exact h ⟨X, hX, hsc⟩
    let T := insert A (shapeNet α)
    have hT_sep : Separated α T := by
      intro A1 hA1 A2 hA2 hne
      simp only [T, Set.mem_insert_iff] at hA1 hA2
      rcases hA1 with (rfl | hA1')
      · rcases hA2 with (rfl | hA2')
        · contradiction
        · exact h' A2 hA2'
      · rcases hA2 with (rfl | hA2')
        · intro hsc
          exact h' A1 hA1' (shapeClose_symm.mpr hsc)
        · exact shapeNet_separated α A1 hA1' A2 hA2' hne
    have hST : shapeNet α ⊆ T := Set.subset_insert A (shapeNet α)
    have h_eq : shapeNet α = T := shapeNet_maximal α T hT_sep hST
    have h_contra : A ∈ shapeNet α := by
      rw [h_eq] <;> exact Set.mem_insert A (shapeNet α)
    exact hA h_contra

/-- Conflict relation: two shapes conflict if they are α²-close. -/
def shapeConflict (α : ℝ) (A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3) : Prop :=
  ShapeClose (α ^ 2) A₁ A₂

lemma shapeConflict_symm (α : ℝ) (A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3) :
    shapeConflict α A₁ A₂ ↔ shapeConflict α A₂ A₁ := by
  simp [shapeConflict, shapeClose_symm]

/-- Conflict neighborhood of A₀ in shapeNet. -/
def conflictNbhd (α : ℝ) (A₀ : Point 3 ≃ₗ[ℝ] Point 3) : Set (Point 3 ≃ₗ[ℝ] Point 3) :=
  {A₂ ∈ shapeNet α | shapeConflict α A₀ A₂}

/-- Bounded degree of conflict graph on shapeNet.
Uses `packing_bound_general` with `C := α^2`. -/
lemma shapeNet_boundedDegree (α : ℝ) (hα : 1 < α) :
    ∃ (D : ℕ), ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhd α A₀) ∧ (conflictNbhd α A₀).ncard ≤ D := by
  have hα2_pos : 0 < (α ^ 2 : ℝ) := by positivity
  rcases packing_bound_general (C := α ^ 2) (α := α) hα2_pos hα with ⟨D, hD⟩
  refine ⟨D, fun A₀ hA₀ => ?_⟩
  let N := conflictNbhd α A₀
  let f : (Point 3 ≃ₗ[ℝ] Point 3) → (Point 3 ≃ₗ[ℝ] Point 3) :=
    fun A₂ => A₀.symm.trans A₂
  let S' := f '' N
  have h1 : ∀ B ∈ S', ShapeClose (α ^ 2) (1 : Point 3 ≃ₗ[ℝ] Point 3) B := by
    rintro B ⟨A₂, hA₂, rfl⟩
    have h_conf : ShapeClose (α ^ 2) A₀ A₂ := hA₂.2
    have h_close1 : ShapeClose (α ^ 2) (A₀.symm.trans A₀) (A₀.symm.trans A₂) :=
      shapeClose_mul_left (A₀ := A₀.symm) (A₁ := A₀) (A₂ := A₂) h_conf
    have h_id : A₀.symm.trans A₀ = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A₀.symm_trans_self
    rw [h_id] at h_close1
    exact h_close1
  have h2 : ∀ B₁ ∈ S', ∀ B₂ ∈ S', B₁ ≠ B₂ → ¬ ShapeClose α B₁ B₂ := by
    rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    have hA1' : A₁ ∈ shapeNet α := hA₁.1
    have hA2' : A₂ ∈ shapeNet α := hA₂.1
    have hne' : A₁ ≠ A₂ := by
      intro h; rw [h] at hne; exact hne rfl
    have h_sep : ¬ ShapeClose α A₁ A₂ := shapeNet_separated α A₁ hA1' A₂ hA2' hne'
    intro h
    have h_mul1 : ShapeClose α (A₀.trans (f A₁)) (A₀.trans (f A₂)) :=
      shapeClose_mul_left (A₀ := A₀) (A₁ := f A₁) (A₂ := f A₂) h
    have h_eq1 : A₀.trans (f A₁) = A₁ := by
      ext x; simp [f, LinearEquiv.trans_apply]
    have h_eq2 : A₀.trans (f A₂) = A₂ := by
      ext x; simp [f, LinearEquiv.trans_apply]
    rw [h_eq1, h_eq2] at h_mul1
    exact h_sep h_mul1
  have h_fin : Set.Finite S' ∧ S'.ncard ≤ D := hD S' h1 h2
  have h_inj : Set.InjOn f N := by
    intro A₂ _ A₃ _ h
    apply LinearEquiv.ext
    intro y
    have h_surj : ∃ x, A₀.symm x = y := ⟨A₀ y, by simp⟩
    rcases h_surj with ⟨x, hx⟩
    have h6 : (f A₂) x = (f A₃) x := by rw [h]
    have h7 : A₂ (A₀.symm x) = A₃ (A₀.symm x) := by
      simpa [f, LinearEquiv.trans_apply] using h6
    rw [hx] at h7
    exact h7
  have hN_fin : Set.Finite N := h_fin.1.of_injOn (Set.mapsTo_image f N) h_inj
  have h_eq : S'.ncard = N.ncard := (Set.ncard_image_iff hN_fin).mpr h_inj
  have hN_card : N.ncard ≤ D := by
    rw [←h_eq]
    exact h_fin.2
  exact ⟨hN_fin, hN_card⟩

/-- Graph conflict relation: restricted to shapeNet. -/
def graphConflict (α : ℝ) (x y : Point 3 ≃ₗ[ℝ] Point 3) : Prop :=
  x ∈ shapeNet α ∧ y ∈ shapeNet α ∧ shapeConflict α x y

lemma graphConflict_symm (α : ℝ) (x y : Point 3 ≃ₗ[ℝ] Point 3) :
    graphConflict α x y → graphConflict α y x := by
  rintro ⟨hx, hy, h⟩
  exact ⟨hy, hx, (shapeConflict_symm α x y).mp h⟩

/-- Existence of finite neighbourhood finsets for the conflict graph. -/
lemma shapeNet_degreeFinset (α : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhd α A₀) ∧ (conflictNbhd α A₀).ncard ≤ D)
    (x : Point 3 ≃ₗ[ℝ] Point 3) :
    ∃ (Nx : Finset (Point 3 ≃ₗ[ℝ] Point 3)),
      (∀ y, y ∈ Nx ↔ graphConflict α x y) ∧ Nx.card ≤ D := by
  classical
  by_cases hx : x ∈ shapeNet α
  · let N := conflictNbhd α x
    have hN_fin : Set.Finite N := (hD x hx).1
    let Nx : Finset (Point 3 ≃ₗ[ℝ] Point 3) := hN_fin.toFinset
    have h2 : ∀ y, y ∈ Nx ↔ graphConflict α x y := by
      intro y
      have h1 : y ∈ Nx ↔ y ∈ N := by
        simp [Nx, Set.Finite.mem_toFinset]
      rw [h1]
      simp only [N, conflictNbhd, Set.mem_setOf_eq, graphConflict]
      <;> exact ⟨fun h => ⟨hx, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
    have h3 : Nx.card ≤ D := by
      have h4 : N.ncard = Nx.card := Set.ncard_eq_toFinset_card N hN_fin
      have h5 : Nx.card = N.ncard := h4.symm
      rw [h5]; exact (hD x hx).2
    exact ⟨Nx, h2, h3⟩
  · exact ⟨∅, by simp [graphConflict, hx], by simp⟩

/-- Proper colouring of shapeNet conflict graph with D+1 colours. -/
noncomputable def shapeColour (α : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhd α A₀) ∧ (conflictNbhd α A₀).ncard ≤ D) :
    (Point 3 ≃ₗ[ℝ] Point 3) → Fin (D + 1) := by
  classical
  exact Classical.choose <|
    bounded_degree_colouring (graphConflict α) D
      (shapeNet_degreeFinset α D hD)
      (graphConflict_symm α)

/-- The shape colouring is a proper colouring of the conflict graph. -/
lemma shapeColour_isProper (α : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhd α A₀) ∧ (conflictNbhd α A₀).ncard ≤ D) :
    ∀ (x y : Point 3 ≃ₗ[ℝ] Point 3),
      graphConflict α x y → x ≠ y → shapeColour α D hD x ≠ shapeColour α D hD y := by
  classical
  exact Classical.choose_spec <|
    bounded_degree_colouring (graphConflict α) D
      (shapeNet_degreeFinset α D hD)
      (graphConflict_symm α)

/-- Same colour + both α-close to the same shape → equal. -/
lemma shapeColour_separation (α : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhd α A₀) ∧ (conflictNbhd α A₀).ncard ≤ D)
    {A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3}
    (h₁ : A₁ ∈ shapeNet α) (h₂ : A₂ ∈ shapeNet α)
    (hcol : shapeColour α D hD A₁ = shapeColour α D hD A₂)
    {A_K : Point 3 ≃ₗ[ℝ] Point 3}
    (hK1 : ShapeClose α A_K A₁) (hK2 : ShapeClose α A_K A₂) :
    A₁ = A₂ := by
  by_cases hne : A₁ = A₂
  · exact hne
  · have h1' : ShapeClose α A₁ A_K := shapeClose_symm.mp hK1
    have h_conf : ShapeClose (α * α) A₁ A₂ := shapeClose_trans h1' hK2
    have h_conf2 : ShapeClose (α ^ 2) A₁ A₂ := by
      have hpow : α * α = α ^ 2 := by ring
      rw [hpow] at h_conf
      exact h_conf
    have h_sc : shapeConflict α A₁ A₂ := h_conf2
    have h_gc : graphConflict α A₁ A₂ := ⟨h₁, h₂, h_sc⟩
    have h_proper : shapeColour α D hD A₁ ≠ shapeColour α D hD A₂ :=
      shapeColour_isProper α D hD A₁ A₂ h_gc hne
    exact False.elim (h_proper hcol)

/-- Monotonicity of ShapeClose in the bound parameter. -/
lemma shapeClose_mono {β γ : ℝ} (h : β ≤ γ) {A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3}
    (hsc : ShapeClose β A₁ A₂) : ShapeClose γ A₁ A₂ := by
  have h1 : ‖clm (A₁.symm.trans A₂)‖ ≤ β := hsc.1
  have h2 : ‖clm (A₂.symm.trans A₁)‖ ≤ β := hsc.2
  exact ⟨by linarith, by linarith⟩

/-- Generalized conflict relation: two shapes conflict if they are γ-close. -/
def shapeConflictGen (γ : ℝ) (A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3) : Prop :=
  ShapeClose γ A₁ A₂

/-- Generalized conflict neighborhood of A₀ in shapeNet. -/
def conflictNbhdGen (α γ : ℝ) (A₀ : Point 3 ≃ₗ[ℝ] Point 3) :
    Set (Point 3 ≃ₗ[ℝ] Point 3) :=
  {A₂ ∈ shapeNet α | shapeConflictGen γ A₀ A₂}

/-- Generalized graph conflict relation: restricted to shapeNet. -/
def graphConflictGen (α γ : ℝ) (x y : Point 3 ≃ₗ[ℝ] Point 3) : Prop :=
  x ∈ shapeNet α ∧ y ∈ shapeNet α ∧ shapeConflictGen γ x y

lemma graphConflictGen_symm (α γ : ℝ) (x y : Point 3 ≃ₗ[ℝ] Point 3) :
    graphConflictGen α γ x y → graphConflictGen α γ y x := by
  rintro ⟨hx, hy, h⟩
  exact ⟨hy, hx, shapeClose_symm.mp h⟩

/-- Bounded degree for a custom conflict parameter γ ≥ α.
Uses `packing_bound_general` with `C := γ`. -/
lemma shapeNet_boundedDegree_gen (α γ : ℝ) (hα : 1 < α) (hγ : 0 < γ) (hge : α ≤ γ) :
    ∃ (D : ℕ), ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhdGen α γ A₀) ∧ (conflictNbhdGen α γ A₀).ncard ≤ D := by
  rcases packing_bound_general (C := γ) (α := α) hγ hα with ⟨D, hD⟩
  refine ⟨D, fun A₀ hA₀ => ?_⟩
  let N := conflictNbhdGen α γ A₀
  let f : (Point 3 ≃ₗ[ℝ] Point 3) → (Point 3 ≃ₗ[ℝ] Point 3) :=
    fun A₂ => A₀.symm.trans A₂
  let S' := f '' N
  have h1 : ∀ B ∈ S', ShapeClose γ (1 : Point 3 ≃ₗ[ℝ] Point 3) B := by
    rintro B ⟨A₂, hA₂, rfl⟩
    have h_conf : ShapeClose γ A₀ A₂ := hA₂.2
    have h_close1 : ShapeClose γ (A₀.symm.trans A₀) (A₀.symm.trans A₂) :=
      shapeClose_mul_left (A₀ := A₀.symm) (A₁ := A₀) (A₂ := A₂) h_conf
    have h_id : A₀.symm.trans A₀ = (1 : Point 3 ≃ₗ[ℝ] Point 3) := A₀.symm_trans_self
    rw [h_id] at h_close1
    exact h_close1
  have h2 : ∀ B₁ ∈ S', ∀ B₂ ∈ S', B₁ ≠ B₂ → ¬ ShapeClose α B₁ B₂ := by
    rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ hne
    have hA1' : A₁ ∈ shapeNet α := hA₁.1
    have hA2' : A₂ ∈ shapeNet α := hA₂.1
    have hne' : A₁ ≠ A₂ := by
      intro h; rw [h] at hne; exact hne rfl
    have h_sep : ¬ ShapeClose α A₁ A₂ := shapeNet_separated α A₁ hA1' A₂ hA2' hne'
    intro h
    have h_mul1 : ShapeClose α (A₀.trans (f A₁)) (A₀.trans (f A₂)) :=
      shapeClose_mul_left (A₀ := A₀) (A₁ := f A₁) (A₂ := f A₂) h
    have h_eq1 : A₀.trans (f A₁) = A₁ := by
      ext x; simp [f, LinearEquiv.trans_apply]
    have h_eq2 : A₀.trans (f A₂) = A₂ := by
      ext x; simp [f, LinearEquiv.trans_apply]
    rw [h_eq1, h_eq2] at h_mul1
    exact h_sep h_mul1
  have h_fin : Set.Finite S' ∧ S'.ncard ≤ D := hD S' h1 h2
  have h_inj : Set.InjOn f N := by
    intro A₂ _ A₃ _ h
    apply LinearEquiv.ext
    intro y
    have h_surj : ∃ x, A₀.symm x = y := ⟨A₀ y, by simp⟩
    rcases h_surj with ⟨x, hx⟩
    have h6 : (f A₂) x = (f A₃) x := by rw [h]
    have h7 : A₂ (A₀.symm x) = A₃ (A₀.symm x) := by
      simpa [f, LinearEquiv.trans_apply] using h6
    rw [hx] at h7
    exact h7
  have hN_fin : Set.Finite N := h_fin.1.of_injOn (Set.mapsTo_image f N) h_inj
  have h_eq : S'.ncard = N.ncard := (Set.ncard_image_iff hN_fin).mpr h_inj
  have hN_card : N.ncard ≤ D := by
    rw [←h_eq]
    exact h_fin.2
  exact ⟨hN_fin, hN_card⟩

/-- Existence of finite neighbourhood finsets for generalized conflict graph. -/
lemma shapeNet_degreeFinset_gen (α γ : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhdGen α γ A₀) ∧ (conflictNbhdGen α γ A₀).ncard ≤ D)
    (x : Point 3 ≃ₗ[ℝ] Point 3) :
    ∃ (Nx : Finset (Point 3 ≃ₗ[ℝ] Point 3)),
      (∀ y, y ∈ Nx ↔ graphConflictGen α γ x y) ∧ Nx.card ≤ D := by
  classical
  by_cases hx : x ∈ shapeNet α
  · let N := conflictNbhdGen α γ x
    have hN_fin : Set.Finite N := (hD x hx).1
    let Nx : Finset (Point 3 ≃ₗ[ℝ] Point 3) := hN_fin.toFinset
    have h2 : ∀ y, y ∈ Nx ↔ graphConflictGen α γ x y := by
      intro y
      have h1 : y ∈ Nx ↔ y ∈ N := by
        simp [Nx, Set.Finite.mem_toFinset]
      rw [h1]
      simp only [N, conflictNbhdGen, Set.mem_setOf_eq, graphConflictGen]
      <;> exact ⟨fun h => ⟨hx, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
    have h3 : Nx.card ≤ D := by
      have h4 : N.ncard = Nx.card := Set.ncard_eq_toFinset_card N hN_fin
      have h5 : Nx.card = N.ncard := h4.symm
      rw [h5]; exact (hD x hx).2
    exact ⟨Nx, h2, h3⟩
  · exact ⟨∅, by simp [graphConflictGen, hx], by simp⟩

/-- Proper colouring of generalized conflict graph with D+1 colours. -/
noncomputable def shapeColour_gen (α γ : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhdGen α γ A₀) ∧ (conflictNbhdGen α γ A₀).ncard ≤ D) :
    (Point 3 ≃ₗ[ℝ] Point 3) → Fin (D + 1) := by
  classical
  exact Classical.choose <|
    bounded_degree_colouring (graphConflictGen α γ) D
      (shapeNet_degreeFinset_gen α γ D hD)
      (graphConflictGen_symm α γ)

/-- The generalized shape colouring is a proper colouring. -/
lemma shapeColour_gen_isProper (α γ : ℝ) (D : ℕ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhdGen α γ A₀) ∧ (conflictNbhdGen α γ A₀).ncard ≤ D) :
    ∀ (x y : Point 3 ≃ₗ[ℝ] Point 3),
      graphConflictGen α γ x y → x ≠ y →
      shapeColour_gen α γ D hD x ≠ shapeColour_gen α γ D hD y := by
  classical
  exact Classical.choose_spec <|
    bounded_degree_colouring (graphConflictGen α γ) D
      (shapeNet_degreeFinset_gen α γ D hD)
      (graphConflictGen_symm α γ)

/-- Same colour + both α-close to the same shape → equal,
for generalized conflict parameter γ ≥ α². -/
lemma shapeColour_gen_separation (α γ : ℝ) (D : ℕ)
    (hα : 1 < α) (hge : α ^ 2 ≤ γ)
    (hD : ∀ (A₀ : Point 3 ≃ₗ[ℝ] Point 3), A₀ ∈ shapeNet α →
      Set.Finite (conflictNbhdGen α γ A₀) ∧ (conflictNbhdGen α γ A₀).ncard ≤ D)
    {A₁ A₂ : Point 3 ≃ₗ[ℝ] Point 3}
    (h₁ : A₁ ∈ shapeNet α) (h₂ : A₂ ∈ shapeNet α)
    (hcol : shapeColour_gen α γ D hD A₁ = shapeColour_gen α γ D hD A₂)
    {A_K : Point 3 ≃ₗ[ℝ] Point 3}
    (hK1 : ShapeClose α A_K A₁) (hK2 : ShapeClose α A_K A₂) :
    A₁ = A₂ := by
  by_cases hne : A₁ = A₂
  · exact hne
  · have h1' : ShapeClose α A₁ A_K := shapeClose_symm.mp hK1
    have h_conf : ShapeClose (α * α) A₁ A₂ := shapeClose_trans h1' hK2
    have h_conf2 : ShapeClose (α ^ 2) A₁ A₂ := by
      have hpow : α * α = α ^ 2 := by ring
      rw [hpow] at h_conf
      exact h_conf
    have h_conf3 : ShapeClose γ A₁ A₂ := shapeClose_mono hge h_conf2
    have h_gc : graphConflictGen α γ A₁ A₂ := ⟨h₁, h₂, h_conf3⟩
    have h_proper : shapeColour_gen α γ D hD A₁ ≠ shapeColour_gen α γ D hD A₂ :=
      shapeColour_gen_isProper α γ D hD A₁ A₂ h_gc hne
    exact False.elim (h_proper hcol)

end Kakeya.CV.ShapeNet
