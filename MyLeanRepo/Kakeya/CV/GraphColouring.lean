import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Order

/-!
# Bounded-degree graph colouring theorem

Every graph with maximum degree `D` admits a proper colouring with `D + 1` colours.
Proof by well-ordering vertices and greedy colouring.
-/

namespace Kakeya.CV

/-- Every graph with maximum degree `D` admits a proper colouring with `D + 1` colours. -/
theorem bounded_degree_colouring {α : Type*} [DecidableEq α]
    (r : α → α → Prop) (D : ℕ)
    (hdeg : ∀ x, ∃ (Nx : Finset α), (∀ y, y ∈ Nx ↔ r x y) ∧ Nx.card ≤ D)
    (hsymm : ∀ x y, r x y → r y x) :
    ∃ (c : α → Fin (D + 1)), ∀ x y, r x y → x ≠ y → c x ≠ c y := by
  classical
  choose N hN_iff hN_card using hdeg
  have hN_symm : ∀ x y, y ∈ N x → x ∈ N y := by
    intro x y hy
    have hxy : r x y := (hN_iff x y).mp hy
    exact (hN_iff y x).mpr (hsymm x y hxy)

  let wo : α → α → Prop := WellOrderingRel
  have hwf : WellFounded wo := IsWellFounded.wf
  have h_total : ∀ (x y : α), x ≠ y → wo x y ∨ wo y x := by
    intro x y hne
    have h : IsWellOrder α wo := inferInstance
    have h' : wo x y ∨ x = y ∨ wo y x := by
      exact Std.Trichotomous.rel_or_eq_or_rel_swap
    rcases h' with (h | rfl | h) <;> tauto

  let used (x : α) (get_c : (y : α) → wo y x → Fin (D + 1)) : Finset (Fin (D + 1)) :=
    let pred_N : Finset α := (N x).filter (fun y => wo y x)
    let get_c_total (y : α) : Fin (D + 1) :=
      if h : wo y x then get_c y h else 0
    pred_N.image get_c_total

  have h_used_le (x : α) (get_c : (y : α) → wo y x → Fin (D + 1)) :
      (used x get_c).card ≤ (N x).card := by
    let pred_N : Finset α := (N x).filter (fun y => wo y x)
    have h1 : (used x get_c).card ≤ pred_N.card := Finset.card_image_le
    have h2 : pred_N.card ≤ (N x).card := Finset.card_filter_le _ _
    exact le_trans h1 h2

  have h_exists (x : α) (get_c : (y : α) → wo y x → Fin (D + 1)) :
      ∃ (col : Fin (D + 1)), col ∉ used x get_c := by
    have h1 : (used x get_c).card ≤ D :=
      le_trans (h_used_le x get_c) (hN_card x)
    by_contra h
    push Not at h
    have h_all : (Finset.univ : Finset (Fin (D + 1))) ⊆ used x get_c := by
      intro col _; exact h col
    have h2 : (Finset.univ : Finset (Fin (D + 1))).card ≤ (used x get_c).card :=
      Finset.card_le_card h_all
    rw [Finset.card_fin] at h2
    linarith

  let F : (x : α) → ((y : α) → wo y x → Fin (D + 1)) → Fin (D + 1) :=
    fun x get_c => Classical.choose (h_exists x get_c)

  let c : α → Fin (D + 1) := hwf.fix F

  have hF_eq : ∀ x, c x = F x (fun y _ => c y) := by
    intro x
    exact WellFounded.fix_eq hwf F x

  have h_not_used : ∀ x, c x ∉ used x (fun y _ => c y) := by
    intro x
    rw [hF_eq x]
    exact Classical.choose_spec (h_exists x (fun y _ => c y))

  refine' ⟨c, _⟩
  intro x y hxy hne
  have h_x_in_Ny : x ∈ N y := by
    have h : r y x := hsymm x y hxy
    exact (hN_iff y x).mpr h
  have h_y_in_Nx : y ∈ N x := (hN_iff x y).mpr hxy
  have h_cases : wo x y ∨ wo y x := h_total x y hne
  cases h_cases with
  | inl h_xy =>
    -- x before y: c x is in used y, so c y ≠ c x
    let pred_Ny : Finset α := (N y).filter (fun z => wo z y)
    have h_x_in_pred : x ∈ pred_Ny := by
      rw [Finset.mem_filter]
      exact ⟨h_x_in_Ny, h_xy⟩
    have h_cx_in_used : c x ∈ used y (fun z _ => c z) := by
      rw [Finset.mem_image]
      refine' ⟨x, h_x_in_pred, _⟩
      have h_eq : (if h : wo x y then c x else 0) = c x := by
        rw [dif_pos h_xy]
      exact h_eq
    have h : c y ∉ used y (fun z _ => c z) := h_not_used y
    exact fun h_eq => h (h_eq ▸ h_cx_in_used)
  | inr h_yx =>
    -- y before x: c y is in used x, so c x ≠ c y
    let pred_Nx : Finset α := (N x).filter (fun z => wo z x)
    have h_y_in_pred : y ∈ pred_Nx := by
      rw [Finset.mem_filter]
      exact ⟨h_y_in_Nx, h_yx⟩
    have h_cy_in_used : c y ∈ used x (fun z _ => c z) := by
      rw [Finset.mem_image]
      refine' ⟨y, h_y_in_pred, _⟩
      have h_eq : (if h : wo y x then c y else 0) = c y := by
        rw [dif_pos h_yx]
      exact h_eq
    have h : c x ∉ used x (fun z _ => c z) := h_not_used x
    exact fun h_eq => h (h_eq ▸ h_cy_in_used)

end Kakeya.CV
