module

/-
  Product Splitting — Extract from InductiveStepCore_v2.

  Splits products over all scales into first-scale (j0) and tail (shift) parts.
  Used to decompose combiningLowerBound into PΔ * Pb.

  Whiteprint node: combining_theorem_genuine / inductive_step_core_v2
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

/-- Split a product over Fin (n_fine+1) into first element + tail via Fin.succ. -/
lemma finset_product_split_first
    {n_fine : ℕ} {α : Type*} [CommMonoid α]
    (j0 : Fin (n_fine + 1))
    (hj0 : j0.val = 0)
    (p : Fin (n_fine + 1) → Prop) [DecidablePred p]
    (f : Fin (n_fine + 1) → α) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n_fine + 1))).filter p, f j) =
    (∏ j ∈ ({j0} : Finset (Fin (n_fine + 1))).filter p, f j) *
    (∏ i ∈ (Finset.univ : Finset (Fin n_fine)).filter (fun (i : Fin n_fine) => p (Fin.succ i)), f (Fin.succ i)) := by
  let shift : Fin n_fine → Fin (n_fine + 1) := Fin.succ
  have h_shift_inj : Function.Injective shift := by
    intro a b h; simp [shift, Fin.ext_iff] at h <;> omega
  have h_univ_split : (Finset.univ : Finset (Fin (n_fine + 1))) =
      insert j0 (Finset.image shift Finset.univ) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_iff]
    by_cases h : x.val = 0
    · left; apply Fin.ext; simp [hj0, h]
    · right
      let j : Fin n_fine := ⟨x.val - 1, by omega⟩
      have h_eq : shift j = x := by
        apply Fin.ext; simp [shift, j] <;> omega
      exact ⟨j, trivial, h_eq⟩
  have h_disj : Disjoint ({j0} : Finset (Fin (n_fine + 1)))
      (Finset.image shift Finset.univ) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : x = j0 := Finset.mem_singleton.mp hx1
    rcases Finset.mem_image.mp hx2 with ⟨j, _, rfl⟩
    simp [hj0, shift, Fin.ext_iff] at h1 <;> omega
  have h_insert_eq : insert j0 (Finset.image shift Finset.univ) =
      ({j0} : Finset (Fin (n_fine + 1))) ∪ Finset.image shift Finset.univ := by
    ext x; simp
  have h1 : (Finset.univ : Finset (Fin (n_fine + 1))).filter p =
      (({j0} : Finset (Fin (n_fine + 1))).filter p) ∪
      ((Finset.image shift Finset.univ).filter p) := by
    rw [h_univ_split, h_insert_eq, Finset.filter_union]
  rw [h1]
  have h_disj2 : Disjoint (({j0} : Finset (Fin (n_fine + 1))).filter p)
      ((Finset.image shift Finset.univ).filter p) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) h_disj
  rw [Finset.prod_union h_disj2]
  have h2 : ((Finset.image shift Finset.univ).filter p) =
      Finset.image shift ((Finset.univ : Finset (Fin n_fine)).filter (fun i => p (shift i))) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨j, hj_mem, rfl⟩, hz2⟩
      exact ⟨j, ⟨hj_mem, hz2⟩, rfl⟩
    · rintro ⟨j, ⟨hj_mem, hgood⟩, rfl⟩
      exact ⟨⟨j, hj_mem, rfl⟩, hgood⟩
  rw [h2]
  have h_inj_on : Set.InjOn shift ((Finset.univ : Finset (Fin n_fine)).filter (fun i => p (shift i))) :=
    fun x _ y _ hxy => h_shift_inj hxy
  rw [Finset.prod_image h_inj_on]
  <;> rfl

end Prop73Restructure

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
