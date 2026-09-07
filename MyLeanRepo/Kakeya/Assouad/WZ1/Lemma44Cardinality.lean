import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Product-filter cardinality helpers for WZ1 Lemma 44

Standard finset identities used in the triple-count assembly.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
`∑ y ∈ B, #{x ∈ A | P x y} = #{(x,y) ∈ A ×ˢ B | P x y}`
-/
lemma sum_card_filter {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {B : Finset β}
    (P : α → β → Prop) [DecidableRel P] :
    ∑ y ∈ B, (A.filter (fun x => P x y)).card =
    ((A ×ˢ B).filter (fun p : α × β => P p.1 p.2)).card := by
  let f : β → Finset (α × β) := fun y =>
    (A.filter (fun x => P x y)).image (fun x => (x, y))
  have h_disj : ∀ y1 ∈ B, ∀ y2 ∈ B, y1 ≠ y2 → Disjoint (f y1) (f y2) := by
    intro y1 _ y2 _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.2 = y1 := by
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩ <;> rfl
    have h2 : p.2 = y2 := by
      rcases Finset.mem_image.mp hp2 with ⟨_, _, rfl⟩ <;> rfl
    exact hne (h1.symm.trans h2)
  have h_union : (A ×ˢ B).filter (fun p : α × β => P p.1 p.2) =
      B.biUnion f := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, f,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨hx, hy⟩, hP⟩
      exact ⟨y, hy, x, ⟨hx, hP⟩, rfl⟩
    · rintro ⟨a, ha, x', ⟨hx', hP'⟩, heq⟩
      have h1 : x' = x := congrArg Prod.fst heq
      have h2 : a = y := congrArg Prod.snd heq
      simp only [h1, h2] at hx' hP' ha ⊢
      exact ⟨⟨hx', ha⟩, hP'⟩
  have h_inj : ∀ (y : β), Function.Injective (fun x : α => (x, y)) := by
    intro y a b h
    simpa using h
  have h_card : ∀ y ∈ B, (f y).card = (A.filter (fun x => P x y)).card := by
    intro y _
    rw [Finset.card_image_of_injective _ (h_inj y)]
  calc
    ∑ y ∈ B, (A.filter (fun x => P x y)).card
      = ∑ y ∈ B, (f y).card := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (h_card y hy).symm
    _ = (B.biUnion f).card := by
        rw [Finset.card_biUnion h_disj]
    _ = ((A ×ˢ B).filter (fun p : α × β => P p.1 p.2)).card := by
        rw [h_union]

/--
`∑ z ∈ C, #{x ∈ A | P x z} * #{y ∈ B | Q y z}
   = #{((x,y),z) ∈ (A ×ˢ B) ×ˢ C | P x z ∧ Q y z}`
-/
lemma sum_product_card_filter {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {A : Finset α} {B : Finset β} {C : Finset γ}
    (P : α → γ → Prop) (Q : β → γ → Prop)
    [DecidableRel P] [DecidableRel Q] :
    ∑ z ∈ C, (A.filter (fun x => P x z)).card * (B.filter (fun y => Q y z)).card =
    (((A ×ˢ B) ×ˢ C).filter
      (fun p : (α × β) × γ => P p.1.1 p.2 ∧ Q p.1.2 p.2)).card := by
  let f : γ → Finset ((α × β) × γ) := fun z =>
    ((A.filter (fun x => P x z)) ×ˢ (B.filter (fun y => Q y z))).image
      (fun p : α × β => (p, z))
  have h_disj : ∀ z1 ∈ C, ∀ z2 ∈ C, z1 ≠ z2 → Disjoint (f z1) (f z2) := by
    intro z1 _ z2 _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.2 = z1 := by
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩ <;> rfl
    have h2 : p.2 = z2 := by
      rcases Finset.mem_image.mp hp2 with ⟨_, _, rfl⟩ <;> rfl
    exact hne (h1.symm.trans h2)
  have h_union : ((A ×ˢ B) ×ˢ C).filter
        (fun p : (α × β) × γ => P p.1.1 p.2 ∧ Q p.1.2 p.2) =
      C.biUnion f := by
    ext ⟨⟨x, y⟩, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, f,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, hz⟩, hP, hQ⟩
      exact ⟨z, hz, (x, y), ⟨⟨hx, hP⟩, ⟨hy, hQ⟩⟩, rfl⟩
    · rintro ⟨a, ha, p, ⟨⟨hx, hP⟩, ⟨hy, hQ⟩⟩, heq⟩
      have h1 : p = (x, y) := congrArg Prod.fst heq
      have h2 : a = z := congrArg Prod.snd heq
      simp only [h1, h2] at hx hP hy hQ ha ⊢
      exact ⟨⟨⟨hx, hy⟩, ha⟩, hP, hQ⟩
  have h_inj : ∀ (z : γ), Function.Injective (fun p : α × β => (p, z)) := by
    intro z a b h
    simpa using h
  have h_card : ∀ z ∈ C, (f z).card =
      (A.filter (fun x => P x z)).card * (B.filter (fun y => Q y z)).card := by
    intro z _
    rw [Finset.card_image_of_injective _ (h_inj z), Finset.card_product]
  calc
    ∑ z ∈ C, (A.filter (fun x => P x z)).card * (B.filter (fun y => Q y z)).card
      = ∑ z ∈ C, (f z).card := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (h_card z hz).symm
    _ = (C.biUnion f).card := by
        rw [Finset.card_biUnion h_disj]
    _ = (((A ×ˢ B) ×ˢ C).filter
          (fun p : (α × β) × γ => P p.1.1 p.2 ∧ Q p.1.2 p.2)).card := by
        rw [h_union]

/--
Real-valued squared version:
`∑ z ∈ C, (#{x ∈ A | P x z} : ℝ)² = (#{((x,y),z) | P x z ∧ P y z} : ℝ)`
-/
lemma sum_sq_card_filter_real {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    {A : Finset α} {C : Finset γ}
    (P : α → γ → Prop) [DecidableRel P] :
    ∑ z ∈ C, ((A.filter (fun x => P x z)).card : ℝ)^2 =
    (((A ×ˢ A) ×ˢ C).filter
      (fun p : (α × α) × γ => P p.1.1 p.2 ∧ P p.1.2 p.2)).card := by
  have h_main := sum_product_card_filter (P := P) (Q := P) (A := A) (B := A) (C := C)
  have h_cast : (∑ z ∈ C, ((A.filter (fun x => P x z)).card : ℝ)^2) =
      ↑(∑ z ∈ C, (A.filter (fun x => P x z)).card * (A.filter (fun x => P x z)).card) := by
    have h : ∀ z ∈ C, (((A.filter (fun x => P x z)).card : ℝ)^2) =
        ↑((A.filter (fun x => P x z)).card * (A.filter (fun x => P x z)).card) := by
      intro z _
      simp [pow_two]
    rw [Finset.sum_congr rfl h]
    norm_cast
  rw [h_cast]
  exact_mod_cast h_main

end Kakeya.Assouad
