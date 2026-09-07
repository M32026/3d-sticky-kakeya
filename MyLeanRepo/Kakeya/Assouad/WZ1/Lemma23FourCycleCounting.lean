import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FourCycleStatements
import Mathlib.Algebra.Order.Chebyshev

/-!
# Count WZ1 Lemma 23 local-global four-cycles

Apply finite Cauchy--Schwarz to local-grain pairs grouped by their collision
signature, then identify equal-signature collisions with the paper's ordered
four-cycles.
-/

namespace Kakeya.Assouad

open Finset

private lemma mem_localPairs_iff
    {Cube : Type*} [DecidableEq Cube]
    {cubes : Finset Cube} {sameLocalGrain : Cube → Cube → Prop}
    [DecidableRel sameLocalGrain] (pair : Cube × Cube) :
    pair ∈ wz1Lemma23LocalPairs cubes sameLocalGrain ↔
      pair.1 ∈ cubes ∧ pair.2 ∈ cubes ∧
        sameLocalGrain pair.1 pair.2 := by
  simp [wz1Lemma23LocalPairs, Finset.mem_filter, Finset.mem_product]
  tauto

private lemma mem_fourCycles_iff
    {Cube Height GlobalBin : Type*}
    [DecidableEq Cube] [DecidableEq Height] [DecidableEq GlobalBin]
    {cubes : Finset Cube} {sameLocalGrain : Cube → Cube → Prop}
    [DecidableRel sameLocalGrain] {height : Cube → Height}
    {globalBin : Cube → GlobalBin}
    (path : Cube × Cube × Cube × Cube) :
    path ∈
        wz1Lemma23FourCycles cubes sameLocalGrain height globalBin ↔
      path.1 ∈ cubes ∧
      path.2.1 ∈ cubes ∧
      path.2.2.1 ∈ cubes ∧
      path.2.2.2 ∈ cubes ∧
      sameLocalGrain path.1 path.2.1 ∧
      sameLocalGrain path.2.2.2 path.2.2.1 ∧
      height path.1 = height path.2.2.2 ∧
      height path.2.1 = height path.2.2.1 ∧
      globalBin path.2.1 = globalBin path.2.2.1 := by
  simp [wz1Lemma23FourCycles, Finset.mem_filter, Finset.mem_product]
  tauto

private lemma mem_collisions_iff
    {Cube Height GlobalBin : Type*}
    [DecidableEq Cube] [DecidableEq Height] [DecidableEq GlobalBin]
    {localPairs : Finset (Cube × Cube)}
    {signature : Cube × Cube → Height × Height × GlobalBin}
    (collision : (Cube × Cube) × (Cube × Cube)) :
    collision ∈
        (localPairs.product localPairs).filter
          (fun pair => signature pair.1 = signature pair.2) ↔
      collision.1 ∈ localPairs ∧
      collision.2 ∈ localPairs ∧
      signature collision.1 = signature collision.2 := by
  simp [Finset.mem_filter, Finset.mem_product]
  tauto

private lemma fiber_cauchy_schwarz
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (set : Finset α) (map : α → β) :
    set.card ^ 2 ≤
      (set.image map).card *
        ((set.product set).filter
          (fun pair : α × α => map pair.1 = map pair.2)).card := by
  let image := set.image map
  let fiber : β → Finset α := fun value =>
    set.filter (fun element => map element = value)
  let collisions :=
    (set.product set).filter
      (fun pair : α × α => map pair.1 = map pair.2)
  have h_fiber_sum :
      set.card = ∑ value ∈ image, (fiber value).card :=
    Finset.card_eq_sum_card_image map set
  have h_disjoint :
      (image : Set β).PairwiseDisjoint
        (fun value => fiber value ×ˢ fiber value) := by
    intro first _ second _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro pair hfirst hsecond
    have h1 : pair.1 ∈ fiber first :=
      (Finset.mem_product.mp hfirst).1
    have h1' : map pair.1 = first :=
      (Finset.mem_filter.mp h1).2
    have h2 : pair.1 ∈ fiber second :=
      (Finset.mem_product.mp hsecond).1
    have h2' : map pair.1 = second :=
      (Finset.mem_filter.mp h2).2
    exact hne (h1'.symm.trans h2')
  have h_collisions_eq :
      collisions =
        image.biUnion (fun value => fiber value ×ˢ fiber value) := by
    ext pair
    simp [collisions, fiber, Finset.mem_biUnion,
      Finset.mem_product, Finset.mem_filter]
    aesop
  have h_collisions_card :
      collisions.card =
        ∑ value ∈ image, (fiber value).card ^ 2 := by
    rw [h_collisions_eq, Finset.card_biUnion h_disjoint]
    apply Finset.sum_congr rfl
    intro value _
    rw [Finset.card_product, sq]
  have h_cauchy_schwarz :
      (set.card : ℤ) ^ 2 ≤
        (image.card : ℤ) *
          ∑ value ∈ image, ((fiber value).card : ℤ) ^ 2 := by
    have h :=
      sq_sum_le_card_mul_sum_sq
        (s := image)
        (f := fun value : β => ((fiber value).card : ℤ))
    have hsum :
        (∑ value ∈ image, ((fiber value).card : ℤ)) =
          (set.card : ℤ) := by
      rw [← Nat.cast_sum, h_fiber_sum]
    rw [hsum] at h
    exact h
  have h_main :
      (set.card : ℤ) ^ 2 ≤
        (image.card : ℤ) * (collisions.card : ℤ) := by
    rw [h_collisions_card] at *
    simpa [Nat.cast_sum, Nat.cast_pow] using h_cauchy_schwarz
  exact_mod_cast h_main

theorem wz1_lemma23_four_cycle_counting :
    WZ1Lemma23FourCycleCountingStatement := by
  intro Cube Height GlobalBin _ _ _ cubes sameLocalGrain _
    height globalBin signatureBound
  dsimp only
  set localPairs :=
    wz1Lemma23LocalPairs cubes sameLocalGrain with hlocalPairs
  set signature :=
    wz1Lemma23PairSignature height globalBin with hsignature
  set signatures := localPairs.image signature with hsignatures
  set fourCycles :=
    wz1Lemma23FourCycles cubes sameLocalGrain height globalBin
      with hfourCycles
  intro hsignature_bound

  let collisions : Finset ((Cube × Cube) × (Cube × Cube)) :=
    (localPairs.product localPairs).filter
      (fun pair => signature pair.1 = signature pair.2)

  have h_cauchy_schwarz :
      localPairs.card ^ 2 ≤ signatures.card * collisions.card :=
    fiber_cauchy_schwarz localPairs signature

  let forward :
      ((Cube × Cube) × (Cube × Cube)) →
        Cube × Cube × Cube × Cube :=
    fun pair => (pair.1.1, pair.1.2, pair.2.2, pair.2.1)
  let inverse :
      (Cube × Cube × Cube × Cube) →
        (Cube × Cube) × (Cube × Cube) :=
    fun path => ((path.1, path.2.1), (path.2.2.2, path.2.2.1))

  have hforward :
      ∀ collision ∈ collisions, forward collision ∈ fourCycles := by
    intro collision hcollision
    have h := (mem_collisions_iff collision).mp hcollision
    have hfirst := (mem_localPairs_iff collision.1).mp h.1
    have hsecond := (mem_localPairs_iff collision.2).mp h.2.1
    have hsignature_eq :
        height collision.1.1 = height collision.2.1 ∧
        height collision.1.2 = height collision.2.2 ∧
        globalBin collision.1.2 = globalBin collision.2.2 := by
      simpa [signature, wz1Lemma23PairSignature, Prod.ext_iff]
        using h.2.2
    rw [hfourCycles, mem_fourCycles_iff]
    exact
      ⟨hfirst.1, hfirst.2.1, hsecond.2.1, hsecond.1,
        hfirst.2.2, hsecond.2.2, hsignature_eq.1,
        hsignature_eq.2.1, hsignature_eq.2.2⟩

  have hinverse :
      ∀ path ∈ fourCycles, inverse path ∈ collisions := by
    intro path hpath
    rcases (mem_fourCycles_iff path).mp hpath with
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    have hfirst : (inverse path).1 ∈ localPairs := by
      rw [mem_localPairs_iff]
      simp [inverse, h1, h2, h5]
    have hsecond : (inverse path).2 ∈ localPairs := by
      rw [mem_localPairs_iff]
      simp [inverse, h3, h4, h6]
    have hsignature_eq :
        signature (inverse path).1 =
          signature (inverse path).2 := by
      simp [inverse, signature, wz1Lemma23PairSignature, h7, h8, h9]
    rw [mem_collisions_iff]
    exact ⟨hfirst, hsecond, hsignature_eq⟩

  have hleft :
      ∀ collision ∈ collisions,
        inverse (forward collision) = collision := by
    intro collision _
    ext <;> simp [forward, inverse]
  have hright :
      ∀ path ∈ fourCycles, forward (inverse path) = path := by
    intro path _
    ext <;> simp [forward, inverse]

  have hcard : collisions.card = fourCycles.card :=
    Finset.card_nbij'
      forward inverse hforward hinverse hleft hright

  have hbound :
      localPairs.card ^ 2 ≤ signatureBound * fourCycles.card := by
    calc
      localPairs.card ^ 2
          ≤ signatures.card * fourCycles.card := by
            rw [← hcard]
            exact h_cauchy_schwarz
      _ ≤ signatureBound * fourCycles.card := by
        gcongr
  simpa [hlocalPairs, hfourCycles] using hbound

end Kakeya.Assouad
