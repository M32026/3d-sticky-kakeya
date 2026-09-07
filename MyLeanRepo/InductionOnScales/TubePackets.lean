module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.SSetVerification
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Tube packet separation and counting

Partition a family of fine dyadic tubes into packets by their coarse ancestor,
and establish counting bounds used in the cardinality estimate (5.5).

## Main results
- `packet_counting`: |F| ≥ num_packets × min_packet_size
- `select_one_per_packet`: extract a subset with one tube per packet

`coarse_tubes_separation` is re-exported from `SSetVerification`.

## Whiteprint node
`separated_tube_packets` under `InductionOnScales/`.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

-- ============================================================================
-- Re-exported foundational lemmas
-- ============================================================================

/-- A fine tube is geometrically contained in its coarse ancestor. -/
lemma fine_tube_in_coarse_ancestor {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) :
    T.toSet ⊆ (deprecatedCoordinatewiseAncestor hnm T).toSet := by
  let U := deprecatedCoordinatewiseAncestor hnm T
  have h1 := coarseParentIndex_spec n m hnm T.a
  have h2 := coarseParentIndex_spec n m hnm T.b
  rw [tube_containment_iff hnm T U]
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

-- ============================================================================
-- Fiber/packet counting
-- ============================================================================

/-- The sum of fiber cardinalities equals the original cardinality. -/
lemma fiber_sum_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (f : α → β) :
    ∑ y ∈ F.image f, (F.filter (fun x => f x = y)).card = F.card := by
  have h1 : ∀ y ∈ F.image f, (F.filter (fun x => f x = y)).card =
      ∑ x ∈ F, (if f x = y then 1 else 0) := by
    intro y _
    rw [Finset.card_filter]
    <;> rfl
  calc
    ∑ y ∈ F.image f, (F.filter (fun x => f x = y)).card
      = ∑ y ∈ F.image f, ∑ x ∈ F, (if f x = y then 1 else 0) := by
        apply Finset.sum_congr rfl; intro y _; exact h1 y ‹_›
    _ = ∑ x ∈ F, ∑ y ∈ F.image f, (if f x = y then 1 else 0) := by rw [Finset.sum_comm]
    _ = ∑ x ∈ F, 1 := by
        apply Finset.sum_congr rfl; intro x hx
        have h2 : f x ∈ F.image f := Finset.mem_image_of_mem f hx
        simp [h2]
    _ = F.card := by simp

/-- Number of fibers times minimum fiber size ≤ total size. -/
lemma packet_counting {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (f : α → β) (hF_nonempty : F.Nonempty)
    (min_size : ℕ) (h_min : ∀ y ∈ F.image f, min_size ≤ (F.filter (fun x => f x = y)).card) :
    (F.image f).card * min_size ≤ F.card := by
  have h_sum : ∑ y ∈ F.image f, (F.filter (fun x => f x = y)).card = F.card :=
    fiber_sum_card F f
  have h_lower : ∑ y ∈ F.image f, min_size ≤ ∑ y ∈ F.image f, (F.filter (fun x => f x = y)).card :=
    Finset.sum_le_sum h_min
  have h_const : ∑ y ∈ F.image f, min_size = (F.image f).card * min_size := by
    simp [Finset.sum_const] <;> ring
  rw [h_const] at h_lower
  rw [h_sum] at h_lower
  exact h_lower

/-- Select one element from each nonempty fiber. -/
lemma select_one_per_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (f : α → β) (hF_nonempty : F.Nonempty) :
    ∃ (S : Finset α), S ⊆ F ∧ S.card = (F.image f).card ∧
      (∀ y ∈ F.image f, ∃! x, x ∈ S ∧ f x = y) := by
  choose x hx using fun (y : β) (hy : y ∈ F.image f) => Finset.mem_image.mp hy
  let default_val : α := Classical.choose hF_nonempty
  let x' : β → α := fun y =>
    if hy : y ∈ F.image f then x y hy else default_val
  have h_x'_eq : ∀ (y : β) (hy : y ∈ F.image f), x' y = x y hy := by
    intro y hy
    unfold x'
    rw [dif_pos hy]
  let S : Finset α := (F.image f).image x'
  have hS_sub : S ⊆ F := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    rw [h_x'_eq y hy]
    exact (hx y hy).1
  have h_inj : Set.InjOn x' (F.image f) := by
    intro y1 hy1 y2 hy2 h
    have h1 : f (x' y1) = y1 := by
      rw [h_x'_eq y1 hy1] <;> exact (hx y1 hy1).2
    have h2 : f (x' y2) = y2 := by
      rw [h_x'_eq y2 hy2] <;> exact (hx y2 hy2).2
    have h_eq_f : f (x' y1) = f (x' y2) := by rw [h]
    have h3 : y1 = y2 := by
      calc y1 = f (x' y1) := h1.symm
        _ = f (x' y2) := h_eq_f
        _ = y2 := h2
    exact h3
  have h_card : S.card = (F.image f).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_unique : ∀ y ∈ F.image f, ∃! (x : α), x ∈ S ∧ f x = y := by
    intro y hy
    refine ⟨x' y, ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, by rw [h_x'_eq y hy] <;> exact (hx y hy).2⟩
    · intro z hz
      have hz1 : z ∈ S := hz.1
      have hz2 : f z = y := hz.2
      rcases Finset.mem_image.mp hz1 with ⟨y', hy', rfl⟩
      have hfy' : f (x' y') = y' := by
        rw [h_x'_eq y' hy'] <;> exact (hx y' hy').2
      rw [hfy'] at hz2
      rw [hz2]
  exact ⟨S, hS_sub, h_card, h_unique⟩

-- ============================================================================
-- Tube-specific packet results
-- ============================================================================

/-- Coarse ancestor packets of a fine tube family. -/
def coarseAncestorPackets {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) : Finset (DyadicTube m) :=
  F.image (deprecatedCoordinatewiseAncestor hnm)

/-- The packet of fine tubes sharing a given coarse ancestor. -/
def packetOf {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) (U : DyadicTube m) : Finset (DyadicTube n) :=
  F.filter (fun T => deprecatedCoordinatewiseAncestor hnm T = U)

/-- Every tube in a packet is contained in the packet's coarse ancestor. -/
lemma packet_tubes_contained {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) (U : DyadicTube m)
    (T : DyadicTube n) (hT : T ∈ packetOf hnm F U) :
    T.toSet ⊆ U.toSet := by
  have h_anc : deprecatedCoordinatewiseAncestor hnm T = U :=
    (Finset.mem_filter.mp hT).2
  have h_contain : T.toSet ⊆ (deprecatedCoordinatewiseAncestor hnm T).toSet :=
    fine_tube_in_coarse_ancestor hnm T
  rw [h_anc] at h_contain
  exact h_contain

/-- Counting bound: |packets| × min_packet_size ≤ |F|. -/
lemma coarse_packet_counting {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) (hF_nonempty : F.Nonempty)
    (min_size : ℕ)
    (h_min : ∀ U ∈ coarseAncestorPackets hnm F,
      min_size ≤ (packetOf hnm F U).card) :
    (coarseAncestorPackets hnm F).card * min_size ≤ F.card :=
  packet_counting F (deprecatedCoordinatewiseAncestor hnm) hF_nonempty min_size h_min

/-- Select one fine tube per coarse ancestor packet. -/
lemma select_one_per_packet {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) (hF_nonempty : F.Nonempty) :
    ∃ (S : Finset (DyadicTube n)),
      S ⊆ F ∧
      S.card = (coarseAncestorPackets hnm F).card ∧
      (∀ U ∈ coarseAncestorPackets hnm F,
        ∃! (T : DyadicTube n), T ∈ S ∧ deprecatedCoordinatewiseAncestor hnm T = U) :=
  select_one_per_fiber F (deprecatedCoordinatewiseAncestor hnm) hF_nonempty

/-- If two fine tubes have distinct coarse ancestors, those ancestors are
Δ-separated. -/
lemma distinct_packets_coarse_separation {n m : ℕ} (hnm : m ≤ n)
    (T1 T2 : DyadicTube n)
    (hne : deprecatedCoordinatewiseAncestor hnm T1 ≠ deprecatedCoordinatewiseAncestor hnm T2) :
    dyadicDelta m ≤ tubeParamDist
      (deprecatedCoordinatewiseAncestor hnm T1)
      (deprecatedCoordinatewiseAncestor hnm T2) :=
  coarse_tubes_separation
    (deprecatedCoordinatewiseAncestor hnm T1)
    (deprecatedCoordinatewiseAncestor hnm T2)
    hne

end InductionOnScales
