module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.ExtraBasic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.UniformSSet
public import MyLeanRepo.InductionOnScales.PadSSet
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# NiceConfiguration Helpers

Helper lemmas for constructing and modifying `NiceConfiguration` structures,
used by both the coarse and fine phase assembly.

## Main results

1. `niceConfigBuilder` — construct a `NiceConfiguration` from explicit fields.
2. `pad_coarse_families_to_uniform_size` — pad per-square tube families to a
   common cardinality while preserving SSet properties.
3. `subset_tube_family_with_sset` — subset with cardinality ratio bound inherits
   SSet with scaled constant (wrapper around `sset_uniform_subset`).
4. `retain_tubes_with_coarse_ancestor` — filter fine tubes to those geometrically
   contained in some member of a coarse tube set; proves the filter is the
   identity when the coarse set covers all ancestors.

## Whiteprint node
`InductionOnScales/NiceConfigHelpers`
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

-- ============================================================================
-- 1. NiceConfiguration builder
-- ============================================================================

/-- Construct a `NiceConfiguration` from all its fields.

This is a thin wrapper around the structure constructor that makes proof
scripts more readable when assembling configurations in the induction step. -/
def niceConfigBuilder
    {n : ℕ} {s C : ℝ} {M : ℕ}
    (points : Finset (DyadicSquare n))
    (tubes : Finset (DyadicTube n))
    (tubeFamily : (p : DyadicSquare n) → p ∈ points → Finset (DyadicTube n))
    (h_subset : ∀ p hp, tubeFamily p hp ⊆ tubes)
    (h_size : ∀ p hp, (tubeFamily p hp).card = M)
    (h_sset : ∀ p hp, IsFiniteTubeSSet s C (tubeFamily p hp))
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
      (T.toSet ∩ p.toSet).Nonempty)
    (h_bounded : ∀ p ∈ points, p.toSet ⊆ unitSquare)
    (h_tube_parameters : ∀ T ∈ tubes, T.IsInAllowedParameterStrip) :
    NiceConfiguration n s C M :=
  { points, tubes, tubeFamily, h_subset, h_size, h_sset, h_incidence,
    h_bounded, h_tube_parameters }

-- ============================================================================
-- 2. Pad per-coarse-square families to uniform size
-- ============================================================================

/-- Given per-square tube families of varying sizes (all ≤ `MΔ`), pad each
one to exactly `MΔ` using `pad_sset_family`, preserving the SSet constant.

The padded families supersede the originals. -/
lemma pad_coarse_families_to_uniform_size
    {m : ℕ} {s C : ℝ} {MΔ : ℕ}
    (QSet : Finset (DyadicSquare m))
    (fam : (Q : DyadicSquare m) → Q ∈ QSet → Finset (DyadicTube m))
    (h_sset : ∀ Q hQ, IsFiniteTubeSSet s C (fam Q hQ))
    (h_size : ∀ Q hQ, (fam Q hQ).card ≤ MΔ) :
    ∃ (fam' : (Q : DyadicSquare m) → Q ∈ QSet → Finset (DyadicTube m)),
      (∀ Q hQ, fam Q hQ ⊆ fam' Q hQ) ∧
      (∀ Q hQ, (fam' Q hQ).card = MΔ) ∧
      (∀ Q hQ, IsFiniteTubeSSet s C (fam' Q hQ)) := by
  have h_choose : ∀ (Q : DyadicSquare m) (hQ : Q ∈ QSet),
      ∃ (G : Finset (DyadicTube m)),
        fam Q hQ ⊆ G ∧ G.card = MΔ ∧ IsFiniteTubeSSet s C G := by
    intro Q hQ
    exact pad_sset_family (h_sset Q hQ) MΔ (h_size Q hQ)
  choose G hG_sub hG_card hG_sset using h_choose
  let fam' : (Q : DyadicSquare m) → Q ∈ QSet → Finset (DyadicTube m) :=
    fun Q hQ => G Q hQ
  exact ⟨fam', hG_sub, hG_card, hG_sset⟩

-- ============================================================================
-- 3. Subset with SSet constant scaling
-- ============================================================================

/-- If `F` is an SSet with constant `C` and `G ⊆ F` with `|F| ≤ K·|G|`,
then `G` is an SSet with constant `K·C`.

Thin wrapper around `sset_uniform_subset` with a name aligned to the
NiceConfiguration assembly vocabulary. -/
lemma subset_tube_family_with_sset
    {n : ℕ} {s C K : ℝ}
    {F G : Finset (DyadicTube n)}
    (hG : G ⊆ F)
    (hSSet : IsFiniteTubeSSet s C F)
    (h_size : (F.card : ℝ) ≤ K * (G.card : ℝ))
    (hK : 1 ≤ K) :
    IsFiniteTubeSSet s (K * C) G :=
  sset_uniform_subset hG hSSet h_size hK

-- ============================================================================
-- 4. Retain tubes with a containing coarse ancestor
-- ============================================================================

/-- The set of fine tubes geometrically contained in some member of `TΔ`. -/
def retainWithCoarseAncestor {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n))
    (TΔ : Finset (DyadicTube m)) : Finset (DyadicTube n) :=
  F.filter (fun T => ∃ U ∈ TΔ, T.toSet ⊆ U.toSet)

/-- If every fine tube `T ∈ F` has its coordinatewise coarse ancestor in `TΔ`,
then `retainWithCoarseAncestor` returns `F` unchanged.

This uses `coarseAnc_contains`: every fine tube is geometrically contained
in its `deprecatedCoordinatewiseAncestor`. -/
lemma retainWithCoarseAncestor_eq_self
    {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n))
    (TΔ : Finset (DyadicTube m))
    (h_cover : ∀ T ∈ F, deprecatedCoordinatewiseAncestor hnm T ∈ TΔ) :
    retainWithCoarseAncestor hnm F TΔ = F := by
  apply Finset.ext
  intro T
  simp only [retainWithCoarseAncestor, Finset.mem_filter]
  constructor
  · rintro ⟨hT, _⟩
    exact hT
  · intro hT
    let U := deprecatedCoordinatewiseAncestor hnm T
    have hU_in : U ∈ TΔ := h_cover T hT
    have h_contain : T.toSet ⊆ U.toSet := coarseAnc_contains hnm T
    exact ⟨hT, ⟨U, hU_in, h_contain⟩⟩

/-- Under the ancestor-cover hypothesis, the retained family is nonempty
iff the original family is nonempty. -/
lemma retainWithCoarseAncestor_nonempty
    {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n))
    (TΔ : Finset (DyadicTube m))
    (h_cover : ∀ T ∈ F, deprecatedCoordinatewiseAncestor hnm T ∈ TΔ) :
    (retainWithCoarseAncestor hnm F TΔ).Nonempty ↔ F.Nonempty := by
  rw [retainWithCoarseAncestor_eq_self hnm F TΔ h_cover]

/-- General version: if every `T ∈ F` is covered by some `U ∈ TΔ` (not
necessarily its coordinatewise ancestor), then the retained family equals `F`. -/
lemma retainWithCoarseAncestor_eq_self_of_cover
    {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n))
    (TΔ : Finset (DyadicTube m))
    (h_cover : ∀ T ∈ F, ∃ U ∈ TΔ, T.toSet ⊆ U.toSet) :
    retainWithCoarseAncestor hnm F TΔ = F := by
  apply Finset.ext
  intro T
  simp only [retainWithCoarseAncestor, Finset.mem_filter]
  constructor
  · rintro ⟨hT, _⟩
    exact hT
  · intro hT
    exact ⟨hT, h_cover T hT⟩

end InductionOnScales
