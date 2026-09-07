module

/-
  T_Delta_global construction from T_source via canonical pipeline.

  Defines T_Delta_global as the image of:
    ℓ ↦ snapTube n ℓ ↦ sourceParent hnm ↦ dyadicTubeToA2
  on T_source.

  Proves that any per-square C_Q with QTTC-style provenance is a subset
  of T_Delta_global.

  This is Lemma 1 of the C_global_A2 correction:
  - C_global_A2 is NOT an unrelated union bound
  - C_global_A2 ⊆ T_Delta_global by construction
  - Cardinality bound comes from coarse failure (Lemma 3, juniper)

  Integrates:
  - SnapTubeProvenance: sourceParent_intercept_bound for canonical intercept bounds
  - sourceParent_slope_bound_nonstrict: non-strict slope bound via floor_dyadic_bound_one
  - H2Migration.inParent_dist_lt_tenDelta: InParent → dist < 10·Δ (parent movement component; full C_move = 17 including 7δ_n Section 9 movement)

  Whiteprint: appendix_a_alternative / cover_first_global
  Dependencies: A2DyadicAdapter, TypedDyadicInfrastructure, SnapTubeProvenance
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.SnapTubeProvenance
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.H2_Migration_Adapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.NcoverEqualities
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.TDeltaGlobal

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
  (snapTube dyadicTubeToA2 dyadicTubeToA2_slope dyadicTubeToA2_intercept
   dyadicTube_parentCell)
open DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
  (sourceParent)
open DirecretisedFurstenbergEstimate.AppendixA.SnapTubeProvenance
  (sourceParent_slope_bound sourceParent_intercept_bound inParent_provenance_bound)
open DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter
  (floor_dyadic_bound_one floor_dyadic_bound_three dyadicTubeToA2_getDirV_ne_zero)
open DirecretisedFurstenbergEstimate.AppendixA.A2Helpers
  (coarse_slope_index_floor)
open DiscretisedFurstenbergEstimate.InductionConfigurations (refinementFactor)
open DyadicCardToNcover (toAffineLine)
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral (toAffineLine_injective)
open CoordinatePartition (swapLine swapLine_isometry)
open LemmaE (getDirV)

abbrev Plane := EuclideanPlane
abbrev FineTube := AffineLine
abbrev CoarseTube := AffineLine

/-! ========================================================================
   1. Core construction and subset lemma
   ======================================================================== -/

/-- Global coarse family from a fixed source family via canonical pipeline:
    ℓ ↦ snapTube n ℓ ↦ sourceParent hnm ↦ dyadicTubeToA2.

    This is T_Δ in OS notation: the set of all occupied coarse dyadic
    parent cells, converted to AffineLine form. -/
def T_Delta_global {n m : ℕ} (hnm : m ≤ n)
    (T_source : Finset FineTube) : Finset CoarseTube :=
  Finset.image (fun ℓ : FineTube =>
    dyadicTubeToA2 (sourceParent hnm (snapTube n ℓ))) T_source

/-- Basic subset: if every c ∈ C has provenance to some ℓ ∈ T_source
    via the canonical pipeline, then C ⊆ T_Delta_global. -/
lemma subset_T_Delta_global {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C : Finset CoarseTube}
    (h_prov : ∀ c ∈ C, ∃ ℓ ∈ T_source,
      c = dyadicTubeToA2 (sourceParent hnm (snapTube n ℓ))) :
    C ⊆ T_Delta_global hnm T_source := by
  intro c hc
  rcases h_prov c hc with ⟨ℓ, hℓ, rfl⟩
  exact Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩

/-- Convert QTTC-style per-point provenance to direct T_source provenance. -/
lemma qttc_provenance_to_source {n m : ℕ} {hnm : m ≤ n}
    {P' : Finset Plane} {T' : Plane → Finset FineTube}
    {T_source : Finset FineTube} {C' : Finset CoarseTube}
    (hT_sub : ∀ p ∈ P', T' p ⊆ T_source)
    (h_qttc : ∀ c ∈ C', ∃ p ∈ P', ∃ ℓ ∈ T' p,
      c = dyadicTubeToA2 (sourceParent hnm (snapTube n ℓ))) :
    ∀ c ∈ C', ∃ ℓ ∈ T_source,
      c = dyadicTubeToA2 (sourceParent hnm (snapTube n ℓ)) := by
  intro c hc
  rcases h_qttc c hc with ⟨p, hp, ℓ, hℓ, h_eq⟩
  have hℓ' : ℓ ∈ T_source := hT_sub p hp hℓ
  exact ⟨ℓ, hℓ', h_eq⟩

/-- Combined: QTTC provenance + T' p ⊆ T_source implies C' ⊆ T_Delta_global. -/
lemma qttc_C_sub_T_Delta_global {n m : ℕ} {hnm : m ≤ n}
    {P' : Finset Plane} {T' : Plane → Finset FineTube}
    {T_source : Finset FineTube} {C' : Finset CoarseTube}
    (hT_sub : ∀ p ∈ P', T' p ⊆ T_source)
    (h_qttc : ∀ c ∈ C', ∃ p ∈ P', ∃ ℓ ∈ T' p,
      c = dyadicTubeToA2 (sourceParent hnm (snapTube n ℓ))) :
    C' ⊆ T_Delta_global hnm T_source :=
  subset_T_Delta_global (qttc_provenance_to_source hT_sub h_qttc)

/-- C_global (biUnion of per-square C_Q) is subset of T_Delta_global
    if each C_Q has QTTC provenance to T_source. -/
lemma C_global_sub_T_Delta_global {n m : ℕ} {hnm : m ≤ n}
    {Δ : ℝ}
    {Qset : Finset (CoarseSquare Δ)}
    {C_Q : ∀ Q, Q ∈ Qset → Finset CoarseTube}
    {P_Q : ∀ Q, Q ∈ Qset → Finset Plane}
    {T_Q : ∀ Q, Q ∈ Qset → Plane → Finset FineTube}
    {T_source : Finset FineTube}
    (hT_sub : ∀ Q hQ p, p ∈ P_Q Q hQ → T_Q Q hQ p ⊆ T_source)
    (h_qttc : ∀ Q hQ c, c ∈ C_Q Q hQ →
      ∃ p ∈ P_Q Q hQ, ∃ ℓ ∈ T_Q Q hQ p,
        c = dyadicTubeToA2 (sourceParent hnm (snapTube n ℓ))) :
    (Qset.biUnion (fun Q => if h : Q ∈ Qset then C_Q Q h else ∅)) ⊆
      T_Delta_global hnm T_source := by
  intro c hc
  rcases Finset.mem_biUnion.mp hc with ⟨Q, hQ, hcQ⟩
  have h_c_in : c ∈ C_Q Q hQ := by simpa [hQ] using hcQ
  rcases h_qttc Q hQ c h_c_in with ⟨p, hp, ℓ, hℓ, h_eq⟩
  have hℓ' : ℓ ∈ T_source := hT_sub Q hQ p hp hℓ
  rw [h_eq]
  exact Finset.mem_image.mpr ⟨ℓ, hℓ', rfl⟩

/-! ========================================================================
   2. Glue lemmas: cardinality chain for C_global_A2 bound
   ======================================================================== -/

/-- Dyadic form of T_Delta_global: image of sourceParent ∘ snapTube on T_source. -/
def T_Delta_global_dyadic {n m : ℕ} (hnm : m ≤ n)
    (T_source : Finset FineTube) : Finset (DyadicTube m) :=
  Finset.image (fun ℓ : FineTube => sourceParent hnm (snapTube n ℓ)) T_source

/-- T_Delta_global is the affine image of T_Delta_global_dyadic. -/
lemma T_Delta_global_eq_image {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} :
    T_Delta_global hnm T_source =
      Finset.image (dyadicTubeToA2 (m := m)) (T_Delta_global_dyadic hnm T_source) := by
  ext c
  simp only [T_Delta_global, T_Delta_global_dyadic, Finset.mem_image]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    refine ⟨sourceParent hnm (snapTube n ℓ), ⟨ℓ, hℓ, rfl⟩, rfl⟩
  · rintro ⟨U, ⟨ℓ, hℓ, rfl⟩, rfl⟩
    exact ⟨ℓ, hℓ, rfl⟩

/-- dyadicTubeToA2 is injective (composition of injective toAffineLine and swapLine). -/
lemma dyadicTubeToA2_injective {m : ℕ} :
    Function.Injective (dyadicTubeToA2 (m := m)) := by
  have h1 : Function.Injective (toAffineLine : DyadicTube m → AffineLine) :=
    toAffineLine_injective
  have h2 : Function.Injective swapLine := swapLine_isometry.injective
  exact h2.comp h1

/-- Cardinality of affine T_Delta_global equals cardinality of dyadic T_Delta_global_dyadic. -/
lemma card_T_Delta_global_eq {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} :
    (T_Delta_global hnm T_source).card = (T_Delta_global_dyadic hnm T_source).card := by
  rw [T_Delta_global_eq_image]
  rw [Finset.card_image_of_injective _ (dyadicTubeToA2_injective (m := m))]

/-- Glue: C_global_A2 ⊆ T_Delta_global → |C_global_A2| ≤ |T_Delta_global_dyadic|. -/
lemma card_C_global_le_dyadic {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_sub : C_global_A2 ⊆ T_Delta_global hnm T_source) :
    C_global_A2.card ≤ (T_Delta_global_dyadic hnm T_source).card := by
  have h1 : C_global_A2.card ≤ (T_Delta_global hnm T_source).card :=
    Finset.card_le_card h_sub
  rw [card_T_Delta_global_eq] at h1
  exact h1

/-- Full cardinality chain:
    |C_global_A2| ≤ |T_Delta_global| = |T_Delta_global_dyadic| ≤ bound.
    The final inequality is supplied by juniper's Lemma 3 (coarse failure + packing). -/
lemma card_C_global_le_bound {n m : ℕ} {hnm : m ≤ n}
    {Δ s ε : ℝ}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_sub : C_global_A2 ⊆ T_Delta_global hnm T_source)
    (h_dyadic_bound : (T_Delta_global_dyadic hnm T_source).card ≤ Real.rpow Δ (-2 * s - 3 * ε)) :
    (C_global_A2.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε) := by
  have h1 : C_global_A2.card ≤ (T_Delta_global_dyadic hnm T_source).card :=
    card_C_global_le_dyadic h_sub
  have h2 : (C_global_A2.card : ℝ) ≤ ((T_Delta_global_dyadic hnm T_source).card : ℝ) := by
    exact_mod_cast h1
  exact le_trans h2 h_dyadic_bound

/-- T_Delta_global has distinct parent cells: no two distinct tubes share
    the same dyadic parent cell. Each tube is the A2 image of a unique
    DyadicTube, and parentCell recovers its (a,b) integer indices. -/
lemma T_Delta_global_distinct_parentCells {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} (hΔ_pos : 0 < dyadicDelta m) :
    ∀ (U1 : CoarseTube), U1 ∈ T_Delta_global hnm T_source →
      ∀ (U2 : CoarseTube), U2 ∈ T_Delta_global hnm T_source → U1 ≠ U2 →
        parentCell (dyadicDelta m) hΔ_pos U1 ≠ parentCell (dyadicDelta m) hΔ_pos U2 := by
  intro U1 hU1 U2 hU2 hne
  rw [T_Delta_global_eq_image] at hU1 hU2
  rcases Finset.mem_image.mp hU1 with ⟨V1, hV1, rfl⟩
  rcases Finset.mem_image.mp hU2 with ⟨V2, hV2, rfl⟩
  intro h_eq
  have h1 : parentCell (dyadicDelta m) hΔ_pos (dyadicTubeToA2 V1) = (V1.a, V1.b) :=
    dyadicTube_parentCell V1 hΔ_pos
  have h2 : parentCell (dyadicDelta m) hΔ_pos (dyadicTubeToA2 V2) = (V2.a, V2.b) :=
    dyadicTube_parentCell V2 hΔ_pos
  rw [h1, h2] at h_eq
  have hV_eq : V1 = V2 := by
    have h3 : V1.a = V2.a := congr_arg Prod.fst h_eq
    have h4 : V1.b = V2.b := congr_arg Prod.snd h_eq
    cases V1 <;> cases V2 <;> simp_all
  have h_contra : dyadicTubeToA2 V1 = dyadicTubeToA2 V2 := by rw [hV_eq]
  exact hne h_contra

/-- Any subset of T_Delta_global inherits the distinct parent cell property. -/
lemma C_global_distinct_parentCells {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_sub : C_global_A2 ⊆ T_Delta_global hnm T_source)
    (hΔ_pos : 0 < dyadicDelta m) :
    ∀ (U1 : CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        parentCell (dyadicDelta m) hΔ_pos U1 ≠ parentCell (dyadicDelta m) hΔ_pos U2 := by
  intro U1 hU1 U2 hU2 hne
  exact T_Delta_global_distinct_parentCells hΔ_pos U1 (h_sub hU1) U2 (h_sub hU2) hne

/-! ========================================================================
   3. SnapTube provenance bounds on T_Delta_global_dyadic

   Uses SnapTubeProvenance to establish slope/intercept bounds on every
   coarse parent in T_Delta_global_dyadic, given bounds on T_source.

   Key lemmas from SnapTubeProvenance:
   - sourceParent_slope_bound: fine strip bound → coarse |slope| ≤ 1
   - sourceParent_intercept_bound: fine |intercept| ≤ 3 → coarse |intercept| ≤ 3
   ======================================================================== -/

/-- If `-1 ≤ tubeSlope ℓ < 1`, then `snapTube n ℓ` satisfies the slope strip bound:
    `-(2^n) ≤ (snapTube n ℓ).a ∧ (snapTube n ℓ).a < 2^n`. -/
lemma snapTube_slope_strip_bound {n : ℕ} {ℓ : AffineLine}
    (h_slope_ge : -1 ≤ tubeSlope ℓ) (h_slope_lt : tubeSlope ℓ < 1) :
    -(2 ^ n : ℤ) ≤ (snapTube n ℓ).a ∧ (snapTube n ℓ).a < (2 ^ n : ℤ) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_int : (1 : ℝ) / δ = (2 ^ n : ℝ) := by
    simp [δ, dyadicDelta] <;> field_simp <;> ring_nf <;> norm_cast
  have h_a_def : (snapTube n ℓ).a = ⌊tubeSlope ℓ / δ⌋ := by
    simp [snapTube] <;> rfl
  rw [h_a_def]
  have h_div_ge : -(2 ^ n : ℝ) ≤ tubeSlope ℓ / δ := by
    have h1 : -(1 : ℝ) / δ ≤ tubeSlope ℓ / δ := by gcongr
    have h2 : -(1 : ℝ) / δ = -(2 ^ n : ℝ) := by
      rw [show -(1 : ℝ) / δ = -((1 : ℝ) / δ) by ring, h_int] <;> ring
    rw [h2] at h1; exact h1
  have h_div_lt : tubeSlope ℓ / δ < (2 ^ n : ℝ) := by
    have h1 : tubeSlope ℓ / δ < (1 : ℝ) / δ := by gcongr
    rw [h_int] at h1; exact h1
  have h_floor_ge : -(2 ^ n : ℤ) ≤ ⌊tubeSlope ℓ / δ⌋ := by
    rw [Int.le_floor]
    exact_mod_cast h_div_ge
  have h_floor_lt : ⌊tubeSlope ℓ / δ⌋ < (2 ^ n : ℤ) := by
    have h3 : ⌊tubeSlope ℓ / δ⌋ ≤ tubeSlope ℓ / δ := Int.floor_le _
    have h4 : (⌊tubeSlope ℓ / δ⌋ : ℝ) < (2 ^ n : ℝ) := by linarith
    exact_mod_cast h4
  exact ⟨h_floor_ge, h_floor_lt⟩

/-- If `|tubeSlope ℓ| ≤ 1`, then `|(snapTube n ℓ).slope| ≤ 1`.
    Uses floor_dyadic_bound_one. -/
lemma snapTube_slope_bound {n : ℕ} {ℓ : AffineLine}
    (h : |tubeSlope ℓ| ≤ 1) : |(snapTube n ℓ).slope| ≤ 1 := by
  have h_eq : (snapTube n ℓ).slope =
      (⌊tubeSlope ℓ / dyadicDelta n⌋ : ℝ) * dyadicDelta n := by
    simp [snapTube, DyadicTube.slope] <;> rfl
  rw [h_eq]
  exact floor_dyadic_bound_one (tubeSlope ℓ) h

/-- If `|tubeIntercept ℓ| ≤ 3`, then `|(snapTube n ℓ).intercept| ≤ 3`.
    Uses floor_dyadic_bound_three. -/
lemma snapTube_intercept_bound {n : ℕ} {ℓ : AffineLine}
    (h : |tubeIntercept ℓ| ≤ 3) : |(snapTube n ℓ).intercept| ≤ 3 := by
  have h_eq : (snapTube n ℓ).intercept =
      (⌊tubeIntercept ℓ / dyadicDelta n⌋ : ℝ) * dyadicDelta n := by
    simp [snapTube, DyadicTube.intercept] <;> rfl
  rw [h_eq]
  exact floor_dyadic_bound_three (tubeIntercept ℓ) h

/-- Non-strict slope bound: if fine DyadicTube T has `|T.slope| ≤ 1`,
    then coarse parent U has `|U.slope| ≤ 1`.

    Uses floor_dyadic_bound_one directly, which accepts non-strict bounds.
    This complements SnapTubeProvenance.sourceParent_slope_bound (which needs
    the strict strip bound) for cases where only `|slope| ≤ 1` is available. -/
lemma sourceParent_slope_bound_nonstrict {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U : DyadicTube m)
    (hU : sourceParent hnm T = U)
    (h_slope : |T.slope| ≤ 1) : |U.slope| ≤ 1 := by
  have h_floor : U.a = ⌊T.slope / dyadicDelta m⌋ := by
    have h1 : U.a = T.a / (refinementFactor n m : ℤ) := by
      rw [←hU] <;> rfl
    rw [h1, ←coarse_slope_index_floor hnm T]
  have h1 : U.slope = (U.a : ℝ) * dyadicDelta m := by
    simp [DyadicTube.slope] <;> ring
  rw [h1, h_floor]
  exact floor_dyadic_bound_one T.slope h_slope

/-- Slope bound on T_Delta_global_dyadic from non-strict slope bound on T_source.

    If every ℓ ∈ T_source has `|tubeSlope ℓ| ≤ 1`, then every
    U ∈ T_Delta_global_dyadic has `|U.slope| ≤ 1`.

    Uses snapTube_slope_bound + sourceParent_slope_bound_nonstrict.
    This matches the bounds provided by A1/QTTC. -/
lemma T_Delta_global_dyadic_slope_bound {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube}
    (h_slope : ∀ ℓ ∈ T_source, |tubeSlope ℓ| ≤ 1) :
    ∀ U ∈ T_Delta_global_dyadic hnm T_source, |U.slope| ≤ 1 := by
  intro U hU
  rcases Finset.mem_image.mp hU with ⟨ℓ, hℓ, rfl⟩
  let T_fine := snapTube n ℓ
  have h_fine_slope : |T_fine.slope| ≤ 1 :=
    snapTube_slope_bound (h_slope ℓ hℓ)
  exact sourceParent_slope_bound_nonstrict hnm T_fine (sourceParent hnm T_fine) rfl h_fine_slope

/-- Intercept bound on T_Delta_global_dyadic from intercept bound on T_source.

    If every ℓ ∈ T_source has `|tubeIntercept ℓ| ≤ 3`, then every
    U ∈ T_Delta_global_dyadic has `|U.intercept| ≤ 3`.

    Uses snapTube_intercept_bound + SnapTubeProvenance.sourceParent_intercept_bound. -/
lemma T_Delta_global_dyadic_intercept_bound {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube}
    (h_intercept : ∀ ℓ ∈ T_source, |tubeIntercept ℓ| ≤ 3) :
    ∀ U ∈ T_Delta_global_dyadic hnm T_source, |U.intercept| ≤ 3 := by
  intro U hU
  rcases Finset.mem_image.mp hU with ⟨ℓ, hℓ, rfl⟩
  let T_fine := snapTube n ℓ
  have h_fine_int : |T_fine.intercept| ≤ 3 :=
    snapTube_intercept_bound (h_intercept ℓ hℓ)
  exact sourceParent_intercept_bound hnm T_fine (sourceParent hnm T_fine) rfl h_fine_int

/-- Transfer dyadic slope/intercept/direction bounds to AffineLine representatives
    in `T_Delta_global`.

    Given dyadic bounds on `T_Delta_global_dyadic`, every `T ∈ T_Delta_global`
    has `getDirV y-component ≠ 0`, `|tubeSlope T| ≤ 1`, and `|tubeIntercept T| ≤ 3`.

    This discharges the `FrontEndComposition` slope-bound obligation
    `h_slope_bound_A7`. -/
lemma T_Delta_global_affine_bounds
    {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube}
    (h_slope_dyadic : ∀ U ∈ T_Delta_global_dyadic hnm T_source, |U.slope| ≤ 1)
    (h_intercept_dyadic : ∀ U ∈ T_Delta_global_dyadic hnm T_source, |U.intercept| ≤ 3) :
    ∀ (T : CoarseTube), T ∈ T_Delta_global hnm T_source →
      (getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3 := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨ℓ, hℓ, rfl⟩
  let U := sourceParent hnm (snapTube n ℓ)
  have hU_in : U ∈ T_Delta_global_dyadic hnm T_source :=
    Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
  have h_dir : (getDirV (dyadicTubeToA2 U)) 1 ≠ 0 :=
    dyadicTubeToA2_getDirV_ne_zero U
  have h_slope_eq : tubeSlope (dyadicTubeToA2 U) = U.slope :=
    dyadicTubeToA2_slope U
  have h_intercept_eq : tubeIntercept (dyadicTubeToA2 U) = U.intercept :=
    dyadicTubeToA2_intercept U
  exact ⟨h_dir,
    by rw [h_slope_eq]; exact h_slope_dyadic U hU_in,
    by rw [h_intercept_eq]; exact h_intercept_dyadic U hU_in⟩

/-! ========================================================================
   4. Orientation correction: T_standard = swapLine '' T_oriented

   Since dyadicTubeToA2 U = swapLine (toAffineLine U), the distance estimate
   InParent → dist < 10Δ is between ℓ and swapLine(toAffineLine U).
   Applying swapLine (isometry) gives dist(swapLine ℓ, toAffineLine U) < 10Δ.
   So the packing lemma is applied to T_standard, with Ncover unchanged.
   C_move = 17 for juniper's packing theorem (10Δ parent movement + 7δ_n Section 9 representative movement).
   ======================================================================== -/

/-- Standard orientation family: swapLine applied to T_oriented. -/
def T_standard (T_oriented : Set AffineLine) : Set AffineLine :=
  swapLine '' T_oriented

/-- Ncover is invariant under swapLine (involutive isometry). -/
lemma ncover_T_standard_eq {Δ : ℝ} {T_oriented : Set AffineLine} :
    Ncover Δ (T_standard T_oriented) = Ncover Δ T_oriented :=
  DirecretisedFurstenbergEstimate.FrontEndLemmas.NcoverEqualities.ncover_swapLine_eq

/-- Provenance to T_standard: if InParent Δ ℓ (dyadicTubeToA2 U) and all
    slope/intercept/direction bounds hold, then
    dist (swapLine ℓ) (toAffineLine U) < 10 * Δ.

    Uses H2Migration.inParent_dist_lt_tenDelta (dist < 10·Δ)
    and swapLine isometry. This is the form needed by the packing lemma
    on T_standard. (Full C_move = 17: this lemma provides the 10Δ parent component;
    the remaining 7δ_n comes from Section 9 representative movement.) -/
lemma provenance_to_T_standard
    {m : ℕ} {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (ℓ : AffineLine) (U : DyadicTube m)
    (h_inParent : InParent Δ hΔ_pos ℓ (dyadicTubeToA2 U))
    (hvℓ : (getDirV ℓ) 1 ≠ 0)
    (hvU : (getDirV (dyadicTubeToA2 U)) 1 ≠ 0)
    (haℓ : |tubeSlope ℓ| ≤ 1)
    (haU : |tubeSlope (dyadicTubeToA2 U)| ≤ 1)
    (hbℓ : |tubeIntercept ℓ| ≤ 3)
    (hbU : |tubeIntercept (dyadicTubeToA2 U)| ≤ 3) :
    dist (swapLine ℓ) (toAffineLine U) < 10 * Δ := by
  have h_dist : dist ℓ (dyadicTubeToA2 U) < 10 * Δ :=
    H2Migration.inParent_dist_lt_tenDelta Δ hΔ_pos ℓ (dyadicTubeToA2 U) h_inParent
      hvℓ hvU haℓ haU hbℓ hbU
  have h_swap : dist (swapLine ℓ) (swapLine (dyadicTubeToA2 U)) =
      dist ℓ (dyadicTubeToA2 U) :=
    swapLine_isometry.dist_eq ℓ (dyadicTubeToA2 U)
  have h_eq : swapLine (dyadicTubeToA2 U) = toAffineLine U := by
    simp [dyadicTubeToA2]
    <;> rw [CoordinatePartition.swapLine_invol]
  rw [h_eq] at h_swap
  rw [h_swap]
  exact h_dist

/-- Source-parent snap equivalence to InParent.

    sourceParent hnm (snapTube n ℓ) = U
      ↔ InParent Δ ℓ (dyadicTubeToA2 U)
    when Δ = dyadicDelta m. -/
lemma sourceParent_snap_iff
    {n m : ℕ} {hnm : m ≤ n} {Δ : ℝ} {hΔ_pos : 0 < Δ}
    (hΔ_eq : Δ = dyadicDelta m)
    (ℓ : AffineLine) (U : DyadicTube m) :
    sourceParent hnm (snapTube n ℓ) = U ↔
    InParent Δ hΔ_pos ℓ (dyadicTubeToA2 U) := by
  have h_tmp := A2DyadicAdapter.sourceParent_snap_iff_inParent hnm ℓ U (dyadicDelta_pos m)
  exact hΔ_eq ▸ h_tmp

/-! ========================================================================
   5. C_global_dyadic: exact dyadic preimage of C_global_A2

   Instead of bounding all of T_Delta_global_dyadic (which may contain
   extra coarse parents with looser bounds), we filter to exactly the
   dyadic tubes whose affine image is in C_global_A2.

   This preserves the tight QTTC bounds (slope ≤ 1, intercept ≤ 3,
   direction ≠ 0) because they hold for dyadicTubeToA2 U ∈ C_global_A2.
   ======================================================================== -/

/-- Exact dyadic preimage of C_global_A2 within T_Delta_global_dyadic. -/
def C_global_dyadic {n m : ℕ} (hnm : m ≤ n)
    (T_source : Finset FineTube) (C_global_A2 : Finset CoarseTube) :
    Finset (DyadicTube m) :=
  (T_Delta_global_dyadic hnm T_source).filter
    (fun U => dyadicTubeToA2 U ∈ C_global_A2)

/-- The affine image of C_global_dyadic equals C_global_A2, assuming
    C_global_A2 ⊆ T_Delta_global. -/
lemma image_C_global_dyadic_eq {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_sub : C_global_A2 ⊆ T_Delta_global hnm T_source) :
    Finset.image dyadicTubeToA2 (C_global_dyadic hnm T_source C_global_A2) =
      C_global_A2 := by
  ext c
  simp only [C_global_dyadic, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨U, ⟨_, hU2⟩, rfl⟩
    exact hU2
  · intro hc
    have h_in_TDelta : c ∈ T_Delta_global hnm T_source := h_sub hc
    rcases Finset.mem_image.mp h_in_TDelta with ⟨ℓ, hℓ, rfl⟩
    let U := sourceParent hnm (snapTube n ℓ)
    have hU_in_dyadic : U ∈ T_Delta_global_dyadic hnm T_source :=
      Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
    refine ⟨U, ⟨hU_in_dyadic, ?_⟩, rfl⟩
    exact hc

/-- Cardinality equality: |C_global_dyadic| = |C_global_A2|. -/
lemma card_C_global_dyadic_eq {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_sub : C_global_A2 ⊆ T_Delta_global hnm T_source) :
    (C_global_dyadic hnm T_source C_global_A2).card = C_global_A2.card := by
  rw [← Finset.card_image_of_injective _ dyadicTubeToA2_injective,
    image_C_global_dyadic_eq h_sub]

/-- Transfer slope bound from C_global_A2 to C_global_dyadic. -/
lemma C_global_dyadic_slope_bound {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_bound : ∀ c ∈ C_global_A2, |tubeSlope c| ≤ 1) :
    ∀ U ∈ C_global_dyadic hnm T_source C_global_A2, |U.slope| ≤ 1 := by
  intro U hU
  have h1 : dyadicTubeToA2 U ∈ C_global_A2 := (Finset.mem_filter.mp hU).2
  have h2 : tubeSlope (dyadicTubeToA2 U) = U.slope := dyadicTubeToA2_slope U
  have h3 : |tubeSlope (dyadicTubeToA2 U)| ≤ 1 := h_bound (dyadicTubeToA2 U) h1
  rwa [h2] at h3

/-- Transfer intercept bound from C_global_A2 to C_global_dyadic. -/
lemma C_global_dyadic_intercept_bound {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_bound : ∀ c ∈ C_global_A2, |tubeIntercept c| ≤ 3) :
    ∀ U ∈ C_global_dyadic hnm T_source C_global_A2, |U.intercept| ≤ 3 := by
  intro U hU
  have h1 : dyadicTubeToA2 U ∈ C_global_A2 := (Finset.mem_filter.mp hU).2
  have h2 : tubeIntercept (dyadicTubeToA2 U) = U.intercept := dyadicTubeToA2_intercept U
  have h3 : |tubeIntercept (dyadicTubeToA2 U)| ≤ 3 := h_bound (dyadicTubeToA2 U) h1
  rwa [h2] at h3

/-- Transfer direction bound from C_global_A2 to C_global_dyadic. -/
lemma C_global_dyadic_dir_bound {n m : ℕ} {hnm : m ≤ n}
    {T_source : Finset FineTube} {C_global_A2 : Finset CoarseTube}
    (h_bound : ∀ c ∈ C_global_A2, (getDirV c) 1 ≠ 0) :
    ∀ U ∈ C_global_dyadic hnm T_source C_global_A2,
      (getDirV (dyadicTubeToA2 U)) 1 ≠ 0 := by
  intro U hU
  have h1 : dyadicTubeToA2 U ∈ C_global_A2 := (Finset.mem_filter.mp hU).2
  exact h_bound (dyadicTubeToA2 U) h1

end DirecretisedFurstenbergEstimate.AppendixA.TDeltaGlobal
