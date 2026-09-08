import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanConvexWolff
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Frostman transfer from full A-fiber to strict subfiber

Given a Frostman bound on a full A-fiber and a strict subfiber retaining at
least a fraction `α` of the mass, transfer the Frostman bound to the strict
subfiber with constant degraded by `1/α`.

This is used in the GWZ→WZ2 conversion to obtain CWB per rescaled fiber
after filtering substantial tiles.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory

attribute [local instance] Classical.propDecidable

/--
If `strict` is a subfamily of `full` (via injection `f`) and `strict` retains
at least a fraction `α` of `full`'s mass, then a Frostman bound on `full`
transfers to `strict` with constant `C'` satisfying `C ≤ C' * α`.
-/
lemma frostman_transfer_to_strict_subfiber
    {full strict : Kakeya.Streamlined.BodyFamily}
    (f : Fin strict.card ↪ Fin full.card)
    (h_eq : ∀ i, strict.body i = full.body (f i))
    (α C C' : ENNReal)
    (hC : C ≤ C' * α)
    (h_mass_ratio : strict.mass ≥ α * full.mass)
    (ACarrier : Set Point3)
    (hfrost_full : ∀ (K : Set Point3), Convex ℝ K → K ⊆ ACarrier →
      full.containedMass K * volume ACarrier ≤ C * full.mass * volume K)
    :
    ∀ (K : Set Point3), Convex ℝ K → K ⊆ ACarrier →
      strict.containedMass K * volume ACarrier ≤
      C' * strict.mass * volume K := by
  have h_contained_mass_mono : ∀ (K : Set Point3),
      strict.containedMass K ≤ full.containedMass K := by
    intro K
    let S_strict := strict.containedIndices K
    let S_full := full.containedIndices K
    have h1 : ∀ i ∈ S_strict, f i ∈ S_full := by
      intro i hi
      have h_i_in : (strict.body i).carrier ⊆ K := by
        have h_iff :
            i ∈ strict.containedIndices K ↔
              (strict.body i).carrier ⊆ K :=
          Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff
        exact h_iff.mp hi
      have h_eq_body : (full.body (f i)).carrier ⊆ K := by
        rw [← h_eq i] <;> exact h_i_in
      have h_iff2 :
          f i ∈ full.containedIndices K ↔
            (full.body (f i)).carrier ⊆ K :=
        Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff
      exact h_iff2.mpr h_eq_body
    have h2 : Finset.image f S_strict ⊆ S_full := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      exact h1 i hi
    have h3 : strict.containedMass K = ∑ i ∈ S_strict, (strict.body i).volume := by rfl
    have h4 : ∑ i ∈ S_strict, (strict.body i).volume =
        ∑ j ∈ Finset.image f S_strict, (full.body j).volume := by
      rw [Finset.sum_image (show Set.InjOn f S_strict from fun _ _ _ _ h => f.inj' h)]
      · apply Finset.sum_congr rfl
        intro i _
        exact congr_arg (fun (b : Kakeya.Streamlined.Body) => b.volume) (h_eq i)
    rw [h3, h4]
    exact Finset.sum_le_sum_of_subset_of_nonneg h2 (fun _ _ _ => by positivity)
  intro K hK hK_sub
  calc
    strict.containedMass K * volume ACarrier
      ≤ full.containedMass K * volume ACarrier := by
        gcongr
        <;> exact h_contained_mass_mono K
    _ ≤ C * full.mass * volume K := hfrost_full K hK hK_sub
    _ ≤ (C' * α) * full.mass * volume K := by
        gcongr
        <;> exact hC
    _ = C' * (α * full.mass) * volume K := by ring
    _ ≤ C' * strict.mass * volume K := by
        gcongr
        <;> exact h_mass_ratio

/--
Transfer a Convex-Wolff bound between body families that are equivalent
up to reindexing.
-/
lemma cwb_transfer_reindex
    {F1 F2 : Kakeya.Streamlined.BodyFamily}
    (e : Fin F1.card ≃ Fin F2.card)
    (h_eq : ∀ i, F1.body i = F2.body (e i))
    {C : ENNReal}
    (h : WZ2PaperBodyConvexWolffBound F1 C)
    : WZ2PaperBodyConvexWolffBound F2 C := by
  intro K hK
  have h_goal : F1.containedCount K ≤ C * volume K * F1.enncard := h K hK
  have h_indices : Finset.image e (F1.containedIndices K) = F2.containedIndices K := by
    ext j
    simp only [Finset.mem_image, Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have h5 : (F2.body (e i)).carrier ⊆ K := by
        rw [← h_eq i] <;> exact hi
      exact h5
    · intro hj
      refine ⟨e.symm j, ?_, by simp⟩
      have h5 : F1.body (e.symm j) = F2.body j := by
        rw [h_eq (e.symm j)] <;> simp
      rw [h5] <;> exact hj
  have h_count : F1.containedCount K = F2.containedCount K := by
    simp only [Kakeya.Streamlined.BodyFamily.containedCount]
    rw [← Finset.card_image_of_injective _ e.injective, h_indices]
  have h_enncard : F1.enncard = F2.enncard := by
    have h_card : F1.card = F2.card := by
      have h := Fintype.card_congr e
      simpa using h
    simp [Kakeya.Streamlined.BodyFamily.enncard, h_card]
  rw [h_count, h_enncard] at h_goal
  exact h_goal

/--
Build `WZ2PaperPureUnitRescaledFullFiberData` for the full fiber of a coarse tile
by transferring Frostman from the GWZ A-fiber and applying the John-rescaled
convex-Wolff conversion.

The `strict` subfamily must be the full fiber of the tile. The output CWB
constant is `27 * C'`.
-/
def fullfiber_rescaled_cwb
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hA : 1 ≤ A)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (full_strict : Kakeya.Streamlined.TubeSubfamily fine)
    (strict : Kakeya.Streamlined.TubeSubfamily fine)
    (f : Fin strict.family.card ↪ Fin full_strict.family.card)
    (h_eq : ∀ i, strict.embedding i = full_strict.embedding (f i))
    (hfiber_strict : ∀ i : Fin strict.family.card,
      (strict.family.tube i).carrier ⊆
        wz2PaperCenteredDilatedCarrier A (coarse.tube parent))
    (α C C' : ENNReal)
    (hC : C ≤ C' * α)
    (h_mass_ratio : strict.family.toBodyFamily.mass ≥
      α * full_strict.family.toBodyFamily.mass)
    (hfrost_full : ∀ (K : Set Point3), Convex ℝ K →
      K ⊆ wz2PaperCenteredDilatedCarrier A (coarse.tube parent) →
        full_strict.family.toBodyFamily.containedMass K *
          volume (wz2PaperCenteredDilatedCarrier A (coarse.tube parent)) ≤
        C * full_strict.family.toBodyFamily.mass * volume K)
    (normalization : WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    (e : Fin strict.family.card ≃
      Fin (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card)
    (h_body_match : ∀ i, strict.family.tube i =
      fine.tube ((wz2PaperOrdinaryFullFiberIndexEquiv parent) (e i)).val)
    : WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse) parent (27 * C') := by
  let ACarrier := wz2PaperCenteredDilatedCarrier A (coarse.tube parent)
  let f' : Fin strict.family.toBodyFamily.card ↪ Fin full_strict.family.toBodyFamily.card := f
  have h_eq' : ∀ i, strict.family.toBodyFamily.body i =
      full_strict.family.toBodyFamily.body (f' i) := by
    intro i
    have h1 : strict.family.toBodyFamily.body i =
        Kakeya.Streamlined.tubeBody (strict.family.tube i) := by rfl
    have h2 : full_strict.family.toBodyFamily.body (f' i) =
        Kakeya.Streamlined.tubeBody (full_strict.family.tube (f' i)) := by rfl
    rw [h1, h2]
    have h3 : strict.family.tube i = fine.tube (strict.embedding i) := strict.tube_eq i
    have h4 : full_strict.family.tube (f' i) = fine.tube (full_strict.embedding (f' i)) :=
      full_strict.tube_eq (f' i)
    rw [h3, h4, h_eq i] <;> rfl
  have hfrost_strict := frostman_transfer_to_strict_subfiber
    (f := f') (h_eq := h_eq') α C C' hC h_mass_ratio ACarrier hfrost_full
  let inlineFamily : Kakeya.Streamlined.BodyFamily :=
    { card := strict.family.card
      body := fun i =>
        ⟨normalization.map '' (strict.family.tube i).carrier⟩ }
  let expectedFamily := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := fine) (coarse := coarse) parent normalization
  have h_cwb_inline : WZ2PaperBodyConvexWolffBound inlineFamily (27 * C') :=
    gwz_frostman_to_john_rescaled_convex_wolff
      hdelta hrho hA parent strict hfiber_strict normalization C' hfrost_strict
  have h_family_eq : ∀ i, inlineFamily.body i = expectedFamily.body (e i) := by
    intro i
    simp [inlineFamily, expectedFamily, h_body_match i]
    <;> rfl
  have h_cwb_expected : WZ2PaperBodyConvexWolffBound expectedFamily (27 * C') :=
    cwb_transfer_reindex e h_family_eq h_cwb_inline
  exact
    { normalization := normalization
      convex_wolff := h_cwb_expected }

end Kakeya.Assouad

end
