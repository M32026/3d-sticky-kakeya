import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureNearbyRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiniteWeightedDegreeSelection
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Data.Nat.Log

/-!
# Balanced selection for pure CWA restriction

Given a tube family with pure CWA, apply simultaneous degree regularization
across a finite list of scales to obtain a balanced subfamily with polylog
degree uniformity and polylog cardinality retention.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Finset

/--
Apply simultaneous degree regularization across a finite list of scales.
-/
theorem pure_cwa_balanced_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (k : ℕ)
    (hk : 0 < k)
    (scales : Fin k → WZ2PaperRequestedScale delta)
    (hfine_nonempty : fine.Nonempty) :
    ∃ (selected : WZ2PaperPureTubeSubfamily fine)
      (degreeConstant : ENNReal)
      (retentionConstant : ENNReal),
      selected.family.Nonempty ∧
      degreeConstant ≠ ⊤ ∧
      retentionConstant ≠ ⊤ ∧
      (fine.enncard ≤ retentionConstant * selected.family.enncard) ∧
      (∀ i : Fin k,
        let nearby := Classical.choice (ambient.2.2.2 (scales i))
        ∀ first second : Fin nearby.scaleData.coarse.card,
          0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
                 fun source => nearby.scaleData.cover.parent (selected.embedding source) = first).card →
          0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
                 fun source => nearby.scaleData.cover.parent (selected.embedding source) = second).card →
          (((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source => nearby.scaleData.cover.parent (selected.embedding source) = first).card : ENNReal) ≤
            degreeConstant *
            (((Finset.univ : Finset (Fin selected.family.card)).filter
                fun source => nearby.scaleData.cover.parent (selected.embedding source) = second).card : ENNReal)) := by
  let coverData : ∀ i, WZ2PaperPureNearbyScaleCoverData fine (scales i) ambientConstant :=
    fun i => Classical.choice (ambient.2.2.2 (scales i))
  let coarseCard : Fin k → ℕ := fun i => (coverData i).scaleData.coarse.card
  let Vertex : Fin k → Type := fun i => Fin (coarseCard i)
  let parent : ∀ i, Fin fine.card → Vertex i :=
    fun i source => (coverData i).scaleData.cover.parent source
  let weight : Fin fine.card → ENNReal := fun _ => 1
  have h_main : Nonempty (WZ2FiniteWeightedDegreeSelectionData k Vertex parent weight) :=
    wz2_finite_weighted_degree_selection k Vertex parent weight hk
  rcases h_main with ⟨data⟩
  let selectedFinset := data.selected
  let selected := WZ2PaperPureTubeSubfamily.fromFinset fine selectedFinset
  let N := Fintype.card (Fin fine.card)
  let degreeConstant : ENNReal :=
    16 * (k : ENNReal) * (Nat.log 2 (2 * N) + 1 : ENNReal) ^ k
  let retentionConstant : ENNReal :=
    8 * (Nat.log 2 (2 * N) + 1 : ENNReal) ^ (k + 1)
  have hN_pos : 0 < N := by
    simpa [N, Fintype.card_fin, Kakeya.Streamlined.TubeFamily.Nonempty] using
      hfine_nonempty
  have h_ret_weight : (∑ index : Fin fine.card, weight index) ≤
      (8 : ENNReal) * (Nat.log 2 (2 * N) + 1 : ENNReal) ^ (k + 1) *
        ∑ index ∈ selectedFinset, weight index :=
    data.retained_weight
  have h_selected_nonempty : selectedFinset.Nonempty := by
    by_contra h
    have h' : selectedFinset = ∅ := by simpa using h
    have h_empty : (∑ index ∈ selectedFinset, weight index) = 0 := by
      rw [h'] <;> simp
    rw [h_empty] at h_ret_weight
    have h_fine_card_pos : 0 < fine.card := by
      simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hfine_nonempty
    have h_total_pos : 0 < (∑ index : Fin fine.card, weight index) := by
      have h_eq : (∑ index : Fin fine.card, weight index) = (fine.card : ENNReal) := by
        simp [weight, Finset.sum_const] <;> norm_cast
      rw [h_eq]
      exact_mod_cast h_fine_card_pos
    have h_contra : (∑ index : Fin fine.card, weight index) ≤ 0 := by
      simpa using h_ret_weight
    exact not_le.mpr h_total_pos h_contra
  have h_card_pos : 0 < selected.family.card := by
    change 0 < selectedFinset.card
    exact Finset.Nonempty.card_pos h_selected_nonempty
  have h_selected_family_nonempty : selected.family.Nonempty := by
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using h_card_pos
  have h_degree_top : degreeConstant ≠ ⊤ := ENNReal.coe_ne_top
  have h_retention_top : retentionConstant ≠ ⊤ := ENNReal.coe_ne_top
  have h_retention : fine.enncard ≤ retentionConstant * selected.family.enncard := by
    have h1 : (∑ index : Fin fine.card, weight index) = (fine.card : ENNReal) := by
      simp [weight, Finset.sum_const] <;> norm_cast
    have h2 : (∑ index ∈ selectedFinset, weight index) =
        (selected.family.card : ENNReal) := by
      simp [weight, Finset.sum_const] <;> norm_cast
    rw [h1, h2] at h_ret_weight
    exact h_ret_weight
  have h_degree_uniform : ∀ i : Fin k,
      ∀ first second : Fin (coverData i).scaleData.coarse.card,
        0 < (selectedFinset.filter fun index => parent i index = first).card →
        0 < (selectedFinset.filter fun index => parent i index = second).card →
        ((selectedFinset.filter fun index => parent i index = first).card : ENNReal) ≤
          degreeConstant *
            ((selectedFinset.filter fun index => parent i index = second).card : ENNReal) := by
    intro i first second h1 h2
    exact data.degree_uniform i first second h1 h2
  have h_emb_mem : ∀ source : Fin selected.family.card,
      selected.embedding source ∈ selectedFinset := by
    intro source
    exact Finset.orderEmbOfFin_mem selectedFinset rfl source
  have h_image_univ :
      Finset.image selected.embedding
          (Finset.univ : Finset (Fin selected.family.card)) =
        selectedFinset := by
    have h_sub : Finset.image selected.embedding
        (Finset.univ : Finset (Fin selected.family.card)) ⊆ selectedFinset := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨source, _, rfl⟩
      exact h_emb_mem source
    have h_card :
        (Finset.image selected.embedding
          (Finset.univ : Finset (Fin selected.family.card))).card =
            selectedFinset.card := by
      rw [Finset.card_image_of_injective _ selected.embedding.injective]
      have h1 :
          (Finset.univ :
            Finset (Fin selected.family.card)).card =
              selected.family.card := by
        simp
      rw [h1]
      rfl
    exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_card])
  have h_surj : ∀ y : Fin fine.card, y ∈ selectedFinset →
      ∃ source : Fin selected.family.card, selected.embedding source = y := by
    intro y hy
    have h_in_image : y ∈ Finset.image selected.embedding
        (Finset.univ : Finset (Fin selected.family.card)) := by
      rw [h_image_univ]
      exact hy
    rcases Finset.mem_image.mp h_in_image with ⟨source, _, rfl⟩
    exact ⟨source, rfl⟩
  have h_filter_card : ∀ (i : Fin k)
      (first : Fin (coverData i).scaleData.coarse.card),
      (selectedFinset.filter fun index => parent i index = first).card =
      ((Finset.univ : Finset (Fin selected.family.card)).filter
         fun source => parent i (selected.embedding source) = first).card := by
    intro i first
    let s1 := selectedFinset.filter fun index => parent i index = first
    let s2 := (Finset.univ : Finset (Fin selected.family.card)).filter
      fun source => parent i (selected.embedding source) = first
    have h_image : Finset.image selected.embedding s2 = s1 := by
      ext y
      simp only [s1, s2, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨h_emb_mem source, hsource⟩
      · rintro ⟨hy1, hy2⟩
        rcases h_surj y hy1 with ⟨source, h_eq⟩
        refine ⟨source, ?_, h_eq⟩
        rwa [h_eq]
    have h : (Finset.image selected.embedding s2).card = s2.card :=
      Finset.card_image_of_injective s2 selected.embedding.injective
    have h_final : s1.card = s2.card := by
      rw [← h_image, h]
    exact h_final
  refine ⟨selected, degreeConstant, retentionConstant,
    h_selected_family_nonempty, h_degree_top, h_retention_top,
    h_retention, ?_⟩
  intro i
  dsimp only
  intro first second h1 h2
  have h1' : 0 < (selectedFinset.filter fun index =>
      parent i index = first).card := by
    rw [h_filter_card i first]
    exact h1
  have h2' : 0 < (selectedFinset.filter fun index =>
      parent i index = second).card := by
    rw [h_filter_card i second]
    exact h2
  have h_main' := h_degree_uniform i first second h1' h2'
  rw [h_filter_card i first, h_filter_card i second] at h_main'
  exact h_main'

/--
Restrict pure CWA to a subfamily using a finite scale schedule with a
quantified rounding factor.
-/
theorem pure_cwa_restrict_with_rounding
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (selectedNonempty : selected.family.Nonempty)
    (k : ℕ) (hk : 0 < k)
    (scales : Fin k → WZ2PaperRequestedScale delta)
    (degreeConstant retentionConstant weight : ENNReal)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hretentionTop : retentionConstant ≠ ⊤)
    (hselectedTop : degreeConstant ≠ ⊤)
    (hglobalRetention :
      weight * fine.enncard ≤ retentionConstant * selected.family.enncard)
    (hDegreeUniform : ∀ i : Fin k,
      let nearby := Classical.choice (ambient.2.2.2 (scales i))
      ∀ first second : Fin nearby.scaleData.coarse.card,
        0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
               fun source =>
                 nearby.scaleData.cover.parent (selected.embedding source) = first).card →
        0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
               fun source =>
                 nearby.scaleData.cover.parent (selected.embedding source) = second).card →
        (((Finset.univ : Finset (Fin selected.family.card)).filter
            fun source =>
              nearby.scaleData.cover.parent (selected.embedding source) = first).card : ENNReal) ≤
          degreeConstant *
          (((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                nearby.scaleData.cover.parent (selected.embedding source) = second).card : ENNReal))
    (hR_pos : (0 : ENNReal) < R)
    (hR_top : R ≠ ⊤)
    (hR_one : (1 : ENNReal) ≤ R)
    (h_rounding : ∀ rho₀ : WZ2PaperRequestedScale delta,
      ∃ i : Fin k,
        rho₀.1 ≤ (scales i).1 ∧
        ENNReal.ofReal (scales i).1 < R * ENNReal.ofReal rho₀.1)
    (h_R_ambient_le_output : R * ambientConstant ≤ outputConstant)
    (houtputTop : outputConstant ≠ ⊤)
    (h_output_ge_restricted :
      wz2PaperPureNearbyRestrictionConstant
        ambientConstant weight degreeConstant retentionConstant ≤ outputConstant) :
    WZ2PaperPureCWAAtNearbyScales selected.family outputConstant := by
  have hdelta_pos : 0 < delta := ambient.1
  have h_ambient_le_output : ambientConstant ≤ outputConstant := by
    have h2 : ambientConstant ≤ R * ambientConstant := by
      have h4 : (1 : ENNReal) * ambientConstant ≤ R * ambientConstant := by
        gcongr
      simpa using h4
    exact h2.trans h_R_ambient_le_output
  have h_output_one : (1 : ENNReal) ≤ outputConstant :=
    ambient.2.1.1.trans h_ambient_le_output
  have h_output_finite : WZ2PaperFiniteErrorConstant outputConstant :=
    ⟨h_output_one, houtputTop⟩
  have h_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct selected.family :=
    ambient.2.2.1.subfamily selected
  have h_main : ∀ rho₀ : WZ2PaperRequestedScale delta,
      Nonempty (WZ2PaperPureNearbyScaleCoverData
        selected.family rho₀ outputConstant) := by
    intro rho₀
    rcases h_rounding rho₀ with ⟨i, hle, hlt⟩
    let scheduledRequested := scales i
    let nearbyScheduled :=
      Classical.choice (ambient.2.2.2 scheduledRequested)
    let scaleData := nearbyScheduled.scaleData
    let selectedCoarse := scaleData.cover.hitParentSubfamily selected
    have hCoarseNonempty : selectedCoarse.family.Nonempty :=
      scaleData.cover.hitParentSubfamily_nonempty selected selectedNonempty
    let restrictedCover := scaleData.cover.restrictToHitParents selected
    have hUniform : WZ2PaperPureFullFibersAreCUniform
        selected.family selectedCoarse.family degreeConstant :=
      scaleData.cover.restrictToHitParents_fullFiber_uniform_of_subfamily
        scaleData.rho_pos.le selected degreeConstant (hDegreeUniform i)
    let restrictedScaleData := scaleData.restrictOfWeightedRetention
      selected selectedCoarse hCoarseNonempty restrictedCover
      hweightZero hweightTop hglobalRetention hUniform
    let restrictedConstant :=
      max degreeConstant
        (weight⁻¹ *
          (ambientConstant * retentionConstant * degreeConstant) *
          ambientConstant)
    have h_restricted_le : restrictedConstant ≤ outputConstant := by
      have h : restrictedConstant ≤
          wz2PaperPureNearbyRestrictionConstant
            ambientConstant weight degreeConstant retentionConstant :=
        le_max_right _ _
      exact h.trans h_output_ge_restricted
    let weakenedScaleData := restrictedScaleData.mono h_restricted_le
    have h_requested_le : rho₀.1 ≤ nearbyScheduled.rho := by
      calc
        rho₀.1 ≤ (scales i).1 := hle
        _ ≤ nearbyScheduled.rho := nearbyScheduled.requested_le
    have h_ambient_lt :
        ENNReal.ofReal nearbyScheduled.rho <
          ambientConstant * ENNReal.ofReal (scales i).1 :=
      nearbyScheduled.within_factor
    have h11 :
        ambientConstant * ENNReal.ofReal (scales i).1 ≤
          R * ambientConstant * ENNReal.ofReal rho₀.1 := by
      have h12 :
          ENNReal.ofReal (scales i).1 ≤ R * ENNReal.ofReal rho₀.1 :=
        le_of_lt hlt
      calc
        ambientConstant * ENNReal.ofReal (scales i).1
            ≤ ambientConstant * (R * ENNReal.ofReal rho₀.1) := by
              gcongr
        _ = R * ambientConstant * ENNReal.ofReal rho₀.1 := by ring
    have h13 :
        R * ambientConstant * ENNReal.ofReal rho₀.1 ≤
          outputConstant * ENNReal.ofReal rho₀.1 :=
      mul_le_mul_of_nonneg_right h_R_ambient_le_output (by positivity)
    have h_within_factor :
        ENNReal.ofReal nearbyScheduled.rho <
          outputConstant * ENNReal.ofReal rho₀.1 :=
      h_ambient_lt.trans_le (h11.trans h13)
    exact ⟨{
      rho := nearbyScheduled.rho
      requested_le := h_requested_le
      within_factor := h_within_factor
      scaleData := weakenedScaleData
    }⟩
  exact ⟨hdelta_pos, h_output_finite, h_distinct, h_main⟩

end Kakeya.Assouad

end
