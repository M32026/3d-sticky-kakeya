import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.MultiplicityPigeonholing
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Core construction: multiplicity regularization for the hairbrush core

Integrates dyadic pigeonholing, band restriction, and alternating pruning
to produce a multiplicity-regularized subfamily with tube mass retention.

This file is self-contained (includes helper definitions from
AlternatingPruning.lean and FullAlternatingPruning.lean).
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Assouad

-- ============================================================================
-- Shared definitions
-- ============================================================================

/-- Shaded multiplicity at a point. -/
def coreShadedMultiplicity {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (x : Point3) : ℕ :=
  letI : DecidablePred (fun T : Kakeya.DeltaTube δ => x ∈ Y.carrier T) :=
    fun T => Classical.propDecidable (x ∈ Y.carrier T)
  (F.filter (fun T => x ∈ Y.carrier T)).card

/-- Measurability of shaded multiplicity. -/
lemma measurable_coreShadedMultiplicity {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) :
    Measurable (coreShadedMultiplicity Y) := by
  classical
  have h1 : coreShadedMultiplicity Y = fun x =>
      ∑ T ∈ F, if x ∈ Y.carrier T then (1 : ℕ) else 0 := by
    funext x
    have h2 : ∑ T ∈ F, (if x ∈ Y.carrier T then (1 : ℕ) else 0) =
        (F.filter (fun T => x ∈ Y.carrier T)).card := by
      rw [Finset.sum_ite]; simp
    dsimp only [coreShadedMultiplicity]
    exact h2.symm
  rw [h1]
  apply Finset.measurable_sum F
  intro T hT
  exact Measurable.ite (Y.measurable_carrier hT) measurable_const measurable_const

/-- Restrict a shading to a subfamily. -/
def coreRestrictFamily {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) {F2 : Kakeya.TubeFamily δ} (h : F2 ⊆ F) :
    Kakeya.Shading F2 :=
  { carrier := Y.carrier
    measurable_carrier := fun _ hT => Y.measurable_carrier (h hT)
    subset_tube := fun _ hT => Y.subset_tube (h hT) }

/-- Prune tubes below mass threshold. -/
def corePruneTubes {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y_orig Y_cur : Kakeya.Shading F) (alphaTube : ENNReal) :
    Kakeya.TubeFamily δ :=
  F.filter (fun T => alphaTube * volume (Y_orig.carrier T) ≤ volume (Y_cur.carrier T))

/-- Total shaded mass. -/
def coreTotalMass {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) : ENNReal :=
  ∑ T ∈ F, volume (Y.carrier T)

/-- Dyadic multiplicity band [2^k, 2^(k+1)). -/
def coreDyadicBand {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (k : ℕ) : Set Point3 :=
  {x | (2 : ℕ)^k ≤ coreShadedMultiplicity Y x ∧
       coreShadedMultiplicity Y x < (2 : ℕ)^(k+1)}

/-- Dyadic bands are measurable. -/
lemma measurableSet_coreDyadicBand {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (k : ℕ) :
    MeasurableSet (coreDyadicBand Y k) := by
  have hmf : Measurable (coreShadedMultiplicity Y) :=
    measurable_coreShadedMultiplicity Y
  have h1 : MeasurableSet (Set.Ici ((2 : ℕ)^k)) := by simp
  have h2 : MeasurableSet (Set.Iio ((2 : ℕ)^(k+1))) := by simp
  have h1' : MeasurableSet (coreShadedMultiplicity Y ⁻¹' (Set.Ici ((2 : ℕ)^k))) :=
    h1.preimage hmf
  have h2' : MeasurableSet (coreShadedMultiplicity Y ⁻¹' (Set.Iio ((2 : ℕ)^(k+1)))) :=
    h2.preimage hmf
  have hband : coreDyadicBand Y k =
      (coreShadedMultiplicity Y ⁻¹' (Set.Ici ((2 : ℕ)^k))) ∩
      (coreShadedMultiplicity Y ⁻¹' (Set.Iio ((2 : ℕ)^(k+1)))) := by
    ext x; simp [coreDyadicBand]
  rw [hband]
  exact h1'.inter h2'

/-- Distinct dyadic bands are disjoint. -/
lemma coreDyadicBands_disjoint {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) {k l : ℕ} (h : k ≠ l) :
    Disjoint (coreDyadicBand Y k) (coreDyadicBand Y l) := by
  have h_main : ∀ {a b : ℕ}, a < b →
      Disjoint (coreDyadicBand Y a) (coreDyadicBand Y b) := by
    intro a b hab
    have h3 : (2 : ℕ)^(a+1) ≤ (2 : ℕ)^b := by
      have h4 : a + 1 ≤ b := by omega
      gcongr; norm_num
    simp only [Set.disjoint_left, coreDyadicBand]
    intro p hpa
    have h4 : coreShadedMultiplicity Y p < (2 : ℕ)^(a+1) := hpa.2
    intro hpb
    have h5 : (2 : ℕ)^b ≤ coreShadedMultiplicity Y p := hpb.1
    have h_contra : coreShadedMultiplicity Y p < coreShadedMultiplicity Y p := by
      calc
        coreShadedMultiplicity Y p < (2 : ℕ)^(a+1) := h4
        _ ≤ (2 : ℕ)^b := h3
        _ ≤ coreShadedMultiplicity Y p := h5
    exact lt_irrefl _ h_contra
  by_cases hkl : k < l
  · exact h_main hkl
  · by_cases hlk : l < k
    · exact (h_main hlk).symm
    · have h_eq : k = l := by omega
      exfalso; exact h h_eq

/-- Dyadic bands k=0,...,K cover Y.union when F.card < 2^(K+1). -/
lemma coreDyadicBands_cover {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) {K : ℕ} (hK : F.card < (2 : ℕ)^(K+1)) :
    Y.union ⊆ ⋃ k ∈ Finset.range (K+1), coreDyadicBand Y k := by
  intro p hp
  letI : DecidablePred (fun T : Kakeya.DeltaTube δ => p ∈ Y.carrier T) :=
    fun T => Classical.propDecidable (p ∈ Y.carrier T)
  have hmult_pos : 0 < coreShadedMultiplicity Y p := by
    rcases hp with ⟨T, hT, hpT⟩
    have h1 : T ∈ F.filter (fun T => p ∈ Y.carrier T) := by
      simp only [Finset.mem_filter]; exact ⟨hT, hpT⟩
    exact Finset.card_pos.mpr ⟨T, h1⟩
  have hmult_le : coreShadedMultiplicity Y p ≤ F.card := by
    apply Finset.card_le_card
    intro T hT
    exact (Finset.mem_filter.mp hT).1
  have h_lt : coreShadedMultiplicity Y p < (2 : ℕ)^(K+1) := by omega
  rcases exists_dyadic_interval (coreShadedMultiplicity Y p) hmult_pos K h_lt with ⟨k, hk, h3, h4⟩
  have h5 : k ∈ Finset.range (K+1) := by
    simp only [Finset.mem_range]; omega
  exact Set.mem_iUnion₂.mpr ⟨k, h5, ⟨h3, h4⟩⟩

/-- Total band masses sum to total shaded mass. -/
lemma coreDyadicBandMass_sum {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) {K : ℕ} (hK : F.card < (2 : ℕ)^(K+1)) :
    ∑ k ∈ Finset.range (K+1),
      (∑ T ∈ F, volume (Y.carrier T ∩ coreDyadicBand Y k)) =
    coreTotalMass Y := by
  have h_partition : ∀ (T : Kakeya.DeltaTube δ), T ∈ F →
      ∑ k ∈ Finset.range (K+1), volume (Y.carrier T ∩ coreDyadicBand Y k) =
      volume (Y.carrier T) := by
    intro T hT
    have h_cover : Y.carrier T ⊆ ⋃ k ∈ Finset.range (K+1), coreDyadicBand Y k := by
      have h1 : Y.carrier T ⊆ Y.union := by
        intro x hx; exact ⟨T, hT, hx⟩
      exact h1.trans (coreDyadicBands_cover Y hK)
    let f : ℕ → Set Point3 := fun k => Y.carrier T ∩ coreDyadicBand Y k
    have h_union : (Y.carrier T) = ⋃ k ∈ Finset.range (K+1), f k := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, f]
      constructor
      · intro hx
        have h2 : x ∈ ⋃ k ∈ Finset.range (K+1), coreDyadicBand Y k := h_cover hx
        rcases Set.mem_iUnion₂.mp h2 with ⟨k, hk, h3⟩
        exact ⟨k, hk, hx, h3⟩
      · rintro ⟨k, _, hx, _⟩; exact hx
    have hd : Set.PairwiseDisjoint (Finset.range (K+1) : Set ℕ) f := by
      intro k _ l _ hne
      exact (coreDyadicBands_disjoint Y hne).mono Set.inter_subset_right Set.inter_subset_right
    have hm : ∀ k ∈ Finset.range (K+1), MeasurableSet (f k) := by
      intro k _
      exact (Y.measurable_carrier hT).inter (measurableSet_coreDyadicBand Y k)
    have h_main : volume (⋃ k ∈ Finset.range (K+1), f k) =
        ∑ k ∈ Finset.range (K+1), volume (f k) :=
      MeasureTheory.measure_biUnion_finset hd hm
    calc
      ∑ k ∈ Finset.range (K+1), volume (Y.carrier T ∩ coreDyadicBand Y k)
        = ∑ k ∈ Finset.range (K+1), volume (f k) := by rfl
      _ = volume (⋃ k ∈ Finset.range (K+1), f k) := h_main.symm
      _ = volume (Y.carrier T) := by rw [h_union]
  have h : ∑ k ∈ Finset.range (K+1), (∑ T ∈ F, volume (Y.carrier T ∩ coreDyadicBand Y k)) =
      ∑ T ∈ F, ∑ k ∈ Finset.range (K+1), volume (Y.carrier T ∩ coreDyadicBand Y k) := by
    rw [Finset.sum_comm]
  rw [h]
  apply Finset.sum_congr rfl
  intro T hT
  exact h_partition T hT

/-- Dyadic multiplicity pigeonhole. -/
lemma core_dyadic_pigeonhole {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) {K : ℕ} (hK : F.card < (2 : ℕ)^(K+1))
    (_hM_pos : 0 < coreTotalMass Y)
    (_hM_ne_top : coreTotalMass Y ≠ ⊤) :
    ∃ k : ℕ, k ∈ Finset.range (K+1) ∧
      coreTotalMass Y / (K+1 : ENNReal) ≤
        ∑ T ∈ F, volume (Y.carrier T ∩ coreDyadicBand Y k) := by
  set M : ENNReal := coreTotalMass Y with hM
  set bands : Finset ℕ := Finset.range (K+1) with hbands
  let f : ℕ → ENNReal := fun k => ∑ T ∈ F, volume (Y.carrier T ∩ coreDyadicBand Y k)
  have h_sum : ∑ k ∈ bands, f k = M := coreDyadicBandMass_sum Y hK
  have h_nonempty : bands.Nonempty := by simp [hbands]
  rcases Finset.exists_max_image bands f h_nonempty with ⟨k, hk, hmax⟩
  have h4 : ∑ j ∈ bands, f j ≤ (K+1 : ENNReal) * f k := by
    have h5 : ∑ j ∈ bands, f j ≤ ∑ j ∈ bands, f k :=
      Finset.sum_le_sum (fun j hj => hmax j hj)
    have h6 : ∑ j ∈ bands, f k = (K+1 : ENNReal) * f k := by
      rw [Finset.sum_const, hbands]; simp
    rw [h6] at h5
    exact h5
  rw [h_sum] at h4
  have h_pos' : (K+1 : ENNReal) ≠ 0 := by simp
  have h_ne_top' : (K+1 : ENNReal) ≠ ⊤ := by simp
  have h7 : M / (K+1 : ENNReal) ≤ f k := by
    have h8 : (K+1 : ENNReal)⁻¹ * M ≤ (K+1 : ENNReal)⁻¹ * ((K+1 : ENNReal) * f k) := by gcongr
    have h9 : (K+1 : ENNReal)⁻¹ * ((K+1 : ENNReal) * f k) = f k := by
      rw [←mul_assoc]
      have h92 : (K+1 : ENNReal)⁻¹ * (K+1 : ENNReal) = 1 := by
        rw [mul_comm]; exact ENNReal.mul_inv_cancel h_pos' h_ne_top'
      rw [h92]; ring
    have h10 : (K+1 : ENNReal)⁻¹ * M = M * (K+1 : ENNReal)⁻¹ := by ring
    rw [h10] at h8
    rw [h9] at h8
    have hdiv : M / (K+1 : ENNReal) = M * (K+1 : ENNReal)⁻¹ := by
      simp [div_eq_mul_inv]
    rw [hdiv]; exact h8
  exact ⟨k, hk, h7⟩

/-- Restrict shading to multiplicity band [lo, hi). -/
def coreRestrictToBand {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (lo hi : ℕ) : Kakeya.Shading F :=
  let band : Set Point3 := {x | lo ≤ coreShadedMultiplicity Y x ∧ coreShadedMultiplicity Y x < hi}
  have h_band_meas : MeasurableSet band := by
    have hmf : Measurable (coreShadedMultiplicity Y) := measurable_coreShadedMultiplicity Y
    have h1 : MeasurableSet (Set.Ici lo) := by simp
    have h2 : MeasurableSet (Set.Iio hi) := by simp
    have h1' : MeasurableSet (coreShadedMultiplicity Y ⁻¹' (Set.Ici lo)) := h1.preimage hmf
    have h2' : MeasurableSet (coreShadedMultiplicity Y ⁻¹' (Set.Iio hi)) := h2.preimage hmf
    have hband : band = (coreShadedMultiplicity Y ⁻¹' (Set.Ici lo)) ∩ (coreShadedMultiplicity Y ⁻¹' (Set.Iio hi)) := by
      ext x; simp [band]
    rw [hband]; exact h1'.inter h2'
  { carrier := fun T => Y.carrier T ∩ band
    measurable_carrier := fun T hT => (Y.measurable_carrier hT).inter h_band_meas
    subset_tube := fun T hT => Set.inter_subset_left.trans (Y.subset_tube hT) }

-- ============================================================================
-- Alternating pruning (well-founded recursion on tube count)
-- ============================================================================

private lemma alternating_prune_aux
    {δ : ℝ} {F_orig : Kakeya.TubeFamily δ}
    (Y_orig : Kakeya.Shading F_orig)
    {F_cur : Kakeya.TubeFamily δ}
    (hF_cur_sub : F_cur ⊆ F_orig)
    (Y_cur : Kakeya.Shading F_cur)
    (alphaTube : ENNReal)
    (threshold : ℕ) :
    ∃ (F3 : Kakeya.TubeFamily δ) (Z : Kakeya.Shading F3),
      F3 ⊆ F_cur ∧
      (∀ T ∈ F3, Z.carrier T ⊆ Y_cur.carrier T) ∧
      (∀ T ∈ F3, alphaTube * volume (Y_orig.carrier T) ≤ volume (Z.carrier T)) ∧
      (∀ x ∈ Z.union, threshold ≤ coreShadedMultiplicity Z x) := by
  have h_main : ∀ (s : Kakeya.TubeFamily δ),
      ∀ (h_sub : s ⊆ F_orig) (Y_s : Kakeya.Shading s),
        ∃ (F3 : Kakeya.TubeFamily δ) (Z : Kakeya.Shading F3),
          F3 ⊆ s ∧
          (∀ T ∈ F3, Z.carrier T ⊆ Y_s.carrier T) ∧
          (∀ T ∈ F3, alphaTube * volume (Y_orig.carrier T) ≤ volume (Z.carrier T)) ∧
          (∀ x ∈ Z.union, threshold ≤ coreShadedMultiplicity Z x) := by
    intro s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro h_sub Y_s
      let Y_orig_s : Kakeya.Shading s := coreRestrictFamily Y_orig h_sub
      let F_pruned := corePruneTubes Y_orig_s Y_s alphaTube
      have hF_pruned_sub : F_pruned ⊆ s := Finset.filter_subset _ _
      let Z : Kakeya.Shading F_pruned := coreRestrictFamily Y_s hF_pruned_sub
      have h_check_em : (∀ x ∈ Z.union, threshold ≤ coreShadedMultiplicity Z x) ∨
          ¬(∀ x ∈ Z.union, threshold ≤ coreShadedMultiplicity Z x) := Classical.em _
      cases h_check_em with
      | inl h_check =>
        have h_mass : ∀ T ∈ F_pruned,
            alphaTube * volume (Y_orig.carrier T) ≤ volume (Z.carrier T) := by
          intro T hT
          have h4 : alphaTube * volume (Y_orig_s.carrier T) ≤ volume (Y_s.carrier T) :=
            (Finset.mem_filter.mp hT).2
          simpa [Y_orig_s, Z, coreRestrictFamily] using h4
        have h_subset : ∀ T ∈ F_pruned, Z.carrier T ⊆ Y_s.carrier T := by
          intro T _; rfl
        exact ⟨F_pruned, Z, hF_pruned_sub, h_subset, h_mass, h_check⟩
      | inr h_check =>
        let goodSet : Set Point3 := {x | threshold ≤ coreShadedMultiplicity Z x}
        have h_goodSet_meas : MeasurableSet goodSet := by
          have hmf : Measurable (coreShadedMultiplicity Z) := measurable_coreShadedMultiplicity Z
          have h1 : MeasurableSet (Set.Ici threshold) := by simp
          exact h1.preimage hmf
        let Y_next : Kakeya.Shading F_pruned :=
          { carrier := fun T => Z.carrier T ∩ goodSet
            measurable_carrier := fun T hT => (Z.measurable_carrier hT).inter h_goodSet_meas
            subset_tube := fun T hT => Set.inter_subset_left.trans (Z.subset_tube hT) }
        let Y_orig_pruned : Kakeya.Shading F_pruned :=
          coreRestrictFamily Y_orig (hF_pruned_sub.trans h_sub)
        let F_next := corePruneTubes Y_orig_pruned Y_next alphaTube
        have hF_next_sub : F_next ⊆ F_pruned := Finset.filter_subset _ _
        by_cases h_strict : F_next ⊂ F_pruned
        · have h1 : F_next ⊆ s := hF_next_sub.trans hF_pruned_sub
          have h2 : F_next.card < F_pruned.card := Finset.card_lt_card h_strict
          have h3 : F_pruned.card ≤ s.card := Finset.card_le_card hF_pruned_sub
          have h4 : F_next.card < s.card := lt_of_lt_of_le h2 h3
          have h_not_supset : ¬(s ⊆ F_next) := by
            intro h_supset
            have h_eq : F_next = s := Finset.Subset.antisymm h1 h_supset
            rw [h_eq] at h4
            exact lt_irrefl s.card h4
          have h_lt : F_next ⊂ s := ⟨h1, h_not_supset⟩
          let Z_next : Kakeya.Shading F_next := coreRestrictFamily Y_next hF_next_sub
          have h_Fnext_sub_orig : F_next ⊆ F_orig := h1.trans h_sub
          have h_ih_result := ih F_next h_lt
          rcases h_ih_result h_Fnext_sub_orig Z_next with ⟨F3, Z3, hF3_sub, h_subset3, h_mass, h_mult⟩
          have h_subset : ∀ T ∈ F3, Z3.carrier T ⊆ Y_s.carrier T := by
            intro T hT
            have h1sub : Z3.carrier T ⊆ Z_next.carrier T := h_subset3 T hT
            have h2sub : Z_next.carrier T ⊆ Y_next.carrier T := by rfl
            have h3sub : Y_next.carrier T ⊆ Z.carrier T := Set.inter_subset_left
            have h4sub : Z.carrier T ⊆ Y_s.carrier T := by rfl
            exact (h1sub.trans h2sub).trans h3sub |>.trans h4sub
          exact ⟨F3, Z3, hF3_sub.trans h1, h_subset, h_mass, h_mult⟩
        · have h_not_ss : ¬(F_next ⊂ F_pruned) := h_strict
          have h_eq : F_next = F_pruned := by
            by_contra hne
            have h_ss : F_next ⊂ F_pruned := by
              refine' ⟨hF_next_sub, _⟩
              intro h_supset
              exact hne (Finset.Subset.antisymm hF_next_sub h_supset)
            exact h_not_ss h_ss
          have h_mass : ∀ T ∈ F_pruned,
              alphaTube * volume (Y_orig.carrier T) ≤ volume (Y_next.carrier T) := by
            intro T hT
            have hT' : T ∈ F_next := by rw [h_eq]; exact hT
            have h4 : alphaTube * volume (Y_orig_pruned.carrier T) ≤ volume (Y_next.carrier T) :=
              (Finset.mem_filter.mp hT').2
            simpa [Y_orig_pruned, coreRestrictFamily] using h4
          have h_mult : ∀ x ∈ Y_next.union, threshold ≤ coreShadedMultiplicity Y_next x := by
            intro x hx
            have h5 : x ∈ goodSet := by
              rcases (show ∃ T, T ∈ F_pruned ∧ x ∈ Y_next.carrier T from by
                simpa [Kakeya.Shading.union, Set.mem_setOf_eq] using hx) with ⟨T, hT, hxT⟩
              exact hxT.2
            have h6 : threshold ≤ coreShadedMultiplicity Z x := h5
            letI : DecidablePred (fun T : Kakeya.DeltaTube δ => x ∈ Y_next.carrier T) :=
              fun T => Classical.propDecidable (x ∈ Y_next.carrier T)
            letI : DecidablePred (fun T : Kakeya.DeltaTube δ => x ∈ Z.carrier T) :=
              fun T => Classical.propDecidable (x ∈ Z.carrier T)
            have h_filter_eq : (F_pruned.filter (fun T => x ∈ Y_next.carrier T)) =
                (F_pruned.filter (fun T => x ∈ Z.carrier T)) := by
              ext T
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hT, h_in⟩; exact ⟨hT, h_in.1⟩
              · rintro ⟨hT, h_in⟩; exact ⟨hT, ⟨h_in, h5⟩⟩
            have h7 : coreShadedMultiplicity Y_next x = coreShadedMultiplicity Z x := by
              dsimp only [coreShadedMultiplicity]; congr
            rw [h7]; exact h6
          have h_subset : ∀ T ∈ F_pruned, Y_next.carrier T ⊆ Y_s.carrier T := by
            intro T _
            have h1 : Y_next.carrier T ⊆ Z.carrier T := Set.inter_subset_left
            have h2 : Z.carrier T ⊆ Y_s.carrier T := by rfl
            exact h1.trans h2
          exact ⟨F_pruned, Y_next, hF_pruned_sub, h_subset, h_mass, h_mult⟩
  exact h_main F_cur hF_cur_sub Y_cur

/-- Full alternating pruning from original and current shading.
Returns Z ⊆ Y_cur pointwise. -/
lemma full_alternating_prune_from
    {δ : ℝ} {F_orig : Kakeya.TubeFamily δ}
    (Y_orig : Kakeya.Shading F_orig)
    {F_cur : Kakeya.TubeFamily δ}
    (hF_cur_sub : F_cur ⊆ F_orig)
    (Y_cur : Kakeya.Shading F_cur)
    (alphaTube : ENNReal)
    (threshold : ℕ) :
    ∃ (F3 : Kakeya.TubeFamily δ) (Z : Kakeya.Shading F3),
      F3 ⊆ F_cur ∧
      (∀ T ∈ F3, Z.carrier T ⊆ Y_cur.carrier T) ∧
      (∀ T ∈ F3, alphaTube * volume (Y_orig.carrier T) ≤ volume (Z.carrier T)) ∧
      (∀ x ∈ Z.union, threshold ≤ coreShadedMultiplicity Z x) :=
  alternating_prune_aux Y_orig hF_cur_sub Y_cur alphaTube threshold

end Kakeya.Assouad
