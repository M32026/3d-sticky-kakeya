module

/-
  Tube family finiteness bridge: finite δ-separated subset of tubes.

  AffineLine is not a ProperSpace instance by default, so we prove
  bounded → TotallyBounded directly using the compact direction circle
  and bounded offset plane.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

/-- Bounded subsets of AffineLine are totally bounded: direction projections lie in the
    compact unit ball of operators, and offsets lie in a bounded Euclidean subset. -/
lemma affineLine_bounded_totallyBounded {S : Set AffineLine}
    (hS : Bornology.IsBounded S) : TotallyBounded S := by
  by_cases h_empty : S = ∅
  · rw [h_empty]; exact Set.Finite.totallyBounded (by simp)
  · rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨ℓ₀, hℓ₀⟩
    have h_bdd : ∃ (B : ℝ), ∀ (x : AffineLine), x ∈ S → dist x ℓ₀ ≤ B := by
      have h : ∃ (C : ℝ), ∀ (x : AffineLine), x ∈ S → ∀ (y : AffineLine), y ∈ S → dist x y ≤ C :=
        Metric.isBounded_iff.mp hS
      rcases h with ⟨C, hC⟩
      exact ⟨C, fun x hx => hC x hx ℓ₀ hℓ₀⟩
    rcases h_bdd with ⟨B, hB⟩
    let R : ℝ := ‖AffineLine.offset ℓ₀‖ + B
    have hR : ∀ ℓ ∈ S, ‖AffineLine.offset ℓ‖ ≤ R := by
      intro ℓ hℓ
      have h_def : dist ℓ ℓ₀ =
          ‖ℓ.1.direction.starProjection - ℓ₀.1.direction.starProjection‖ +
          ‖AffineLine.offset ℓ - AffineLine.offset ℓ₀‖ := by
        rfl
      have h2 : ‖AffineLine.offset ℓ - AffineLine.offset ℓ₀‖ ≤ dist ℓ ℓ₀ := by
        rw [h_def]
        exact le_add_of_nonneg_left (norm_nonneg _)
      have h3 : ‖AffineLine.offset ℓ‖ ≤
          ‖AffineLine.offset ℓ₀‖ + ‖AffineLine.offset ℓ - AffineLine.offset ℓ₀‖ := by
        exact norm_le_norm_add_norm_sub' ℓ.offset ℓ₀.offset
      linarith [hB ℓ hℓ]
    let Op := EuclideanPlane →L[ℝ] EuclideanPlane
    let K_off : Set EuclideanPlane := Metric.closedBall 0 R
    let K_dir : Set Op := Metric.closedBall 0 1
    have h_off_compact : IsCompact K_off := by exact isCompact_closedBall 0 R
    have h_dir_compact : IsCompact K_dir := by exact isCompact_closedBall 0 1
    let f : AffineLine → EuclideanPlane × Op :=
      fun ℓ => (AffineLine.offset ℓ, ℓ.1.direction.starProjection)
    have h_sp_norm : ∀ (ℓ : AffineLine), ‖ℓ.1.direction.starProjection‖ ≤ 1 := by
      intro ℓ
      have h : IsStarProjection ℓ.1.direction.starProjection := by
        exact isStarProjection_starProjection
      exact IsStarProjection.norm_le _ h
    have h_img_subset : f '' S ⊆ K_off ×ˢ K_dir := by
      intro z hz
      have h_exists : ∃ (ℓ : AffineLine), ℓ ∈ S ∧ f ℓ = z := by
        simpa [Set.mem_image] using hz
      rcases h_exists with ⟨ℓ, hℓ, rfl⟩
      have h4 : ‖AffineLine.offset ℓ‖ ≤ R := hR ℓ hℓ
      have h5 : ‖ℓ.1.direction.starProjection‖ ≤ 1 := h_sp_norm ℓ
      have h6 : f ℓ ∈ K_off ×ˢ K_dir := by
        exact ⟨by simpa [K_off, Metric.mem_closedBall] using h4,
                 by simpa [K_dir, Metric.mem_closedBall] using h5⟩
      exact h6
    have h_compact : IsCompact (K_off ×ˢ K_dir) := h_off_compact.prod h_dir_compact
    have h_tb_img : TotallyBounded (f '' S) :=
      h_compact.totallyBounded.subset h_img_subset
    have h_lip1 : ∀ (ℓ₁ ℓ₂ : AffineLine), dist (f ℓ₁) (f ℓ₂) ≤ dist ℓ₁ ℓ₂ := by
      intro ℓ₁ ℓ₂
      have h_dir_dist : dist (ℓ₁.1.direction.starProjection) (ℓ₂.1.direction.starProjection) =
          ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := by
        rw [dist_eq_norm]
      have h_off_dist : dist (AffineLine.offset ℓ₁) (AffineLine.offset ℓ₂) =
          ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ := by
        rw [dist_eq_norm]
      have h_dist_f : dist (f ℓ₁) (f ℓ₂) =
          max ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖
              ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := by
        have h : dist (f ℓ₁) (f ℓ₂) = max
            (dist (AffineLine.offset ℓ₁) (AffineLine.offset ℓ₂))
            (dist (ℓ₁.1.direction.starProjection) (ℓ₂.1.direction.starProjection)) := by
          simp [f, Prod.dist_eq]
        rw [h, h_off_dist, h_dir_dist]
      rw [h_dist_f]
      have h1 : ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ ≤ dist ℓ₁ ℓ₂ := by
        have hdef : dist ℓ₁ ℓ₂ =
            ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
            ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ := by rfl
        rw [hdef]; exact le_add_of_nonneg_left (norm_nonneg _)
      have h2 : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ dist ℓ₁ ℓ₂ := by
        have hdef : dist ℓ₁ ℓ₂ =
            ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
            ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ := by rfl
        rw [hdef]; exact le_add_of_nonneg_right (norm_nonneg _)
      exact max_le h1 h2
    have h_lip2 : ∀ (ℓ₁ ℓ₂ : AffineLine), dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := by
      intro ℓ₁ ℓ₂
      have h_dir_dist : dist (ℓ₁.1.direction.starProjection) (ℓ₂.1.direction.starProjection) =
          ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := by
        rw [dist_eq_norm]
      have h_off_dist : dist (AffineLine.offset ℓ₁) (AffineLine.offset ℓ₂) =
          ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ := by
        rw [dist_eq_norm]
      have h_dist_f : dist (f ℓ₁) (f ℓ₂) =
          max ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖
              ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := by
        have h : dist (f ℓ₁) (f ℓ₂) = max
            (dist (AffineLine.offset ℓ₁) (AffineLine.offset ℓ₂))
            (dist (ℓ₁.1.direction.starProjection) (ℓ₂.1.direction.starProjection)) := by
          simp [f, Prod.dist_eq]
        rw [h, h_off_dist, h_dir_dist]
      have hdef : dist ℓ₁ ℓ₂ =
          ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
          ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ := by rfl
      rw [hdef]
      have h3 : ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖ ≤
          max ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖
              ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := le_max_left _ _
      have h4 : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤
          max ‖AffineLine.offset ℓ₁ - AffineLine.offset ℓ₂‖
              ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ := le_max_right _ _
      linarith
    have h_inj : Function.Injective f := by
      intro ℓ₁ ℓ₂ h
      have h_eq : f ℓ₁ = f ℓ₂ := h
      have h1 : AffineLine.offset ℓ₁ = AffineLine.offset ℓ₂ := by
        exact congr_arg Prod.fst h_eq
      have h2 : ℓ₁.1.direction.starProjection = ℓ₂.1.direction.starProjection := by
        exact congr_arg Prod.snd h_eq
      have h3 : ℓ₁.1.direction = ℓ₂.1.direction := by
        simpa using congr((·.range) $h2)
      apply Subtype.ext
      rw [AffineSubspace.eq_iff_direction_eq_of_mem (AffineLine.offset_mem ℓ₁)
          (h1 ▸ AffineLine.offset_mem ℓ₂)]
      exact h3
    have h_uc : UniformContinuous f := by
      rw [Metric.uniformContinuous_iff]
      intro ε hε
      refine' ⟨ε, hε, _⟩
      intro x y hxy
      exact h_lip1 x y |>.trans_lt hxy
    have h_ui : IsUniformInducing f := by
      apply IsUniformInducing.mk'
      intro s
      constructor
      · -- Forward: s ∈ uniformity → ∃ t ∈ uniformity, preimage t ⊆ s
        intro hs
        have hε : ∃ (ε : ℝ), 0 < ε ∧ ∀ ⦃a b : AffineLine⦄, dist a b < ε → (a, b) ∈ s :=
          Metric.mem_uniformity_dist.mp hs
        rcases hε with ⟨ε, hε_pos, hε_sub⟩
        let t : Set ((EuclideanPlane × Op) × (EuclideanPlane × Op)) :=
          {p | dist p.1 p.2 < ε / 2}
        have h_half_pos : 0 < ε / 2 := by linarith [hε_pos]
        have ht : t ∈ uniformity (EuclideanPlane × Op) :=
          Metric.mem_uniformity_dist.mpr ⟨ε / 2, h_half_pos, fun {a} {b} h => h⟩
        refine' ⟨t, ht, _⟩
        intro x y hxy
        have h5 : dist (f x) (f y) < ε / 2 := hxy
        have h6 : dist x y < ε := by
          have h7 : dist x y ≤ 2 * dist (f x) (f y) := h_lip2 x y
          linarith
        exact hε_sub h6
      · -- Backward: ∃ t ∈ uniformity, preimage t ⊆ s → s ∈ uniformity
        rintro ⟨t, ht, h_sub⟩
        have h_preimg : {p : AffineLine × AffineLine | (f p.1, f p.2) ∈ t} ∈ uniformity AffineLine :=
          h_uc ht
        have h9 : {p : AffineLine × AffineLine | (f p.1, f p.2) ∈ t} ⊆ s := by
          intro p hp
          exact h_sub p.1 p.2 hp
        exact Filter.mem_of_superset h_preimg h9
    have h_main : TotallyBounded S := by
      have h6 : S ⊆ f ⁻¹' (f '' S) := by
        intro x hx
        exact ⟨x, hx, rfl⟩
      have h7 : TotallyBounded (f ⁻¹' (f '' S)) := totallyBounded_preimage h_ui h_tb_img
      exact TotallyBounded.subset h6 h7
    exact h_main

/-- Version of finite_separated_subset for spaces where bounded implies totally bounded,
    without requiring ProperSpace. -/
lemma finite_separated_subset_of_totallyBounded {X : Type*} [PseudoMetricSpace X]
    {P : Set X} {δ : ℝ≥0} (hδ_pos : 0 < δ)
    (hP_tb : TotallyBounded P) (hP_nonempty : P.Nonempty) :
    ∃ (P' : Set X), P'.Finite ∧ P' ⊆ P ∧
      Metric.IsSeparated (δ : ENNReal) P' ∧
      Metric.IsCover δ P P' ∧
      Metric.externalCoveringNumber δ P ≤ P'.encard := by
  let halfδ : ℝ≥0 := δ / 2
  have hhalfδ_pos : 0 < halfδ := by positivity
  have h2δ : 2 * halfδ = δ := by
    apply NNReal.coe_injective
    simp [halfδ] <;> ring
  let U : SetRel X X := {p | edist p.1 p.2 < (halfδ : ENNReal)}
  have hU : U ∈ uniformity X := by
    apply edist_mem_uniformity
    exact_mod_cast hhalfδ_pos
  rcases hP_tb.exists_subset hU with ⟨C, hC_sub, hC_fin, hCover⟩
  have h_mono : ∀ y ∈ C, {x : X | edist x y < (halfδ : ENNReal)} ⊆ {x : X | edist x y ≤ (halfδ : ENNReal)} := by
    intro y _
    intro x hx
    have h_lt : edist x y < (halfδ : ENNReal) := by simpa using hx
    exact le_of_lt h_lt
  have hCover' : P ⊆ ⋃ y ∈ C, {x | edist x y ≤ (halfδ : ENNReal)} := by
    calc P ⊆ ⋃ y ∈ C, {x | (x, y) ∈ U} := hCover
      _ = ⋃ y ∈ C, {x | edist x y < (halfδ : ENNReal)} := by rfl
      _ ⊆ ⋃ y ∈ C, {x | edist x y ≤ (halfδ : ENNReal)} := by
        exact Set.iUnion₂_mono h_mono
  have h_isCover : Metric.IsCover halfδ P C := by exact Metric.isCover_iff_subset_iUnion_closedEBall.mpr hCover'
  have h_cover_fin : Metric.externalCoveringNumber halfδ P ≠ ⊤ := by
    have h4 : Metric.externalCoveringNumber halfδ P ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_isCover
    have h5 : C.encard ≠ ⊤ := Set.encard_ne_top_iff.mpr hC_fin
    exact ne_top_of_le_ne_top h5 h4
  have h_pack_fin : Metric.packingNumber δ P ≠ ⊤ := by
    have h6 : Metric.packingNumber (2 * halfδ) P ≤ Metric.externalCoveringNumber halfδ P :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber halfδ P
    rw [h2δ] at h6
    exact ne_top_of_le_ne_top h_cover_fin h6
  let P' := Metric.maximalSeparatedSet δ P
  have h_sub : P' ⊆ P := Metric.maximalSeparatedSet_subset
  have h_sep : Metric.IsSeparated (δ : ENNReal) P' := Metric.isSeparated_maximalSeparatedSet
  have h_coverP : Metric.IsCover δ P P' := Metric.isCover_maximalSeparatedSet h_pack_fin
  have h_encard : P'.encard = Metric.packingNumber δ P :=
    Metric.encard_maximalSeparatedSet h_pack_fin
  have h_fin : P'.Finite := Set.encard_ne_top_iff.mp (by
    rw [h_encard]; exact h_pack_fin)
  have h_ge : Metric.externalCoveringNumber δ P ≤ P'.encard := by
    rw [h_encard]
    have h7 : Metric.externalCoveringNumber δ P ≤ Metric.coveringNumber δ P :=
      Metric.externalCoveringNumber_le_coveringNumber _ _
    have h8 : Metric.coveringNumber δ P ≤ Metric.packingNumber δ P :=
      Metric.coveringNumber_le_packingNumber _ _
    exact le_trans h7 h8
  exact ⟨P', h_fin, h_sub, h_sep, h_coverP, h_ge⟩

/-- Finite δ-separated subset of a bounded tube family in AffineLine. -/
lemma finite_separated_tubes {T : Set AffineLine} {δ : ℝ≥0} (hδ_pos : 0 < δ)
    (hT_bounded : Bornology.IsBounded T) (hT_nonempty : T.Nonempty) :
    ∃ (T' : Set AffineLine), T'.Finite ∧ T' ⊆ T ∧
      Metric.IsSeparated (δ : ENNReal) T' ∧
      Metric.IsCover δ T T' ∧
      Metric.externalCoveringNumber δ T ≤ T'.encard :=
  finite_separated_subset_of_totallyBounded hδ_pos (affineLine_bounded_totallyBounded hT_bounded) hT_nonempty

end DirecretisedFurstenbergEstimate
