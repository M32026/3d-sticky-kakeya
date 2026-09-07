module

/-
  AffineLine S-set transfer lemmas for A10 product witness.

  Provides:
  - IsDeltaSSet.scale_down2: scale from larger δ to smaller δ in 2D
  - affineLine_bounded_slope_sset_to_params: transfer S-set from AffineLine to ℝ²

  Whiteprint node: appendix_a_alternative / a10_product_witness
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBoundedHelpers2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BilipschitzImage
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SsetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.A10

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Scale-down lemma (larger δ → smaller δ) in 2D -/

/-- Scale down in 2D: (δ₂,s,C)-set → (δ₁,s,C·16·4^s)-set when δ₁ ≤ δ₂ ≤ 4δ₁. -/
lemma IsDeltaSSet.scale_down2 {δ₁ δ₂ s C : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h1 : δ₁ ≤ δ₂) (h2 : δ₂ ≤ 4 * δ₁) {A : Set (ℝ × ℝ)}
    (hP : IsDeltaSSet δ₂ s C A) :
    IsDeltaSSet δ₁ s (C * 16 * (4 : ℝ) ^ s) A := by
  have hC_pos : 0 < C := hP.2.2.1
  have hs_nonneg : 0 ≤ s := hP.2.2.2.1
  have hC'_pos : 0 < C * 16 * (4 : ℝ) ^ s := by positivity
  have h1' : δ₁.toNNReal ≤ δ₂.toNNReal := by
    have hδ₁_nn : 0 ≤ δ₁ := by linarith
    have hδ₂_nn : 0 ≤ δ₂ := by linarith
    exact (Real.toNNReal_le_toNNReal_iff hδ₂_nn).mpr h1
  have h_refine : ∀ (S : Set (ℝ × ℝ)),
      (Metric.externalCoveringNumber δ₁.toNNReal S : ENNReal) ≤
        ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber δ₂.toNNReal S : ENNReal) := by
    intro S
    have h : Metric.externalCoveringNumber δ₁.toNNReal S ≤ 16 * Metric.externalCoveringNumber δ₂.toNNReal S :=
      covering_scale_2d hδ₁ hδ₂ h2
    have h' : (↑(Metric.externalCoveringNumber δ₁.toNNReal S) : ENNReal) ≤
        (↑(16 * Metric.externalCoveringNumber δ₂.toNNReal S) : ENNReal) := by
      exact_mod_cast h
    have h'' : (↑(16 * Metric.externalCoveringNumber δ₂.toNNReal S) : ENNReal) =
        ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber δ₂.toNNReal S : ENNReal) := by
      simp [ENNReal.coe_mul] <;> ring
    rw [h''] at h'
    exact h'
  have h_anti : (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) ≤
      (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by
    have h : Metric.externalCoveringNumber δ₂.toNNReal A ≤ Metric.externalCoveringNumber δ₁.toNNReal A :=
      Metric.externalCoveringNumber_anti (X := (ℝ × ℝ)) h1'
    have h' : (↑(Metric.externalCoveringNumber δ₂.toNNReal A) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber δ₁.toNNReal A) : ENNReal) := by
      exact_mod_cast h
    exact h'
  have h4s_ge1 : (1 : ℝ) ≤ (4 : ℝ) ^ s := by
    apply Real.one_le_rpow <;> norm_num <;> linarith
  have h_const_le : ENNReal.ofReal C * ENNReal.ofReal (16 : ℝ) ≤
      ENNReal.ofReal (C * 16 * (4 : ℝ) ^ s) := by
    have h_real : C * 16 ≤ C * 16 * (4 : ℝ) ^ s := by
      have h10 : (1 : ℝ) ≤ (4 : ℝ) ^ s := h4s_ge1
      nlinarith
    have h_eq : ENNReal.ofReal C * ENNReal.ofReal (16 : ℝ) = ENNReal.ofReal (C * (16 : ℝ)) := by
      rw [ENNReal.ofReal_mul (by linarith)] <;> norm_num
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_real
  have h_main : ∀ (x : ℝ × ℝ) (r : ℝ), δ₁ ≤ r →
      (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (C * 16 * (4 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by
    intro x r hr
    by_cases h_r_ge : r ≥ δ₂
    · have h41 : Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) ≤
          16 * Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) :=
        covering_scale_2d hδ₁ hδ₂ h2
      have h4 : (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := by
        exact_mod_cast h41
      have h5 : (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) :=
        hP.2.2.2.2 x r h_r_ge
      have h6 : (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) ≤
          (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := h_anti
      calc (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) := h4
      _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal)) := by gcongr
      _ = ENNReal.ofReal C * ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) := by ring
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by gcongr
      _ ≤ ENNReal.ofReal (C * 16 * (4 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by gcongr
    · have h8 : δ₂ ≤ 4 * r := by linarith
      have h_sub : A ∩ Metric.closedBall x r ⊆ A ∩ Metric.closedBall x δ₂ := by
        intro z hz
        have h_dist : dist z x ≤ r := hz.2
        have h_r_le : r ≤ δ₂ := by linarith
        have h_dist2 : dist z x ≤ δ₂ := by linarith
        exact ⟨hz.1, h_dist2⟩
      have h41 : Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x δ₂) :=
        Metric.externalCoveringNumber_mono_set (ε := δ₁.toNNReal) h_sub
      have h4 : (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x δ₂) : ENNReal) := by
        exact_mod_cast h41
      have h51 : Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x δ₂) ≤
          16 * Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x δ₂) :=
        covering_scale_2d hδ₁ hδ₂ h2
      have h5 : (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x δ₂) : ENNReal) ≤
          ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x δ₂) : ENNReal) := by
        exact_mod_cast h51
      have h6 : (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x δ₂) : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal δ₂) ^ s *
            (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) :=
        hP.2.2.2.2 x δ₂ (by linarith)
      have h9 : δ₂ ^ s ≤ (4 : ℝ) ^ s * r ^ s := by
        have h10 : δ₂ ≤ 4 * r := h8
        have h11 : δ₂ ^ s ≤ (4 * r) ^ s := by gcongr <;> linarith
        have h12 : (4 * r) ^ s = (4 : ℝ) ^ s * r ^ s := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
        rw [h12] at h11; exact h11
      have h13 : (ENNReal.ofReal δ₂) ^ s ≤
          ENNReal.ofReal ((4 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s := by
        have h14 : ENNReal.ofReal δ₂ ^ s = ENNReal.ofReal (δ₂ ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
        have h15 : ENNReal.ofReal ((4 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s =
            ENNReal.ofReal (((4 : ℝ) ^ s) * r ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h14, h15]
        exact ENNReal.ofReal_le_ofReal h9
      have h16 : (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal) ≤
          (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := h_anti
      have h17 : ENNReal.ofReal C * ENNReal.ofReal (16 : ℝ) * ENNReal.ofReal ((4 : ℝ) ^ s) =
          ENNReal.ofReal (C * (16 : ℝ) * ((4 : ℝ) ^ s)) := by
        rw [← ENNReal.ofReal_mul (show 0 ≤ C by linarith),
            ← ENNReal.ofReal_mul (show 0 ≤ C * (16 : ℝ) by positivity)]
        <;> ring
      have h18 : C * (16 : ℝ) * ((4 : ℝ) ^ s) = C * 16 * (4 : ℝ) ^ s := by ring
      calc (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber δ₁.toNNReal (A ∩ Metric.closedBall x δ₂) : ENNReal) := h4
      _ ≤ ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber δ₂.toNNReal (A ∩ Metric.closedBall x δ₂) : ENNReal) := h5
      _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal C * (ENNReal.ofReal δ₂) ^ s *
              (Metric.externalCoveringNumber δ₂.toNNReal A : ENNReal)) := by gcongr
      _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal C *
              (ENNReal.ofReal ((4 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
              (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal)) := by gcongr
      _ = ENNReal.ofReal C * ENNReal.ofReal (16 : ℝ) * ENNReal.ofReal ((4 : ℝ) ^ s) *
              (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by ring
      _ = ENNReal.ofReal (C * (16 : ℝ) * ((4 : ℝ) ^ s)) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by
        rw [h17] <;> ring
      _ = ENNReal.ofReal (C * 16 * (4 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s *
              (Metric.externalCoveringNumber δ₁.toNNReal A : ENNReal) := by
        rw [h18]
  exact ⟨hP.1, hδ₁, hC'_pos, hs_nonneg, h_main⟩

end DirecretisedFurstenbergEstimate.A10

namespace DirecretisedFurstenbergEstimate.A10

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils
open AffineLineLipschitzTransfer

/-! ### AffineLine → ℝ² parameter transfer -/

/-- Helper: convert dist bound to edist bound. -/
private lemma dist_to_edist {X : Type*} [PseudoMetricSpace X] {x y : X} {ε : ℝ} (hε : 0 ≤ ε)
    (h : dist x y ≤ ε) : edist x y ≤ ↑ε.toNNReal := by
  have hfin1 : edist x y ≠ ⊤ := by exact edist_ne_top x y
  have hfin2 : (↑ε.toNNReal : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
  have h3 : (edist x y).toReal ≤ (↑ε.toNNReal : ENNReal).toReal := by
    have h4 : (edist x y).toReal = dist x y := by exact Eq.symm (dist_edist x y)
    have h5 : (↑ε.toNNReal : ENNReal).toReal = ε := by simp [hε]
    rw [h4, h5]; exact h
  exact (ENNReal.toReal_le_toReal hfin1 hfin2).mp h3

/-- Specialized reverse covering for AffineLine → ℝ².
    N_δ(T) ≤ N_{δ/20}(f '' T) using 10-anti-Lipschitz on T. -/
private lemma affineLine_reverse_cover
    {δ : ℝ} (hδ_pos : 0 < δ)
    {T : Set AffineLine} (hT_nonempty : T.Nonempty)
    (f : AffineLine → ℝ × ℝ)
    (h_antilip : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ T → ℓ₂ ∈ T →
      dist ℓ₁ ℓ₂ ≤ 10 * dist (f ℓ₁) (f ℓ₂)) :
    (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
      (Metric.externalCoveringNumber ((δ / 20).toNNReal) (f '' T) : ENNReal) := by
  let ε : ℝ := δ / 20
  have hε_pos : 0 < ε := by positivity
  have hε_nonneg : 0 ≤ ε := by linarith
  let a_default : AffineLine := hT_nonempty.some
  have h_main : ∀ (C : Set (ℝ × ℝ)), Metric.IsCover ε.toNNReal (f '' T) C →
      (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤ (1 : ENNReal) * (C.encard : ENNReal) := by
    intro C hC
    by_cases h_inf : Set.Infinite C
    · have h_top' : (C.encard : ENNReal) = ⊤ := by
        have h : C.encard = ⊤ := by rw [Set.encard_eq_top] <;> exact h_inf
        exact_mod_cast h
      rw [h_top'] <;> simp
    · have hfin : Set.Finite C := Set.not_infinite.mp h_inf
      classical
      let Cfin : Finset (ℝ × ℝ) := hfin.toFinset
      have hCfin : (Cfin : Set (ℝ × ℝ)) = C := Set.Finite.coe_toFinset hfin
      let pick (c : ℝ × ℝ) : AffineLine :=
        if h : ∃ a, a ∈ T ∧ dist (f a) c ≤ ε then
          Classical.choose h
        else
          a_default
      let D : Finset AffineLine := Cfin.image pick
      have h_cover : Metric.IsCover δ.toNNReal T (D : Set AffineLine) := by
        intro x hx
        have hfx_in : f x ∈ f '' T := ⟨x, hx, rfl⟩
        rcases hC hfx_in with ⟨c, hc, hed⟩
        have hcfin : c ∈ Cfin := by
          have h1 : c ∈ (Cfin : Set (ℝ × ℝ)) := by simpa [hCfin] using hc
          exact_mod_cast h1
        have h_edist : dist (f x) c ≤ ε := by
          have hfin1 : edist (f x) c ≠ ⊤ := by exact edist_ne_top (f x) c
          have hfin2 : (↑ε.toNNReal : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
          have h3 : (edist (f x) c).toReal ≤ (↑ε.toNNReal : ENNReal).toReal :=
            (ENNReal.toReal_le_toReal hfin1 hfin2).mpr hed
          have h4 : (edist (f x) c).toReal = dist (f x) c := by exact Eq.symm (dist_edist (f x) c)
          have h5 : (↑ε.toNNReal : ENNReal).toReal = ε := by simp [hε_nonneg]
          rw [←h4, ←h5]; exact h3
        set h_exists : ∃ (a : AffineLine), a ∈ T ∧ dist (f a) c ≤ ε := ⟨x, hx, h_edist⟩ with h_exists_def
        set a : AffineLine := Classical.choose h_exists with ha_def
        have ha_in_T : a ∈ T := (Classical.choose_spec h_exists).1
        have hfa_dist : dist (f a) c ≤ ε := (Classical.choose_spec h_exists).2
        have h_pick_eq : pick c = a := by
          have h_unfold : pick c = (if h : ∃ (a : AffineLine), a ∈ T ∧ dist (f a) c ≤ ε then Classical.choose h else a_default) := by rfl
          rw [h_unfold, dif_pos h_exists]
        have ha_in_D : a ∈ (D : Set AffineLine) := by
          rw [←h_pick_eq]
          exact Finset.mem_image.mpr ⟨c, hcfin, rfl⟩
        have h_dist2 : dist (f x) (f a) ≤ 2 * ε := by
          calc dist (f x) (f a)
            ≤ dist (f x) c + dist c (f a) := dist_triangle _ _ _
          _ = dist (f x) c + dist (f a) c := by rw [dist_comm c (f a)]
          _ ≤ ε + ε := by linarith
          _ = 2 * ε := by ring
        have h_final : dist x a ≤ δ := by
          have h : dist x a ≤ 10 * dist (f x) (f a) := h_antilip x a hx ha_in_T
          calc dist x a
            ≤ 10 * dist (f x) (f a) := h
          _ ≤ 10 * (2 * ε) := by gcongr
          _ = δ := by dsimp only [ε] <;> ring
        exact ⟨a, ha_in_D, dist_to_edist (by linarith) h_final⟩
      have h_cover_enat : Metric.externalCoveringNumber δ.toNNReal T ≤ (D : Set AffineLine).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard h_cover
      have h_cover_le : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤ ((D : Set AffineLine).encard : ENNReal) :=
        ENat.toENNReal_le.mpr h_cover_enat
      have h_card : D.card ≤ Cfin.card := Finset.card_image_le
      have h1 : (D : Set AffineLine).encard = D.card := by simp
      have h2 : C.encard = Cfin.card := by rw [← hCfin] <;> simp
      have h_encard : ((D : Set AffineLine).encard : ENNReal) ≤ (C.encard : ENNReal) := by
        rw [h1, h2] <;> exact_mod_cast h_card
      have h_one : (1 : ENNReal) * (C.encard : ENNReal) = (C.encard : ENNReal) := by simp
      rw [h_one]
      exact le_trans h_cover_le h_encard
  have h_transfer : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
      (1 : ENNReal) * (Metric.externalCoveringNumber ((δ / 20).toNNReal) (f '' T) : ENNReal) :=
    externalCoveringNumber_transfer h_main
  simpa using h_transfer

/-- Specialized forward covering for AffineLine → ℝ².
    N_{16δ}(f '' S) ≤ N_δ(S) using 8-Lipschitz on S. -/
private lemma affineLine_forward_cover
    {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Set AffineLine} (hS_nonempty : S.Nonempty)
    (f : AffineLine → ℝ × ℝ)
    (h_lip : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ S → ℓ₂ ∈ S →
      dist (f ℓ₁) (f ℓ₂) ≤ 8 * dist ℓ₁ ℓ₂) :
    (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
  have h16δ_nonneg : 0 ≤ 16 * δ := by positivity
  let s_default : AffineLine := hS_nonempty.some
  have h_main : ∀ (C : Set AffineLine), Metric.IsCover δ.toNNReal S C →
      (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) ≤
        (1 : ENNReal) * (C.encard : ENNReal) := by
    intro C hC
    by_cases h_inf : Set.Infinite C
    · have h_top' : (C.encard : ENNReal) = ⊤ := by
        have h : C.encard = ⊤ := by rw [Set.encard_eq_top] <;> exact h_inf
        exact_mod_cast h
      rw [h_top'] <;> simp
    · have hfin : Set.Finite C := Set.not_infinite.mp h_inf
      classical
      let Cfin : Finset AffineLine := hfin.toFinset
      have hCfin : (Cfin : Set AffineLine) = C := Set.Finite.coe_toFinset hfin
      let pick (c : AffineLine) : AffineLine :=
        if h : ∃ s, s ∈ S ∧ dist s c ≤ δ then
          Classical.choose h
        else
          s_default
      let D : Finset (ℝ × ℝ) := Cfin.image (fun c => f (pick c))
      have h_cover : Metric.IsCover ((16 * δ).toNNReal) (f '' S) (D : Set (ℝ × ℝ)) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hC hx with ⟨c, hc, hed⟩
        have hcfin : c ∈ Cfin := by
          have h1 : c ∈ (Cfin : Set AffineLine) := by simpa [hCfin] using hc
          exact_mod_cast h1
        have h_dist : dist x c ≤ δ := by
          have hfin1 : edist x c ≠ ⊤ := by exact edist_ne_top x c
          have hfin2 : (↑δ.toNNReal : ENNReal) ≠ ⊤ := by exact ENNReal.coe_ne_top
          have h3 : (edist x c).toReal ≤ (↑δ.toNNReal : ENNReal).toReal :=
            (ENNReal.toReal_le_toReal hfin1 hfin2).mpr hed
          have h4 : (edist x c).toReal = dist x c := by exact Eq.symm (dist_edist x c)
          have h5 : (↑δ.toNNReal : ENNReal).toReal = δ := by simp [hδ_pos.le]
          rw [←h4, ←h5]; exact h3
        set h_exists : ∃ (s : AffineLine), s ∈ S ∧ dist s c ≤ δ := ⟨x, hx, h_dist⟩ with h_exists_def
        set s : AffineLine := Classical.choose h_exists with hs_def
        have hs_in_S : s ∈ S := (Classical.choose_spec h_exists).1
        have hs_dist : dist s c ≤ δ := (Classical.choose_spec h_exists).2
        have h_pick_eq : pick c = s := by
          have h_unfold : pick c = (if h : ∃ (s : AffineLine), s ∈ S ∧ dist s c ≤ δ then Classical.choose h else s_default) := by rfl
          rw [h_unfold, dif_pos h_exists]
        have h_s_in_D : f s ∈ (D : Set (ℝ × ℝ)) := by
          rw [←h_pick_eq]
          exact Finset.mem_image.mpr ⟨c, hcfin, rfl⟩
        have h_dist2 : dist x s ≤ 2 * δ := by
          calc dist x s
            ≤ dist x c + dist c s := dist_triangle _ _ _
          _ = dist x c + dist s c := by rw [dist_comm c s]
          _ ≤ δ + δ := by linarith
          _ = 2 * δ := by ring
        have h_fdist : dist (f x) (f s) ≤ 16 * δ := by
          have h : dist (f x) (f s) ≤ 8 * dist x s := h_lip x s hx hs_in_S
          calc dist (f x) (f s)
            ≤ 8 * dist x s := h
          _ ≤ 8 * (2 * δ) := by gcongr
          _ = 16 * δ := by ring
        exact ⟨f s, h_s_in_D, dist_to_edist h16δ_nonneg h_fdist⟩
      have h_cover_enat : Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) ≤ (D : Set (ℝ × ℝ)).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard h_cover
      have h_cover_le : (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) ≤ ((D : Set (ℝ × ℝ)).encard : ENNReal) :=
        ENat.toENNReal_le.mpr h_cover_enat
      have h_card : D.card ≤ Cfin.card := Finset.card_image_le
      have h1 : (D : Set (ℝ × ℝ)).encard = D.card := by simp
      have h2 : C.encard = Cfin.card := by rw [← hCfin] <;> simp
      have h_encard : ((D : Set (ℝ × ℝ)).encard : ENNReal) ≤ (C.encard : ENNReal) := by
        rw [h1, h2] <;> exact_mod_cast h_card
      have h_one : (1 : ENNReal) * (C.encard : ENNReal) = (C.encard : ENNReal) := by simp
      rw [h_one]
      exact le_trans h_cover_le h_encard
  have h_transfer : (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) ≤
      (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) :=
    externalCoveringNumber_transfer h_main
  simpa using h_transfer

/-- Transfer S-set from AffineLine to parameter space ℝ².

    If T is a (δ,s,C)-set of affine lines with bounded slopes/intercepts,
    then affineLineParams '' T is a (12δ, s, C · 20^s · 1048576)-set in ℝ². -/
lemma affineLine_bounded_slope_sset_to_params
    {δ s C : ℝ} {T : Set AffineLine}
    (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (hT : IsDeltaSSet δ s C T)
    (h_bounds : ∀ ℓ ∈ T, (LemmaE.getDirV ℓ) 1 ≠ 0 ∧
      |(LemmaE.affineLineParams ℓ).1| ≤ 1 ∧ |(LemmaE.affineLineParams ℓ).2| ≤ 3) :
    IsDeltaSSet (16 * δ) s (C * (20 : ℝ) ^ s * 1048576)
      (LemmaE.affineLineParams '' T) := by
  let f : AffineLine → ℝ × ℝ := LemmaE.affineLineParams
  let P : Set (ℝ × ℝ) := f '' T
  have hT_nonempty : T.Nonempty := hT.1
  have hP_nonempty : P.Nonempty := hT_nonempty.image f
  have h16δ_pos : 0 < 16 * δ := by positivity
  have hC'_pos : 0 < C * (20 : ℝ) ^ s * 1048576 := by positivity
  have h_lip : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ T → ℓ₂ ∈ T →
      dist (f ℓ₁) (f ℓ₂) ≤ 8 * dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂ h1 h2
    have hb1_3 : |(LemmaE.affineLineParams ℓ₁).2| ≤ 3 := (h_bounds ℓ₁ h1).2.2
    have hb2_3 : |(LemmaE.affineLineParams ℓ₂).2| ≤ 3 := (h_bounds ℓ₂ h2).2.2
    exact affineLineParams_lipschitz_upper ℓ₁ ℓ₂ (h_bounds ℓ₁ h1).1 (h_bounds ℓ₂ h2).1
      (h_bounds ℓ₁ h1).2.1 (h_bounds ℓ₂ h2).2.1 hb1_3 hb2_3
  have h_antilip : ∀ (ℓ₁ ℓ₂ : AffineLine), ℓ₁ ∈ T → ℓ₂ ∈ T →
      dist ℓ₁ ℓ₂ ≤ 10 * dist (f ℓ₁) (f ℓ₂) := by
    intro ℓ₁ ℓ₂ h1 h2
    have hb1_3 : |(LemmaE.affineLineParams ℓ₁).2| ≤ 3 := (h_bounds ℓ₁ h1).2.2
    have hb2_3 : |(LemmaE.affineLineParams ℓ₂).2| ≤ 3 := (h_bounds ℓ₂ h2).2.2
    exact affineLineParams_antilipschitz ℓ₁ ℓ₂ (h_bounds ℓ₁ h1).1 (h_bounds ℓ₂ h2).1
      (h_bounds ℓ₁ h1).2.1 (h_bounds ℓ₂ h2).2.1 hb1_3 hb2_3
  have h_reverse_cover : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
      (Metric.externalCoveringNumber ((δ / 20).toNNReal) P : ENNReal) :=
    affineLine_reverse_cover hδ_pos hT_nonempty f h_antilip
  have h_refine1 : (Metric.externalCoveringNumber ((δ / 20).toNNReal) P : ENNReal) ≤
      ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((δ / 5).toNNReal) P : ENNReal) := by
    have h : Metric.externalCoveringNumber ((δ / 20).toNNReal) P ≤
        16 * Metric.externalCoveringNumber ((δ / 5).toNNReal) P :=
      covering_scale_2d (show (0 : ℝ) < δ / 20 by positivity) (show (0 : ℝ) < δ / 5 by positivity)
        (by linarith)
    exact_mod_cast h
  have h_refine2 : (Metric.externalCoveringNumber ((δ / 5).toNNReal) P : ENNReal) ≤
      ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((4 * δ / 5).toNNReal) P : ENNReal) := by
    have h : Metric.externalCoveringNumber ((δ / 5).toNNReal) P ≤
        16 * Metric.externalCoveringNumber ((4 * δ / 5).toNNReal) P :=
      covering_scale_2d (show (0 : ℝ) < δ / 5 by positivity) (show (0 : ℝ) < 4 * δ / 5 by positivity)
        (by linarith)
    exact_mod_cast h
  have h_refine3 : (Metric.externalCoveringNumber ((4 * δ / 5).toNNReal) P : ENNReal) ≤
      ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((16 * δ / 5).toNNReal) P : ENNReal) := by
    have h : Metric.externalCoveringNumber ((4 * δ / 5).toNNReal) P ≤
        16 * Metric.externalCoveringNumber ((16 * δ / 5).toNNReal) P :=
      covering_scale_2d (show (0 : ℝ) < 4 * δ / 5 by positivity) (show (0 : ℝ) < 16 * δ / 5 by positivity)
        (by linarith)
    exact_mod_cast h
  have h_refine4 : (Metric.externalCoveringNumber ((16 * δ / 5).toNNReal) P : ENNReal) ≤
      ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((64 * δ / 5).toNNReal) P : ENNReal) := by
    have h : Metric.externalCoveringNumber ((16 * δ / 5).toNNReal) P ≤
        16 * Metric.externalCoveringNumber ((64 * δ / 5).toNNReal) P :=
      covering_scale_2d (show (0 : ℝ) < 16 * δ / 5 by positivity) (show (0 : ℝ) < 64 * δ / 5 by positivity)
        (by linarith)
    exact_mod_cast h
  have h_refine5 : (Metric.externalCoveringNumber ((64 * δ / 5).toNNReal) P : ENNReal) ≤
      ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by
    have h : Metric.externalCoveringNumber ((64 * δ / 5).toNNReal) P ≤
        16 * Metric.externalCoveringNumber ((16 * δ).toNNReal) P :=
      covering_scale_2d (show (0 : ℝ) < 64 * δ / 5 by positivity) (show (0 : ℝ) < 16 * δ by positivity)
        (by linarith)
    exact_mod_cast h
  have h_refine_total : (Metric.externalCoveringNumber ((δ / 20).toNNReal) P : ENNReal) ≤
      ENNReal.ofReal (1048576 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by
    calc (Metric.externalCoveringNumber ((δ / 20).toNNReal) P : ENNReal)
      ≤ ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((δ / 5).toNNReal) P : ENNReal) := h_refine1
    _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((4 * δ / 5).toNNReal) P : ENNReal)) := by gcongr
    _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((16 * δ / 5).toNNReal) P : ENNReal))) := by gcongr
    _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((64 * δ / 5).toNNReal) P : ENNReal)))) := by gcongr
    _ ≤ ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (ENNReal.ofReal (16 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal))))) := by gcongr
    _ = ENNReal.ofReal (1048576 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by
      have h : ENNReal.ofReal (16 : ℝ) ^ 5 = ENNReal.ofReal (1048576 : ℝ) := by norm_num
      simp [h, pow_succ] <;> ring
  have h_Nδ_T_le : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
      ENNReal.ofReal (1048576 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by
    calc (Metric.externalCoveringNumber δ.toNNReal T : ENNReal)
      ≤ (Metric.externalCoveringNumber ((δ / 20).toNNReal) P : ENNReal) := h_reverse_cover
    _ ≤ ENNReal.ofReal (1048576 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := h_refine_total
  have h_main : ∀ (p : ℝ × ℝ) (r : ℝ), 16 * δ ≤ r →
      (Metric.externalCoveringNumber ((16 * δ).toNNReal) (P ∩ Metric.closedBall p r) : ENNReal) ≤
        ENNReal.ofReal (C * (20 : ℝ) ^ s * 1048576) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by
    intro p r hr
    by_cases h_empty : (P ∩ Metric.closedBall p r).Nonempty
    · rcases h_empty with ⟨q, hq⟩
      have hq_in_P : q ∈ P := hq.1
      rcases hq_in_P with ⟨ℓ, hℓ, rfl⟩
      let S : Set AffineLine := T ∩ Metric.closedBall ℓ (20 * r)
      have hS_nonempty : S.Nonempty := ⟨ℓ, ⟨hℓ, by
        have h : dist ℓ ℓ ≤ 20 * r := by
          simp [dist_self]
          <;> linarith
        exact h⟩⟩
      have h_preimage : P ∩ Metric.closedBall p r ⊆ f '' S := by
        intro z hz
        rcases hz.1 with ⟨ℓ', hℓ', rfl⟩
        have h_dist_f : dist (f ℓ') (f ℓ) ≤ 2 * r := by
          have h1 : dist (f ℓ') p ≤ r := hz.2
          have h2 : dist (f ℓ) p ≤ r := hq.2
          calc dist (f ℓ') (f ℓ)
            ≤ dist (f ℓ') p + dist p (f ℓ) := dist_triangle _ _ _
          _ = dist (f ℓ') p + dist (f ℓ) p := by rw [dist_comm p (f ℓ)]
          _ ≤ r + r := by linarith
          _ = 2 * r := by ring
        have h_dist' : dist ℓ' ℓ ≤ 20 * r := by
          have h1 : dist ℓ' ℓ ≤ 10 * dist (f ℓ') (f ℓ) := h_antilip ℓ' ℓ hℓ' hℓ
          linarith
        exact ⟨ℓ', ⟨hℓ', h_dist'⟩, rfl⟩
      have h_lip_S : ∀ (x y : AffineLine), x ∈ S → y ∈ S →
          dist (f x) (f y) ≤ 8 * dist x y := by
        intro x y hx hy
        exact h_lip x y hx.1 hy.1
      have h4 : (Metric.externalCoveringNumber ((16 * δ).toNNReal) (P ∩ Metric.closedBall p r) : ENNReal) ≤
          (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) := by
        have h : Metric.externalCoveringNumber ((16 * δ).toNNReal) (P ∩ Metric.closedBall p r) ≤
            Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) :=
          Metric.externalCoveringNumber_mono_set h_preimage
        exact ENat.toENNReal_le.mpr h
      have h5 : (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) :=
        affineLine_forward_cover hδ_pos hS_nonempty f h_lip_S
      have h6 : 20 * r ≥ δ := by linarith
      have h7 : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal (20 * r)) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) :=
        hT.2.2.2.2 ℓ (20 * r) h6
      have h8 : (ENNReal.ofReal (20 * r)) ^ s =
          ENNReal.ofReal ((20 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s := by
        have h81 : (ENNReal.ofReal (20 * r)) ^ s = ENNReal.ofReal ((20 * r) ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
        have h82 : (20 * r) ^ s = (20 : ℝ) ^ s * r ^ s := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
        have h83 : ENNReal.ofReal ((20 * r) ^ s) = ENNReal.ofReal ((20 : ℝ) ^ s * r ^ s) := by rw [h82]
        have h84 : ENNReal.ofReal ((20 : ℝ) ^ s * r ^ s) = ENNReal.ofReal ((20 : ℝ) ^ s) * ENNReal.ofReal (r ^ s) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        have h85 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg]
        rw [h81, h83, h84, h85]
      have h9 : ENNReal.ofReal C * ENNReal.ofReal ((20 : ℝ) ^ s) * ENNReal.ofReal (1048576 : ℝ) =
          ENNReal.ofReal (C * (20 : ℝ) ^ s * 1048576) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity)] <;> ring
      calc (Metric.externalCoveringNumber ((16 * δ).toNNReal) (P ∩ Metric.closedBall p r) : ENNReal)
        ≤ (Metric.externalCoveringNumber ((16 * δ).toNNReal) (f '' S) : ENNReal) := h4
      _ ≤ (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h5
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (20 * r)) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := h7
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal ((20 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
            (ENNReal.ofReal (1048576 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal)) := by
          rw [h8] <;> gcongr <;> exact h_Nδ_T_le
      _ = ENNReal.ofReal (C * (20 : ℝ) ^ s * 1048576) * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by
        have h10 : ENNReal.ofReal C * (ENNReal.ofReal ((20 : ℝ) ^ s) * (ENNReal.ofReal r) ^ s) *
              (ENNReal.ofReal (1048576 : ℝ) * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal)) =
            ENNReal.ofReal C * ENNReal.ofReal ((20 : ℝ) ^ s) * ENNReal.ofReal (1048576 : ℝ) *
              (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber ((16 * δ).toNNReal) P : ENNReal) := by ring
        rw [h10, h9] <;> ring
    · have h_empty' : P ∩ Metric.closedBall p r = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h_empty
      rw [h_empty']
      simp
  exact ⟨hP_nonempty, h16δ_pos, hC'_pos, hs_nonneg, h_main⟩

/-! ### Snapping transfer for S-sets in ℝ×ℝ (max metric) -/

/-- Helper: N_δ(f '' S) ≤ 16 * N_δ(S) when f moves points by ≤ δ/2 in max metric. -/
lemma ncover_snap_upper_prod {δ : ℝ} (hδ : 0 < δ) {S : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ × ℝ} (hf : ∀ x, dist x (f x) ≤ δ / 2) :
    Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤
      16 * Metric.externalCoveringNumber δ.toNNReal S := by
  by_cases htop : Metric.externalCoveringNumber δ.toNNReal S = ⊤
  · rw [htop]; simp
  · rcases exists_minimal_external_cover htop with ⟨C, hC, hCeq⟩
    have h3δ2_pos : 0 < (3 * δ / 2).toNNReal := by positivity
    have hCover : Metric.IsCover δ.toNNReal S C := hC
    have hC' : Metric.IsCover ((3 * δ / 2).toNNReal) (f '' S) C := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have h_ex : ∃ c ∈ C, edist x c ≤ ↑δ.toNNReal := hCover (x := x) hx
      rcases h_ex with ⟨c, hcC, hdist_edist⟩
      have hdist_dist : dist x c ≤ δ := by
        have h1 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
        have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal (δ : ℝ) := by exact ENNReal.ofNNReal_toNNReal δ
        rw [h1, h2] at hdist_edist
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdist_edist
      have hdist' : dist (f x) c ≤ 3 * δ / 2 := by
        calc dist (f x) c ≤ dist (f x) x + dist x c := dist_triangle _ _ _
          _ ≤ δ / 2 + δ := by
            have hfa : dist x (f x) ≤ δ / 2 := hf x
            have hfb : dist (f x) x ≤ δ / 2 := by rwa [dist_comm]
            linarith
          _ = 3 * δ / 2 := by ring
      have hfinal : edist (f x) c ≤ ↑(3 * δ / 2).toNNReal := by
        have h1 : edist (f x) c = ENNReal.ofReal (dist (f x) c) := edist_dist (f x) c
        have h2 : (↑(3 * δ / 2).toNNReal : ENNReal) = ENNReal.ofReal ((3 * δ / 2 : ℝ)) := by exact ENNReal.ofNNReal_toNNReal (3 * δ / 2)
        rw [h1, h2]
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr hdist'
      exact ⟨c, hcC, hfinal⟩
    have h1 : Metric.externalCoveringNumber ((3 * δ / 2).toNNReal) (f '' S) ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'
    have h2 : Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤
        16 * Metric.externalCoveringNumber ((3 * δ / 2).toNNReal) (f '' S) :=
      covering_scale_2d hδ (by positivity) (by linarith)
    have h3 : Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤ 16 * C.encard := by
      calc
        Metric.externalCoveringNumber δ.toNNReal (f '' S)
          ≤ 16 * Metric.externalCoveringNumber ((3 * δ / 2).toNNReal) (f '' S) := h2
        _ ≤ 16 * C.encard := by gcongr
    rw [hCeq] at h3
    exact h3

/-- Helper: N_δ(S) ≤ 16 * N_δ(f '' S) when f moves points by ≤ δ/2. -/
lemma ncover_snap_lower_prod {δ : ℝ} (hδ : 0 < δ) {S : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℝ × ℝ} (hf : ∀ x, dist x (f x) ≤ δ / 2) :
    Metric.externalCoveringNumber δ.toNNReal S ≤
      16 * Metric.externalCoveringNumber δ.toNNReal (f '' S) := by
  by_cases htop : Metric.externalCoveringNumber δ.toNNReal (f '' S) = ⊤
  · rw [htop]; simp
  · rcases exists_minimal_external_cover htop with ⟨C, hC, hCeq⟩
    have hCover : Metric.IsCover δ.toNNReal (f '' S) C := hC
    have hC' : Metric.IsCover ((3 * δ / 2).toNNReal) S C := by
      intro x hx
      have h_ex : ∃ c ∈ C, edist (f x) c ≤ ↑δ.toNNReal := hCover (x := f x) (Set.mem_image_of_mem f hx)
      rcases h_ex with ⟨c, hcC, hdist_edist⟩
      have hdist_dist : dist (f x) c ≤ δ := by
        have h1 : edist (f x) c = ENNReal.ofReal (dist (f x) c) := edist_dist (f x) c
        have h2 : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal (δ : ℝ) := by exact ENNReal.ofNNReal_toNNReal δ
        rw [h1, h2] at hdist_edist
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdist_edist
      have hdist' : dist x c ≤ 3 * δ / 2 := by
        calc dist x c ≤ dist x (f x) + dist (f x) c := dist_triangle _ _ _
          _ ≤ δ / 2 + δ := by
            have hfa : dist x (f x) ≤ δ / 2 := hf x
            linarith
          _ = 3 * δ / 2 := by ring
      have hfinal : edist x c ≤ ↑(3 * δ / 2).toNNReal := by
        have h1 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
        have h2 : (↑(3 * δ / 2).toNNReal : ENNReal) = ENNReal.ofReal ((3 * δ / 2 : ℝ)) := by exact ENNReal.ofNNReal_toNNReal (3 * δ / 2)
        rw [h1, h2]
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr hdist'
      exact ⟨c, hcC, hfinal⟩
    have h1 : Metric.externalCoveringNumber ((3 * δ / 2).toNNReal) S ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'
    have h2 : Metric.externalCoveringNumber δ.toNNReal S ≤
        16 * Metric.externalCoveringNumber ((3 * δ / 2).toNNReal) S :=
      covering_scale_2d hδ (by positivity) (by linarith)
    have h3 : Metric.externalCoveringNumber δ.toNNReal S ≤ 16 * C.encard := by
      calc
        Metric.externalCoveringNumber δ.toNNReal S
          ≤ 16 * Metric.externalCoveringNumber ((3 * δ / 2).toNNReal) S := h2
        _ ≤ 16 * C.encard := by gcongr
    rw [hCeq] at h3
    exact h3

/-- Snapping transfer for S-sets in ℝ×ℝ (max metric).
    If P is a (δ,s,C)-set and f moves each point by ≤ δ/2,
    then f '' P is a (δ,s,256·(3/2)^s·C)-set. -/
lemma IsDeltaSSet.snap_prod {δ s C : ℝ} {P : Set (ℝ × ℝ)}
    (h : IsDeltaSSet δ s C P)
    (f : ℝ × ℝ → ℝ × ℝ) (hf : ∀ x, dist x (f x) ≤ δ / 2) :
    IsDeltaSSet δ s (256 * (3 / 2 : ℝ)^s * C) (f '' P) := by
  let P' := f '' P
  have hδ_pos : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  have hC'_pos : 0 < 256 * (3 / 2 : ℝ)^s * C := by positivity
  have hP_nonempty : P.Nonempty := h.1
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image f
  have h_upper : (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) ≤
      (16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    exact_mod_cast ncover_snap_upper_prod hδ_pos hf
  have h_lower : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := by
    exact_mod_cast ncover_snap_lower_prod hδ_pos hf
  refine ⟨hP'_nonempty, hδ_pos, hC'_pos, hs, fun x r hr => ?_⟩
  set r' : ℝ := r + δ / 2 with hr'_def
  have hr'_ge : δ ≤ r' := by
    dsimp only [r']
    have h_pos : 0 < δ / 2 := by positivity
    linarith
  have hr'_le : r' ≤ (3 / 2 : ℝ) * r := by
    dsimp only [r']
    have h1 : δ ≤ r := hr
    have h2 : 0 ≤ r := by linarith
    have h3 : δ / 2 ≤ r / 2 := by gcongr
    linarith
  have h_inter1 : P' ∩ Metric.closedBall x r ⊆
      f '' (P ∩ Metric.closedBall x r') := by
    intro z hz
    rcases hz.1 with ⟨a, ha, rfl⟩
    have hdist : dist (f a) x ≤ r := by simpa [Metric.mem_closedBall] using hz.2
    have hdist2 : dist a x ≤ r + δ / 2 := by
      calc dist a x
        ≤ dist a (f a) + dist (f a) x := dist_triangle _ _ _
      _ ≤ δ / 2 + r := by
        have hfa : dist a (f a) ≤ δ / 2 := hf a
        linarith
      _ = r + δ / 2 := by ring
    exact ⟨a, ⟨ha, by simpa [Metric.mem_closedBall] using hdist2⟩, rfl⟩
  have h_cover1 : (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (f '' (P ∩ Metric.closedBall x r')) : ENNReal) := by
    have h := Metric.externalCoveringNumber_mono_set (ε := δ.toNNReal) h_inter1
    exact_mod_cast h
  have h_cover2 : (Metric.externalCoveringNumber δ.toNNReal (f '' (P ∩ Metric.closedBall x r')) : ENNReal) ≤
      (16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r') : ENNReal) := by
    exact_mod_cast ncover_snap_upper_prod hδ_pos hf
  have h_sset : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r') : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r') ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    h.2.2.2.2 x r' hr'_ge
  have h_rpow_mono : (ENNReal.ofReal r') ^ s ≤ (ENNReal.ofReal ((3 / 2 : ℝ) * r)) ^ s := by
    gcongr <;> linarith
  have hpos1 : 0 < (3 / 2 : ℝ) := by norm_num
  have h_expand : ENNReal.ofReal ((3 / 2 : ℝ) * r) ^ s =
      ENNReal.ofReal ((3 / 2 : ℝ)^s) * (ENNReal.ofReal r) ^ s := by
    have h9 : ENNReal.ofReal ((3 / 2 : ℝ) * r) =
        ENNReal.ofReal (3 / 2 : ℝ) * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul hpos1.le] <;> ring
    rw [h9]
    have h10 : (ENNReal.ofReal (3 / 2 : ℝ) * ENNReal.ofReal r) ^ s =
        (ENNReal.ofReal (3 / 2 : ℝ)) ^ s * (ENNReal.ofReal r) ^ s :=
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith)
    rw [h10]
    have h11 : (ENNReal.ofReal (3 / 2 : ℝ)) ^ s =
        ENNReal.ofReal ((3 / 2 : ℝ) ^ s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
    rw [h11] <;> ring
  calc
    (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (f '' (P ∩ Metric.closedBall x r')) : ENNReal) := h_cover1
    _ ≤ (16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r') : ENNReal) := h_cover2
    _ ≤ (16 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r') ^ s * (Metric.externalCoveringNumber δ.toNNReal P)) := by gcongr
    _ ≤ (16 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((3 / 2 : ℝ) * r)) ^ s * (Metric.externalCoveringNumber δ.toNNReal P)) := by gcongr
    _ ≤ (16 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((3 / 2 : ℝ)^s) * (ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal P)) := by
        rw [h_expand] <;> ring
    _ ≤ (16 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal ((3 / 2 : ℝ)^s) * (ENNReal.ofReal r) ^ s) * ((16 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P'))) := by
        gcongr <;> exact h_lower
    _ = ENNReal.ofReal (256 * (3 / 2 : ℝ)^s * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P') := by
        have h_const : ENNReal.ofReal (256 * (3 / 2 : ℝ)^s * C) =
            (16 : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal ((3 / 2 : ℝ)^s) * (16 : ENNReal) := by
          have hC_nonneg : 0 ≤ C := by linarith
          have h1 : ENNReal.ofReal (256 * (3 / 2 : ℝ)^s * C) =
              ENNReal.ofReal (256 * (3 / 2 : ℝ)^s) * ENNReal.ofReal C := by
            rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
          rw [h1]
          have h2 : ENNReal.ofReal (256 * (3 / 2 : ℝ)^s) =
              (256 : ENNReal) * ENNReal.ofReal ((3 / 2 : ℝ)^s) := by
            have h21 : ENNReal.ofReal (256 * (3 / 2 : ℝ)^s) =
                ENNReal.ofReal (256 : ℝ) * ENNReal.ofReal ((3 / 2 : ℝ)^s) := by
              rw [← ENNReal.ofReal_mul (by norm_num)] <;> ring
            rw [h21]
            have h22 : ENNReal.ofReal (256 : ℝ) = (256 : ENNReal) := by norm_cast
            rw [h22] <;> ring
          rw [h2] <;> ring
        rw [h_const] <;> ring

/-- Translation preserves S-sets on ℝ×ℝ. -/
lemma IsDeltaSSet.translate_prod {δ s C : ℝ} {P : Set (ℝ × ℝ)} {v : ℝ × ℝ}
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C ((fun x => x + v) '' P) := by
  let τ : ℝ × ℝ → ℝ × ℝ := fun x => x + v
  let τinv : ℝ × ℝ → ℝ × ℝ := fun x => x - v
  let P' := τ '' P
  have hδ_pos : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs : 0 ≤ s := h.2.2.2.1
  have hP_nonempty : P.Nonempty := h.1
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image τ
  have h_iso : Isometry τ := by
    intro x y
    simp [τ, dist_eq_norm] <;> abel
  have h_iso_inv : Isometry τinv := by
    intro x y
    simp [τinv, dist_eq_norm] <;> abel
  have h_left_inv : τinv ∘ τ = id := by funext x; simp [τ, τinv] <;> ring
  have h_right_inv : τ ∘ τinv = id := by funext x; simp [τ, τinv] <;> ring
  have h_cover : ∀ (S : Set (ℝ × ℝ)),
      Metric.externalCoveringNumber δ.toNNReal (τ '' S) = Metric.externalCoveringNumber δ.toNNReal S := by
    intro S
    have h1 : Metric.externalCoveringNumber δ.toNNReal (τ '' S) ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
      have h : ∀ (C : Set (ℝ × ℝ)), Metric.IsCover δ.toNNReal S C →
          Metric.externalCoveringNumber δ.toNNReal (τ '' S) ≤ C.encard := by
        intro C hC
        have hC' : Metric.IsCover δ.toNNReal (τ '' S) (τ '' C) :=
          (h_iso.isCover_image_iff C).mpr hC
        have h_card : (τ '' C).encard = C.encard := h_iso.injective.encard_image C
        have h_le : Metric.externalCoveringNumber δ.toNNReal (τ '' S) ≤ (τ '' C).encard :=
          Metric.IsCover.externalCoveringNumber_le_encard hC'
        rw [h_card] at h_le
        exact h_le
      simpa [Metric.externalCoveringNumber] using le_iInf₂ h
    have h2 : Metric.externalCoveringNumber δ.toNNReal S ≤
        Metric.externalCoveringNumber δ.toNNReal (τ '' S) := by
      have h : ∀ (D : Set (ℝ × ℝ)), Metric.IsCover δ.toNNReal (τ '' S) D →
          Metric.externalCoveringNumber δ.toNNReal S ≤ D.encard := by
        intro D hD
        have hD1 : Metric.IsCover δ.toNNReal (τinv '' (τ '' S)) (τinv '' D) := by
          have hD2 := Metric.IsCover.image_lipschitz hD h_iso_inv.lipschitz
          have h_simp : (1 : NNReal) * δ.toNNReal = δ.toNNReal := by simp
          rw [h_simp] at hD2
          exact hD2
        have h_image_eq : τinv '' (τ '' S) = S := by
          ext x
          simp only [Set.mem_image, τ, τinv]
          constructor
          · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
            simpa using hz
          · intro hx
            refine ⟨x + v, ⟨x, hx, by ring⟩, by ring⟩
        rw [h_image_eq] at hD1
        have h_card : (τinv '' D).encard ≤ D.encard := Set.encard_image_le τinv D
        have h_le : Metric.externalCoveringNumber δ.toNNReal S ≤ (τinv '' D).encard :=
          Metric.IsCover.externalCoveringNumber_le_encard hD1
        exact le_trans h_le h_card
      simpa [Metric.externalCoveringNumber] using le_iInf₂ h
    exact le_antisymm h1 h2
  refine ⟨hP'_nonempty, hδ_pos, hC_pos, hs, fun x r hr => ?_⟩
  have h_inter : P' ∩ Metric.closedBall x r = τ '' (P ∩ Metric.closedBall (x - v) r) := by
    ext z
    simp only [P', Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hball⟩
      have hball2 : dist y (x - v) ≤ r := by
        have h_eq : y + v - x = y - (x - v) := by ring
        simpa [τ, dist_eq_norm, h_eq] using hball
      exact ⟨y, ⟨hy, hball2⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hball⟩, rfl⟩
      have hball2 : dist (y + v) x ≤ r := by
        have h_eq : y - (x - v) = y + v - x := by ring
        simpa [τ, dist_eq_norm, h_eq] using hball
      exact ⟨⟨y, hy, rfl⟩, hball2⟩
  rw [h_inter]
  have h5 : Metric.externalCoveringNumber δ.toNNReal (τ '' (P ∩ Metric.closedBall (x - v) r)) =
      Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall (x - v) r) :=
    h_cover (P ∩ Metric.closedBall (x - v) r)
  rw [h5]
  have h6 : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall (x - v) r) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber δ.toNNReal P :=
    h.2.2.2.2 (x - v) r hr
  have h7 : Metric.externalCoveringNumber δ.toNNReal P =
      Metric.externalCoveringNumber δ.toNNReal P' :=
    (h_cover P).symm
  rw [h7] at h6
  exact h6

/-- Convert IsDeltaSSet to IsRescalableDeltaSet.
    If P is a (δ,s,C)-set and δ ≤ Δ², then it is a rescalable set with constant C * Δ^s. -/
lemma IsDeltaSSet.to_rescalable {X : Type*} [PseudoMetricSpace X]
    {δ Δ s C : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P)
    (hδ_le_Δ2 : δ ≤ Δ^2) (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) :
    IsRescalableDeltaSet δ Δ s (C * Δ^s) P := by
  have hC_pos : 0 < C := h.2.2.1
  have hC'_pos : 0 < C * Δ^s := by positivity
  refine ⟨h.1, h.2.1, hΔ_pos, hC'_pos, hs, fun x r hr => ?_⟩
  have h_r_nonneg : 0 ≤ r := by linarith
  have h1 : δ ≤ Δ * r := by
    calc δ ≤ Δ^2 := hδ_le_Δ2
       _ = Δ * Δ := by ring
       _ ≤ Δ * r := by
         apply mul_le_mul_of_nonneg_left hr (by linarith)
  have h2 := h.2.2.2.2 x (Δ * r) h1
  have h41 : 0 ≤ Δ := by linarith
  have h_mul1 : ENNReal.ofReal (Δ * r) = ENNReal.ofReal Δ * ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul (show 0 ≤ Δ by linarith)] <;> ring
  have h3 : (ENNReal.ofReal (Δ * r)) ^ s =
      ENNReal.ofReal (Δ^s) * (ENNReal.ofReal r) ^ s := by
    rw [h_mul1, ENNReal.mul_rpow_of_nonneg _ _ hs]
    have h5 : (ENNReal.ofReal Δ) ^ s = ENNReal.ofReal (Δ^s) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg h41 hs]
    rw [h5] <;> ring
  rw [h3] at h2
  have hΔs_nonneg : 0 ≤ Δ^s := Real.rpow_nonneg (by linarith) s
  have hCΔ : ENNReal.ofReal C * ENNReal.ofReal (Δ^s) = ENNReal.ofReal (C * Δ^s) := by
    have hC_nonneg : 0 ≤ C := by linarith
    have h : (ENNReal.ofReal (C * Δ^s)) = ENNReal.ofReal C * ENNReal.ofReal (Δ^s) := by exact ENNReal.ofReal_mul hC_nonneg
    exact h.symm
  have h4 : ENNReal.ofReal C * (ENNReal.ofReal (Δ^s) * (ENNReal.ofReal r) ^ s) *
        (Metric.externalCoveringNumber δ.toNNReal P) =
      ENNReal.ofReal (C * Δ^s) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P) := by
    rw [← hCΔ] <;> ring
  rw [h4] at h2
  exact h2

/-- Full assembly: FineTube S-set → IsRescalableDeltaSet on ℝ×ℝ cell params.

    Chain:
    1. affineLine_bounded_slope_sset_to_params: δ → 12δ, constant ×20^s×1048576
    2. translate by v: isometry, no loss
    3. snap to grid at scale 12δ (perturbation ≤ 6δ): constant ×256×(3/2)^s
    4. scale_down2: 12δ → 3δ → δ, constant ×256×16^s
    5. to_rescalable: δ → Δ, constant ×Δ^s
-/
lemma fine_tube_sset_to_cell_rescalable
    {δ Δ s C : ℝ} {Tubes : Set AffineLine}
    (hT_sset : IsDeltaSSet δ s C Tubes)
    (h_bounds : ∀ T ∈ Tubes,
      (LemmaE.getDirV T) 1 ≠ 0 ∧
      |(LemmaE.affineLineParams T).1| ≤ 1 ∧
      |(LemmaE.affineLineParams T).2| ≤ 3)
    (v : ℝ × ℝ)
    (snap : ℝ × ℝ → ℝ × ℝ)
    (hsnap : ∀ p, dist p (snap p) ≤ δ)
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hδ_eq : δ = Δ^2) (hs : 0 ≤ s) :
    IsRescalableDeltaSet δ Δ s
      (C * (20 : ℝ)^s * 1048576 * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s * Δ^s)
      (snap '' ((fun x => x + v) '' (LemmaE.affineLineParams '' Tubes))) := by
  have hC_pos : 0 < C := hT_sset.2.2.1
  -- Step 1: FineTube → params at scale 12δ
  have h1 : IsDeltaSSet (16 * δ) s (C * (20 : ℝ)^s * 1048576)
      (LemmaE.affineLineParams '' Tubes) :=
    affineLine_bounded_slope_sset_to_params hδ_pos hs hC_pos hT_sset h_bounds
  -- Step 2: translate
  have h2 : IsDeltaSSet (16 * δ) s (C * (20 : ℝ)^s * 1048576)
      ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes)) :=
    IsDeltaSSet.translate_prod h1
  -- Step 3: snap at scale 12δ (perturbation δ ≤ (12δ)/2 = 6δ)
  set δ12 := 16 * δ with hδ12_def
  have hδ12_pos : 0 < δ12 := by positivity
  have hsnap12 : ∀ p, dist p (snap p) ≤ δ12 / 2 := by
    intro p
    have h : δ ≤ δ12 / 2 := by
      dsimp only [δ12] <;> linarith
    exact le_trans (hsnap p) h
  have h3_raw : IsDeltaSSet δ12 s
      (256 * (3 / 2 : ℝ)^s * (C * (20 : ℝ)^s * 1048576))
      (snap '' ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes))) :=
    IsDeltaSSet.snap_prod h2 snap hsnap12
  have h_const3 : 256 * (3 / 2 : ℝ)^s * (C * (20 : ℝ)^s * 1048576) =
      (C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s := by ring
  have h3 : IsDeltaSSet δ12 s
      ((C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s)
      (snap '' ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes))) := by
    rw [h_const3] at h3_raw
    exact h3_raw
  -- Step 4: scale down 16δ → 4δ → δ
  have h4δ_pos : 0 < 4 * δ := by positivity
  have h_step4a : IsDeltaSSet (4 * δ) s
      (((C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s) * 16 * (4 : ℝ)^s)
      (snap '' ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes))) :=
    IsDeltaSSet.scale_down2 h4δ_pos hδ12_pos (by linarith) (by linarith) h3
  have h_step4b : IsDeltaSSet δ s
      ((((C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s) * 16 * (4 : ℝ)^s) * 16 * (4 : ℝ)^s)
      (snap '' ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes))) :=
    IsDeltaSSet.scale_down2 hδ_pos h4δ_pos (by linarith) (by linarith) h_step4a
  have h4s : (4 : ℝ)^s * (4 : ℝ)^s = (16 : ℝ)^s := by
    have h : (4 : ℝ)^s * (4 : ℝ)^s = (4 * 4 : ℝ)^s := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)] <;> norm_num
    rw [h] <;> norm_num
  have h_const4 : ((((C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s) * 16 * (4 : ℝ)^s) * 16 * (4 : ℝ)^s) =
      (C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s := by
    calc
      ((((C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s) * 16 * (4 : ℝ)^s) * 16 * (4 : ℝ)^s)
        = (C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s * (16 * 16) * ((4 : ℝ)^s * (4 : ℝ)^s) := by ring
      _ = (C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s := by rw [h4s] <;> ring
  have h_step4 : IsDeltaSSet δ s
      ((C * (20 : ℝ)^s * 1048576) * 256 * (3 / 2 : ℝ)^s * 256 * (16 : ℝ)^s)
      (snap '' ((fun x : ℝ × ℝ => x + v) '' (LemmaE.affineLineParams '' Tubes))) := by
    rw [h_const4] at h_step4b
    exact h_step4b
  -- Step 5: convert to rescalable
  have hδ_le_Δ2 : δ ≤ Δ^2 := by rw [hδ_eq]
  exact IsDeltaSSet.to_rescalable h_step4 hδ_le_Δ2 hΔ_pos hs

end DirecretisedFurstenbergEstimate.A10
