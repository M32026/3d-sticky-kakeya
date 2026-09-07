import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjectionFiber
import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSanity

/-!
# Kaufman projection application for the faithful Lemma 8.13 closing

Given the faithful Kaufman input data, build the incidence graph explicitly
and apply the fiber-output Kaufman projection theorem.  The selected direction
comes from the radial direction set, and the covering bound is stated on the
original tripartite fiber.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open Finset Metric
attribute [local instance] Classical.propDecidable

private def fiber (H : Finset (Point2 × Point2)) (θ : Point2) : Finset Point2 :=
  (H.filter (fun h => h.1 = θ)).image (fun h => h.2)

/-- Apply the Kaufman projection theorem to the faithful Kaufman input data. -/
lemma wz1_lemma8_13_faithful_kaufman_projection
    {delta epsilon : ℝ}
    {input : WZ1Lemma8_13ResidualInput delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    (kaufman : WZ1Lemma8_13FaithfulKaufmanInputData affine) :
    ∃ (direction : Point2), direction ∈ kaufman.radial.directions ∧
      ENNReal.ofReal
          (wz1Lemma8_13FaithfulGraphDensity delta epsilon ^ 2 /
            (2 * kaufman_total_const (max 1 kaufman.commonConstant) 1 1
                (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2) *
              (2 : ℝ) ^ (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2))) *
        Kakeya.realRpowENN (wz1Lemma8_13FaithfulAngularScale input)
          (-(2 * wz1Lemma8_13FaithfulNormalizedEta epsilon + 1 - epsilon / 2)) ≤
      (↑(Metric.externalCoveringNumber
          (Real.toNNReal (wz1Lemma8_13FaithfulAngularScale input))
          (inner ℝ direction ''
            (kaufmanFiber kaufman.finalH
              (kaufman.firstEndpoint direction)
              (kaufman.secondEndpoint direction) : Set Point2))) : ENNReal) := by
  let normalizedEta := wz1Lemma8_13FaithfulNormalizedEta epsilon
  let gamma := 2 * normalizedEta + 1 - epsilon / 2
  let angularScale := wz1Lemma8_13FaithfulAngularScale input
  let graphDensity := wz1Lemma8_13FaithfulGraphDensity delta epsilon
  let F := kaufman.finalF
  let Λ := kaufman.radial.directions
  let b1 := kaufman.firstEndpoint
  let b2 := kaufman.secondEndpoint
  let H := kaufman.finalH
  let C := kaufman.commonConstant
  let d := graphDensity
  let Hk : Finset (Point2 × Point2) := kaufmanIncidenceGraph Λ b1 b2 H

  have hepsilon_pos : 0 < epsilon := by
    have h1 : 0 < normalizedEta := kaufman.normalizedEta_pos
    have h2 : normalizedEta < epsilon / 4 := kaufman.normalizedEta_lt_epsilon_quarter
    linarith

  have hgamma_pos : 0 < gamma := by
    dsimp only [gamma, normalizedEta, wz1Lemma8_13FaithfulNormalizedEta]
    nlinarith [sq_nonneg (epsilon - 25 / 8)]

  have hgamma_lt_one : gamma < 1 := by
    dsimp only [gamma]
    have h2 : 2 * normalizedEta < epsilon / 2 := by
      linarith [kaufman.normalizedEta_lt_epsilon_quarter]
    linarith

  have hangularScale_pos : 0 < angularScale := affine.angularScale_pos
  have hangularScale_le_one : angularScale ≤ 1 := by
    have h : angularScale ≤ 1 / 4 := affine.angularScale_le_quarter
    linarith
  have hC : 0 ≤ C := by linarith [kaufman.commonConstant_ge_one]
  have hd_pos : 0 < d := wz1Lemma8_13_graphDensity_pos hdelta
  have hneF : F.Nonempty := kaufman.finalF_nonempty
  have hΛ_nonempty : Λ.Nonempty := kaufman.radial.directions_nonempty

  have hF_frost : F.IsFrostman angularScale 1 (ENNReal.ofReal C) :=
    kaufman.finalF_frostman
  have hΛ_frost : Λ.IsFrostman angularScale 1 (ENNReal.ofReal C) :=
    kaufman.radial.frostman
  have hF_sep : F.IsDeltaSeparated angularScale :=
    kaufman.finalF_separated
  have hΛ_sep : Λ.IsDeltaSeparated angularScale :=
    kaufman.radial.separated
  have hF_ball : F.IsInUnitBall := kaufman.finalF_ball
  have hunit : ∀ θ ∈ Λ, ‖θ‖ = 1 := kaufman.radial.unit

  have hb1 : ∀ θ ∈ Λ, b1 θ ∈ kaufman.finalG₁ := kaufman.firstEndpoint_mem
  have hb2 : ∀ θ ∈ Λ, b2 θ ∈ kaufman.finalG₂ := kaufman.secondEndpoint_mem
  have hH_support : ∀ e ∈ H, e.1 ∈ F ∧ e.2.1 ∈ kaufman.finalG₁ ∧ e.2.2 ∈ kaufman.finalG₂ :=
    kaufman.finalSupport

  have hfiber : ∀ θ ∈ Λ,
      ((kaufmanFiber H (b1 θ) (b2 θ)).card : ENNReal) ≥
        ENNReal.ofReal d * F.enncard := by
    intro θ hθ
    simpa [graphDensity] using kaufman.fiber_density θ hθ

  have hHk_sub : ∀ h ∈ Hk, h.1 ∈ Λ ∧ h.2 ∈ F := by
    intro h hh
    have h_ex : ∃ (θ : Point2), θ ∈ Λ ∧
        h ∈ (kaufmanFiber H (b1 θ) (b2 θ)).image (fun f => (θ, f)) := by
      simpa [Hk, kaufmanIncidenceGraph, Finset.mem_biUnion] using hh
    rcases h_ex with ⟨θ, hθ, h_in_image⟩
    rcases Finset.mem_image.mp h_in_image with ⟨f, hf, h_eq⟩
    have h_h_eq : h = (θ, f) := h_eq.symm
    rcases Finset.mem_image.mp hf with ⟨e, he, h_e_eq⟩
    have h2 : e.1 ∈ F := (hH_support e (Finset.mem_filter.mp he).1).1
    have h3 : h.1 = θ := by simp [h_h_eq]
    have h4 : h.2 = e.1 := by simp [h_h_eq, h_e_eq]
    exact ⟨by rw [h3]; exact hθ, by rw [h4]; exact h2⟩

  have h_filter_eq : ∀ θ ∈ Λ,
      Hk.filter (fun h : Point2 × Point2 => h.1 = θ) =
        (kaufmanFiber H (b1 θ) (b2 θ)).image (fun f => (θ, f)) := by
    intro θ hθ
    ext p
    simp only [Hk, kaufmanIncidenceGraph, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨θ', hθ', f, hf, h_eq_pair⟩, hx1⟩
      have h_p1 : p.1 = θ' := (congr_arg Prod.fst h_eq_pair).symm
      have h_θ'_eq : θ' = θ := by
        rw [h_p1] at hx1; exact hx1
      have hf' : f ∈ kaufmanFiber H (b1 θ) (b2 θ) := by
        rw [h_θ'_eq] at hf; exact hf
      refine ⟨f, hf', ?_⟩
      have h_goal : (θ, f) = p := by
        have h : (θ, f) = (θ', f) := by ext <;> simp [h_θ'_eq]
        exact h.trans h_eq_pair
      exact h_goal
    · rintro ⟨f, hf, h_eq_pair⟩
      have h_p1 : p.1 = θ := (congr_arg Prod.fst h_eq_pair).symm
      exact ⟨⟨θ, hθ, f, hf, h_eq_pair⟩, h_p1⟩

  have hHk_dense : ∀ θ ∈ Λ,
      ((Hk.filter (fun h => h.1 = θ)).card : ENNReal) ≥
        ENNReal.ofReal d * F.enncard := by
    intro θ hθ
    rw [h_filter_eq θ hθ]
    have h_inj : Set.InjOn (fun f : Point2 => (θ, f))
        (kaufmanFiber H (b1 θ) (b2 θ) : Set Point2) := by
      intro f1 _ f2 _ h; simpa using h
    rw [Finset.card_image_of_injOn h_inj]
    exact hfiber θ hθ

  have h_fiber_eq : ∀ θ ∈ Λ, fiber Hk θ = kaufmanFiber H (b1 θ) (b2 θ) := by
    intro θ hθ
    dsimp only [fiber]
    rw [h_filter_eq θ hθ]
    rw [Finset.image_image]
    have h_comp : ((fun h : Point2 × Point2 => h.2) ∘ (fun f : Point2 => (θ, f))) = id := by
      funext x
      simp
    rw [h_comp]
    simp

  have h_dense_real : ∀ θ ∈ Λ, (fiber Hk θ).card ≥ d * F.card := by
    intro θ hθ
    have h1 : (fiber Hk θ).card = (Hk.filter (fun h => h.1 = θ)).card := by
      have h_inj : Set.InjOn (fun h : Point2 × Point2 => h.2)
          (Hk.filter (fun h => h.1 = θ) : Set (Point2 × Point2)) := by
        intro h1 hh1 h2 hh2 h
        have h_eq2 : h1.2 = h2.2 := h
        have h11 : h1.1 = θ := (Finset.mem_filter.mp hh1).2
        have h21 : h2.1 = θ := (Finset.mem_filter.mp hh2).2
        have h_eq1 : h1.1 = h2.1 := by rw [h11, h21]
        exact Prod.ext h_eq1 h_eq2
      rw [fiber, Finset.card_image_of_injOn h_inj]
    rw [h1]
    have h_enreal : ((Hk.filter (fun h => h.1 = θ)).card : ENNReal) ≥
        ENNReal.ofReal d * F.enncard := hHk_dense θ hθ
    have h_d_nonneg : 0 ≤ d := by linarith
    have h_enncard : F.enncard = ENNReal.ofReal (F.card : ℝ) := by
      have h2 : F.enncard = (↑F.card : ENNReal) := by rfl
      rw [h2]
      exact Eq.symm (ENNReal.ofReal_natCast F.card)
    have h_mul : ENNReal.ofReal d * F.enncard =
        ENNReal.ofReal (d * (F.card : ℝ)) := by
      rw [h_enncard, ← ENNReal.ofReal_mul h_d_nonneg]
    rw [h_mul] at h_enreal
    exact_mod_cast h_enreal

  rcases kaufman_projection_fiber
      (F := F) (Λ := Λ) (δ := angularScale) (C := C) (d := d)
      (α := 1) (β := 1) (γ := gamma)
      hangularScale_pos hangularScale_le_one
      (by positivity) (by positivity) hgamma_pos
      hgamma_lt_one hgamma_lt_one hC hd_pos
      hF_frost hΛ_frost hF_sep hΛ_sep hF_ball hunit
      Hk hHk_sub h_dense_real hneF hΛ_nonempty with
    ⟨θ, hθ_in_Λ, h_kaufman_cover⟩

  have h_main : (↑(Metric.externalCoveringNumber (Real.toNNReal angularScale)
          (inner ℝ θ '' (fiber Hk θ : Set Point2))) : ENNReal) ≥
      ENNReal.ofReal (d ^ 2 /
          (2 * kaufman_total_const (max 1 C) 1 1 gamma * (2 : ℝ) ^ gamma)) *
        Kakeya.realRpowENN angularScale (-gamma) := by
    exact_mod_cast h_kaufman_cover

  have h_set_eq : inner ℝ θ '' (fiber Hk θ : Set Point2) =
      inner ℝ θ '' (kaufmanFiber H (b1 θ) (b2 θ) : Set Point2) := by
    rw [h_fiber_eq θ hθ_in_Λ]

  rw [h_set_eq] at h_main

  refine ⟨θ, hθ_in_Λ, ?_⟩
  simpa [graphDensity, d, C, gamma, normalizedEta, angularScale] using h_main

end Kakeya.Assouad
