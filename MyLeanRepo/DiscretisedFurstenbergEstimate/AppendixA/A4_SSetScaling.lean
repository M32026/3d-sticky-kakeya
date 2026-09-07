module

/-
  A4 helper: S-set property under scaling/normalization.

  If P is a (δ, t, C)-set and we scale by 1/Δ,
  then the scaled set is a (δ/Δ, t, C * Δ^t)-set.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

namespace DirecretisedFurstenbergEstimate.AppendixA4

open DirecretisedFurstenbergEstimate

/-- Covering number scaling: Ncover(ε, f '' A) = Ncover(ε*Δ, A)
    where f(p) = (1/Δ) • (p - z). -/
lemma externalCoveringNumber_normalize
    {A : Set EuclideanPlane} {ε Δ : ℝ} (hε_pos : 0 < ε) (hΔ_pos : 0 < Δ) (z : EuclideanPlane) :
    Metric.externalCoveringNumber ε.toNNReal (((1 / Δ : ℝ) • · - (1 / Δ : ℝ) • z) '' A) =
    Metric.externalCoveringNumber (ε * Δ).toNNReal A := by
  let f : EuclideanPlane → EuclideanPlane := fun p => (1 / Δ : ℝ) • (p - z)
  let g : EuclideanPlane → EuclideanPlane := fun q => Δ • q + z
  have hf_eq : f = fun p => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z := by
    funext p
    simp [f, smul_sub]
    <;> abel
  have hfg : ∀ q, f (g q) = q := by
    intro q
    have h : f (g q) = (1 / Δ : ℝ) • ((Δ • q + z) - z) := by rfl
    rw [h]
    have h2 : (Δ • q + z) - z = Δ • q := by simp
    rw [h2]
    have h3 : (1 / Δ : ℝ) • (Δ • q) = ((1 / Δ) * Δ : ℝ) • q := by rw [smul_smul]
    rw [h3]
    have h4 : (1 / Δ) * Δ = (1 : ℝ) := by field_simp [hΔ_pos.ne'] <;> ring
    rw [h4] <;> simp
  have hgf : ∀ p, g (f p) = p := by
    intro p
    have h : g (f p) = Δ • ((1 / Δ : ℝ) • (p - z)) + z := by rfl
    rw [h]
    have h2 : Δ • ((1 / Δ : ℝ) • (p - z)) = ((Δ * (1 / Δ) : ℝ) • (p - z)) := by rw [smul_smul]
    rw [h2]
    have h3 : Δ * (1 / Δ) = (1 : ℝ) := by field_simp [hΔ_pos.ne'] <;> ring
    rw [h3]
    simp <;> abel
  have h_dist_f : ∀ x y, dist (f x) (f y) = dist x y / Δ := by
    intro x y
    have h1 : f x - f y = (1 / Δ : ℝ) • (x - y) := by
      simp only [f]
      have h_smul : (1 / Δ : ℝ) • (x - z) - (1 / Δ : ℝ) • (y - z) =
          (1 / Δ : ℝ) • ((x - z) - (y - z)) := by rw [← smul_sub]
      rw [h_smul]
      have h_sub : (x - z) - (y - z) = x - y := by simp
      rw [h_sub]
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
    have h_abs : ‖(1 / Δ : ℝ)‖ = 1 / Δ := by
      rw [Real.norm_eq_abs, abs_of_pos] <;> positivity
    rw [h_abs] <;> ring
  have h_dist_g : ∀ x y, dist (g x) (g y) = Δ * dist x y := by
    intro x y
    have h1 : g x - g y = Δ • (x - y) := by
      simp only [g]
      have h2 : (Δ • x + z) - (Δ • y + z) = Δ • x - Δ • y := by simp
      rw [h2, ← smul_sub]
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
    have h_abs : ‖(Δ : ℝ)‖ = Δ := by
      rw [Real.norm_eq_abs, abs_of_pos] <;> linarith
    rw [h_abs] <;> ring
  have h_edist_le_f : ∀ (a b : EuclideanPlane), dist a b ≤ ε ↔ edist a b ≤ ↑ε.toNNReal := by
    intro a b
    constructor
    · intro h
      rw [edist_dist]
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h
    · intro h
      rw [edist_dist] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have h_edist_le_g : ∀ (a b : EuclideanPlane), dist a b ≤ ε * Δ ↔ edist a b ≤ ↑(ε * Δ).toNNReal := by
    intro a b
    constructor
    · intro h
      rw [edist_dist]
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h
    · intro h
      rw [edist_dist] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have h1 : Metric.externalCoveringNumber ε.toNNReal (f '' A) ≤
      Metric.externalCoveringNumber (ε * Δ).toNNReal A := by
    have h_main : ∀ (D : Set EuclideanPlane), Metric.IsCover (ε * Δ).toNNReal A D →
        Metric.externalCoveringNumber ε.toNNReal (f '' A) ≤ D.encard := by
      intro D hD
      let D' := f '' D
      have hD' : Metric.IsCover ε.toNNReal (f '' A) D' := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have h2 : ∃ d ∈ D, edist x d ≤ ↑(ε * Δ).toNNReal := hD hx
        rcases h2 with ⟨d, hd, hdist⟩
        have hdist' : dist x d ≤ ε * Δ := (h_edist_le_g x d).mpr hdist
        have h3 : dist (f x) (f d) ≤ ε := by
          rw [h_dist_f]
          have h4 : dist x d / Δ ≤ (ε * Δ) / Δ := by gcongr
          have h5 : (ε * Δ) / Δ = ε := by field_simp [hΔ_pos.ne'] <;> ring
          rw [h5] at h4
          exact h4
        have h4 : edist (f x) (f d) ≤ ↑ε.toNNReal := (h_edist_le_f (f x) (f d)).mp h3
        exact ⟨f d, Set.mem_image_of_mem f hd, h4⟩
      have h5 : Metric.externalCoveringNumber ε.toNNReal (f '' A) ≤ D'.encard :=
        hD'.externalCoveringNumber_le_encard
      have h6 : D'.encard ≤ D.encard := Set.encard_image_le f D
      exact h5.trans h6
    simp only [Metric.externalCoveringNumber]
    apply le_iInf_iff.mpr
    intro D
    by_cases hD : Metric.IsCover (ε * Δ).toNNReal A D
    · have h_lhs : (⨅ (C' : Set EuclideanPlane) (_ : Metric.IsCover ε.toNNReal (f '' A) C'), C'.encard) =
          Metric.externalCoveringNumber ε.toNNReal (f '' A) := by rfl
      rw [h_lhs]
      apply le_iInf_iff.mpr
      intro hD'
      exact h_main D hD
    · simpa [hD] using le_top
  have h2 : Metric.externalCoveringNumber (ε * Δ).toNNReal A ≤
      Metric.externalCoveringNumber ε.toNNReal (f '' A) := by
    have h_main : ∀ (C : Set EuclideanPlane), Metric.IsCover ε.toNNReal (f '' A) C →
        Metric.externalCoveringNumber (ε * Δ).toNNReal A ≤ C.encard := by
      intro C hC
      let C' := g '' C
      have hC' : Metric.IsCover (ε * Δ).toNNReal A C' := by
        intro x hx
        have h2 : ∃ c ∈ C, edist (f x) c ≤ ↑ε.toNNReal := hC (Set.mem_image_of_mem f hx)
        rcases h2 with ⟨c, hc, hdist⟩
        have hdist' : dist (f x) c ≤ ε := (h_edist_le_f (f x) c).mpr hdist
        have h3 : dist x (g c) ≤ ε * Δ := by
          have h4 : dist x (g c) = dist (g (f x)) (g c) := by rw [hgf x]
          rw [h4, h_dist_g]
          have h5 : Δ * dist (f x) c ≤ Δ * ε := by gcongr
          have h6 : Δ * ε = ε * Δ := by ring
          rw [h6] at h5
          exact h5
        have h5 : edist x (g c) ≤ ↑(ε * Δ).toNNReal := (h_edist_le_g x (g c)).mp h3
        exact ⟨g c, Set.mem_image_of_mem g hc, h5⟩
      have h5 : Metric.externalCoveringNumber (ε * Δ).toNNReal A ≤ C'.encard :=
        hC'.externalCoveringNumber_le_encard
      have h6 : C'.encard ≤ C.encard := Set.encard_image_le g C
      exact h5.trans h6
    simp only [Metric.externalCoveringNumber]
    apply le_iInf_iff.mpr
    intro C
    by_cases hC : Metric.IsCover ε.toNNReal (f '' A) C
    · have h_lhs : (⨅ (D' : Set EuclideanPlane) (_ : Metric.IsCover (ε * Δ).toNNReal A D'), D'.encard) =
          Metric.externalCoveringNumber (ε * Δ).toNNReal A := by rfl
      rw [h_lhs]
      apply le_iInf_iff.mpr
      intro hC'
      exact h_main C hC
    · simpa [hC] using le_top
  have h_eq : ((fun p : EuclideanPlane => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z) '' A) = f '' A := by
    rw [hf_eq]
  rw [h_eq]
  exact le_antisymm h1 h2

/-- S-set scaling: if P is a (δ, t, C)-set and f(p) = (1/Δ) • (p - z),
    then f '' P is a (δ/Δ, t, C * Δ^t)-set. -/
lemma sset_normalize
    {P : Set EuclideanPlane} {δ t C : ℝ} (h : IsDeltaSSet δ t C P)
    {Δ : ℝ} (hΔ_pos : 0 < Δ) (z : EuclideanPlane)
    (hδ_pos : 0 < δ) (ht_nonneg : 0 ≤ t) (hC_pos : 0 < C) :
    IsDeltaSSet (δ / Δ) t (C * Δ^t) (((1 / Δ : ℝ) • · - (1 / Δ : ℝ) • z) '' P) := by
  let f : EuclideanPlane → EuclideanPlane := fun p => (1 / Δ : ℝ) • (p - z)
  let g : EuclideanPlane → EuclideanPlane := fun q => Δ • q + z
  have hf_eq : f = fun p => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z := by
    funext p
    simp [f, smul_sub] <;> abel
  have hfg : ∀ q, f (g q) = q := by
    intro q
    have h : f (g q) = (1 / Δ : ℝ) • ((Δ • q + z) - z) := by rfl
    rw [h]
    have h2 : (Δ • q + z) - z = Δ • q := by simp
    rw [h2]
    have h3 : (1 / Δ : ℝ) • (Δ • q) = ((1 / Δ) * Δ : ℝ) • q := by rw [smul_smul]
    rw [h3]
    have h4 : (1 / Δ) * Δ = (1 : ℝ) := by field_simp [hΔ_pos.ne'] <;> ring
    rw [h4] <;> simp
  have hgf : ∀ p, g (f p) = p := by
    intro p
    have h : g (f p) = Δ • ((1 / Δ : ℝ) • (p - z)) + z := by rfl
    rw [h]
    have h2 : Δ • ((1 / Δ : ℝ) • (p - z)) = ((Δ * (1 / Δ) : ℝ) • (p - z)) := by rw [smul_smul]
    rw [h2]
    have h3 : Δ * (1 / Δ) = (1 : ℝ) := by field_simp [hΔ_pos.ne'] <;> ring
    rw [h3]
    simp <;> abel
  have h_dist_f : ∀ x y, dist (f x) (f y) = dist x y / Δ := by
    intro x y
    have h1 : f x - f y = (1 / Δ : ℝ) • (x - y) := by
      simp only [f]
      have h_smul : (1 / Δ : ℝ) • (x - z) - (1 / Δ : ℝ) • (y - z) =
          (1 / Δ : ℝ) • ((x - z) - (y - z)) := by rw [← smul_sub]
      rw [h_smul]
      have h_sub : (x - z) - (y - z) = x - y := by simp
      rw [h_sub]
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
    have h_abs : ‖(1 / Δ : ℝ)‖ = 1 / Δ := by
      rw [Real.norm_eq_abs, abs_of_pos] <;> positivity
    rw [h_abs] <;> ring
  have h_dist_g : ∀ x y, dist (g x) (g y) = Δ * dist x y := by
    intro x y
    have h1 : g x - g y = Δ • (x - y) := by
      simp only [g]
      have h2 : (Δ • x + z) - (Δ • y + z) = Δ • x - Δ • y := by simp
      rw [h2, ← smul_sub]
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
    have h_abs : ‖(Δ : ℝ)‖ = Δ := by
      rw [Real.norm_eq_abs, abs_of_pos] <;> linarith
    rw [h_abs] <;> ring
  have h_nonempty : (f '' P).Nonempty := h.1.image f
  have h_scale_pos : 0 < δ / Δ := by positivity
  have hC2_pos : 0 < C * Δ ^ t := by positivity
  have h_main_goal : IsDeltaSSet (δ / Δ) t (C * Δ^t) (f '' P) := by
    refine' ⟨h_nonempty, h_scale_pos, hC2_pos, ht_nonneg, _⟩
    intro x' r' hr'
    let x := g x'
    let r := Δ * r'
    have hr : δ ≤ r := by
      have h1 : δ / Δ ≤ r' := hr'
      have h2 : δ ≤ Δ * r' := by
        calc δ
          = Δ * (δ / Δ) := by field_simp [hΔ_pos.ne'] <;> ring
        _ ≤ Δ * r' := by gcongr
      exact h2
    have h_image_inter : f '' (P ∩ Metric.closedBall x r) = (f '' P) ∩ Metric.closedBall x' r' := by
      ext y
      simp only [Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨p, ⟨hp, hball⟩, rfl⟩
        have hball' : dist (f p) x' ≤ r' := by
          have h : dist p x ≤ r := hball
          have h2 : dist (f p) (f x) = dist p x / Δ := h_dist_f p x
          have h3 : f x = x' := by
            have h4 : x = g x' := by rfl
            rw [h4]
            exact hfg x'
          rw [h3] at h2
          rw [h2]
          have h5 : dist p x / Δ ≤ r / Δ := by gcongr
          have h6 : r / Δ = r' := by
            simp [r]
            <;> field_simp [hΔ_pos.ne'] <;> ring
          rw [h6] at h5
          exact h5
        exact ⟨Set.mem_image_of_mem f hp, hball'⟩
      · rintro ⟨⟨p, hp, rfl⟩, hball'⟩
        have hball : dist p x ≤ r := by
          have h2 : dist (f p) x' ≤ r' := hball'
          have h3 : dist p x = Δ * dist (f p) x' := by
            have h4 : dist p x = dist (g (f p)) (g x') := by rw [hgf p]
            rw [h4, h_dist_g]
          rw [h3]
          exact mul_le_mul_of_nonneg_left hball' (by linarith)
        exact ⟨p, ⟨hp, hball⟩, rfl⟩
    have h4 := h.2.2.2.2 x r hr
    have h_scale2 : (δ / Δ) * Δ = δ := by
      field_simp [hΔ_pos.ne'] <;> ring
    have h6 : (Metric.externalCoveringNumber (δ / Δ).toNNReal ((f '' P) ∩ Metric.closedBall x' r') : ENNReal) =
        (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
      have h_eq1 : (f '' P) ∩ Metric.closedBall x' r' = f '' (P ∩ Metric.closedBall x r) :=
        h_image_inter.symm
      rw [h_eq1]
      have h_norm := externalCoveringNumber_normalize (A := P ∩ Metric.closedBall x r) (hε_pos := h_scale_pos) hΔ_pos z
      have h_norm2 : Metric.externalCoveringNumber (δ / Δ).toNNReal (f '' (P ∩ Metric.closedBall x r)) =
          Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) := by
        have h_f_eq : f '' (P ∩ Metric.closedBall x r) =
            ((fun a : EuclideanPlane => (1 / Δ : ℝ) • a - (1 / Δ : ℝ) • z) '' (P ∩ Metric.closedBall x r)) := by
          rw [hf_eq]
        rw [h_f_eq]
        rw [h_norm]
        have h_scale3 : (δ / Δ) * Δ = δ := by field_simp [hΔ_pos.ne'] <;> ring
        rw [h_scale3]
      simpa using congr_arg (fun x : ℕ∞ => (x : ENNReal)) h_norm2
    have h7 : (Metric.externalCoveringNumber (δ / Δ).toNNReal (f '' P) : ENNReal) =
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      have h_norm := externalCoveringNumber_normalize (A := P) (hε_pos := h_scale_pos) hΔ_pos z
      have h_norm2 : Metric.externalCoveringNumber (δ / Δ).toNNReal (f '' P) =
          Metric.externalCoveringNumber δ.toNNReal P := by
        have h_f_eq : f '' P =
            ((fun a : EuclideanPlane => (1 / Δ : ℝ) • a - (1 / Δ : ℝ) • z) '' P) := by rw [hf_eq]
        rw [h_f_eq]
        rw [h_norm]
        have h_scale3 : (δ / Δ) * Δ = δ := by field_simp [hΔ_pos.ne'] <;> ring
        rw [h_scale3]
      simpa using congr_arg (fun x : ℕ∞ => (x : ENNReal)) h_norm2
    have h9 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        ENNReal.ofReal (C * Δ ^ t) * (ENNReal.ofReal r') ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      have h10 : r = Δ * r' := by rfl
      rw [h10]
      have h11 : ENNReal.ofReal (Δ * r') = ENNReal.ofReal Δ * ENNReal.ofReal r' := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h11]
      have h12 : (ENNReal.ofReal Δ * ENNReal.ofReal r') ^ t =
          (ENNReal.ofReal Δ) ^ t * (ENNReal.ofReal r') ^ t := by
        rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
      rw [h12]
      have h13 : ENNReal.ofReal C * ((ENNReal.ofReal Δ) ^ t * (ENNReal.ofReal r') ^ t) =
          ENNReal.ofReal (C * Δ ^ t) * (ENNReal.ofReal r') ^ t := by
        have h14 : ENNReal.ofReal C * (ENNReal.ofReal Δ) ^ t = ENNReal.ofReal (C * Δ ^ t) := by
          have h15 : (ENNReal.ofReal Δ) ^ t = ENNReal.ofReal (Δ ^ t) :=
            ENNReal.ofReal_rpow_of_pos hΔ_pos
          rw [h15, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
        rw [← mul_assoc, h14]
      rw [h13] <;> exact le_refl _
    calc (Metric.externalCoveringNumber (δ / Δ).toNNReal ((f '' P) ∩ Metric.closedBall x' r') : ENNReal)
      = (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := h6
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h4
    _ ≤ ENNReal.ofReal (C * Δ ^ t) * (ENNReal.ofReal r') ^ t *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h9
    _ = ENNReal.ofReal (C * Δ ^ t) * (ENNReal.ofReal r') ^ t *
          (Metric.externalCoveringNumber (δ / Δ).toNNReal (f '' P) : ENNReal) := by rw [h7]
  have h_final : ((fun p : EuclideanPlane => (1 / Δ : ℝ) • p - (1 / Δ : ℝ) • z) '' P) = f '' P := by
    rw [hf_eq]
  rw [h_final]
  exact h_main_goal

end DirecretisedFurstenbergEstimate.AppendixA4
