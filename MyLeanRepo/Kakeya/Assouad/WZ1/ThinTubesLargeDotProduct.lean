import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma40AngularSum
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma40AngularSumUnnormalized

/-!
# WZ1 Lemma 40: Clean main proof (direct energy averaging)
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Metric

attribute [local instance] Classical.propDecidable

/-- Total energy constant: 1 + C_ang_unnorm * (2 + 2*K_frost0). -/
noncomputable def totalEnergyConst (γ : ℝ) : ℝ :=
  1 + (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * (2 + 2 * kaufman_K_frost0 1 γ)

/-- Angular sum bound from thin tubes, proved via dyadic decomposition. -/
lemma thin_tubes_angular_sum
    {G₁ G₂ : DiscreteSet 2} {δ K γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hK : 1 ≤ K)
    (hγ : 0 < γ) (hγ_lt_one : γ < 1)
    (b₁ : Point2) (v : Point2) (hv : ‖v‖ = 1)
    (E : Finset (Point2 × Point2)) (hE_sub : E ⊆ G₁ ×ˢ G₂)
    (h_thin : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r →
        ((G₂.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal) ≤
        ENNReal.ofReal (K * r) * (G₂.card : ENNReal))
    (hG1_ball : G₁.IsInUnitBall) (hG2_ball : G₂.IsInUnitBall)
    (h_mutual_sep : ∀ b₁ ∈ G₁, ∀ b₂ ∈ G₂, 1 / 2 ≤ dist b₁ b₂)
    (hb₁ : b₁ ∈ G₁) :
    ∑ b₂ ∈ (G₂.filter (fun b₂ => (b₁, b₂) ∈ E)),
      (max (|inner ℝ ((‖b₂ - b₁‖⁻¹) • (b₂ - b₁)) v|) δ)^(-γ) ≤
      angularSumConst γ * K * (G₂.card : ℝ) := by
  let D : Finset Point2 := G₂.filter (fun b₂ => (b₁, b₂) ∈ E)
  have hD_sub : D ⊆ G₂ := by
    intro b₂ hb₂; exact (Finset.mem_filter.mp hb₂).1
  have h_sep : ∀ b₂ ∈ D, 1 / 2 ≤ dist b₁ b₂ := by
    intro b₂ hb₂
    have hb₂_in_G₂ : b₂ ∈ G₂ := hD_sub hb₂
    exact h_mutual_sep b₁ hb₁ b₂ hb₂_in_G₂
  have h_bound : ∀ b₂ ∈ D, dist b₁ b₂ ≤ 2 := by
    intro b₂ hb₂
    have h1 : dist b₁ (0 : Point2) ≤ 1 := hG1_ball b₁ hb₁
    have h2 : dist b₂ (0 : Point2) ≤ 1 := hG2_ball b₂ (hD_sub hb₂)
    have h3 : dist b₁ b₂ ≤ dist b₁ (0 : Point2) + dist (0 : Point2) b₂ := dist_triangle _ _ _
    have h4 : dist (0 : Point2) b₂ = dist b₂ (0 : Point2) := dist_comm _ _
    linarith
  let ℓ : AffineSubspace ℝ Point2 := AffineSubspace.mk' b₁ (ℝ ∙ wz1Perp2 v)
  have h_b1_in_ℓ : b₁ ∈ (ℓ : Set Point2) := by simp [ℓ]
  have h_dir : ℓ.direction = ℝ ∙ wz1Perp2 v := by
    exact AffineSubspace.direction_mk' b₁ (ℝ ∙ wz1Perp2 v)
  have h_perp_ne_zero : wz1Perp2 v ≠ 0 := by
    intro h
    have h1 : (wz1Perp2 v) 0 = 0 := by rw [h] <;> simp
    have h2 : (wz1Perp2 v) 1 = 0 := by rw [h] <;> simp
    have h3 : v 1 = 0 := by simpa [wz1Perp2] using h1
    have h4 : v 0 = 0 := by simpa [wz1Perp2] using h2
    have h5 : v = 0 := by
      apply PiLp.ext
      intro i
      fin_cases i <;> tauto
    rw [h5] at hv
    <;> norm_num at hv
  have h_finrank : Module.finrank ℝ ℓ.direction = 1 := by
    rw [h_dir]
    exact finrank_span_singleton h_perp_ne_zero
  have h_thin' : ∀ (r : ℝ), δ ≤ r →
      ((D.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card : ℝ) ≤
      K * r * (G₂.card : ℝ) := by
    intro r hr
    have h_eq : D.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2)) =
        G₂.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E) := by
      ext b₂
      simp only [D, Finset.mem_filter]
      <;> tauto
    have h_enn : ((D.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card : ENNReal) ≤
        ENNReal.ofReal (K * r) * (G₂.card : ENNReal) := by
      rw [h_eq]
      exact h_thin b₁ hb₁ ℓ h_b1_in_ℓ h_finrank r hr
    have h_fin : (ENNReal.ofReal (K * r) * (G₂.card : ENNReal)) ≠ ⊤ := by
      simp [ENNReal.mul_ne_top]
    have h_toReal1 : ((D.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2))).card : ℝ) ≤
        (ENNReal.ofReal (K * r) * (G₂.card : ENNReal)).toReal :=
      ENNReal.toReal_mono h_fin h_enn
    have h_r_pos : 0 < r := by linarith
    have h_K_pos : 0 < K := by linarith
    have hKr_pos : 0 ≤ K * r := mul_nonneg h_K_pos.le h_r_pos.le
    have h_toReal2 : (ENNReal.ofReal (K * r) * (G₂.card : ENNReal)).toReal =
        K * r * (G₂.card : ℝ) := by
      have h1 : (ENNReal.ofReal (K * r) * (G₂.card : ENNReal)).toReal =
          (ENNReal.ofReal (K * r)).toReal * (G₂.card : ℝ) := by
        rw [ENNReal.toReal_mul] <;> simp
      rw [h1]
      have h2 : (ENNReal.ofReal (K * r)).toReal = K * r := by
        rw [ENNReal.toReal_ofReal hKr_pos]
      rw [h2] <;> ring
    rw [h_toReal2] at h_toReal1
    exact h_toReal1
  exact angular_sum_from_thin_tubes hδ hδ_le_one hK hγ hγ_lt_one b₁ v hv D hD_sub h_sep h_bound h_thin'

/-- Extract vertex containment from uniform triple density. -/
lemma density_vertex_containment
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)} {c : ENNReal}
    (h_dense : WZ1UniformTripleDensity c F G₁ G₂ H) :
    ∀ (t : Point2 × Point2 × Point2), t ∈ H → t.1 ∈ F ∧ t.2.1 ∈ G₁ ∧ t.2.2 ∈ G₂ := by
  have h1 := h_dense.2.1
  intro t ht
  let e : Fin 3 → Point2 := wz1TripleCoordinate t
  have he : e ∈ wz1EncodeTriples H := Finset.mem_image_of_mem _ ht
  have h2 : ∀ (i : Fin 3), e i ∈ wz1TripleVertexClasses F G₁ G₂ i := h1 e he
  exact ⟨h2 0, h2 1, h2 2⟩

/-- Extract fiber size bound from uniform triple density. -/
lemma density_fiber_bound
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)} {c : ℝ} (hc : 0 ≤ c)
    (h_dense : WZ1UniformTripleDensity (ENNReal.ofReal (2 * c)) F G₁ G₂ H)
    {b₁ b₂ : Point2} (h_in_piH : (b₁, b₂) ∈ H.image (fun h => (h.2.1, h.2.2))) :
    ((H.filter (fun h => h.2.1 = b₁ ∧ h.2.2 = b₂)).image (fun h => h.1)).card ≥ (2 * c) * (F.card : ℝ) := by
  let A := wz1TripleVertexClasses F G₁ G₂
  let H_enc := wz1EncodeTriples H
  have h1 : WZ1UniformHypergraphDensity (ENNReal.ofReal (2 * c)) A H_enc := h_dense.2
  rcases Finset.mem_image.mp h_in_piH with ⟨h0, hh0, h_eq⟩
  have hb1 : h0.2.1 = b₁ := by simp [Prod.ext_iff] at h_eq <;> tauto
  have hb2 : h0.2.2 = b₂ := by simp [Prod.ext_iff] at h_eq <;> tauto
  let edge : Fin 3 → Point2 := wz1TripleCoordinate h0
  have hedge_in : edge ∈ H_enc := Finset.mem_image_of_mem _ hh0
  let I : Finset (Fin 3) := {1, 2}
  have h2 := h1.2 edge hedge_in I
  have h3 : Finset.univ \ I = ({0} : Finset (Fin 3)) := by decide
  rw [h3] at h2
  have h4 : wz1VertexCardProduct A ({0} : Finset (Fin 3)) = (F.card : ENNReal) := by
    simp [wz1VertexCardProduct, A, wz1TripleVertexClasses] <;> rfl
  rw [h4] at h2
  let fiber_H := H.filter (fun h => h.2.1 = b₁ ∧ h.2.2 = b₂)
  let fiber_img := fiber_H.image (fun h => h.1)
  have h_inj1 : Function.Injective wz1TripleCoordinate := by
    intro a b h
    have h0 : a.1 = b.1 := by simpa [wz1TripleCoordinate] using congr_fun h 0
    have h1 : a.2.1 = b.2.1 := by simpa [wz1TripleCoordinate] using congr_fun h 1
    have h2 : a.2.2 = b.2.2 := by simpa [wz1TripleCoordinate] using congr_fun h 2
    exact Prod.ext h0 (Prod.ext h1 h2)
  have h_fiber_set_eq : wz1HypergraphFiber H_enc I edge = fiber_H.image wz1TripleCoordinate := by
    ext e
    simp only [wz1HypergraphFiber, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨h_in1, h_ag⟩
      rcases Finset.mem_image.mp h_in1 with ⟨h, hh, rfl⟩
      have h1 : h.2.1 = b₁ := by
        have h_eq1 : (wz1TripleCoordinate h) 1 = edge 1 := h_ag 1 (by simp [I])
        have h_edge1 : edge 1 = b₁ := by simp [edge, wz1TripleCoordinate, hb1]
        exact h_eq1.trans h_edge1
      have h2 : h.2.2 = b₂ := by
        have h_eq2 : (wz1TripleCoordinate h) 2 = edge 2 := h_ag 2 (by simp [I])
        have h_edge2 : edge 2 = b₂ := by simp [edge, wz1TripleCoordinate, hb2]
        exact h_eq2.trans h_edge2
      have h_in_fiber : h ∈ fiber_H := by
        dsimp only [fiber_H]
        exact Finset.mem_filter.mpr ⟨hh, h1, h2⟩
      exact ⟨h, h_in_fiber, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      have h_in_H : h ∈ H := (Finset.mem_filter.mp hh).1
      have h1 : h.2.1 = b₁ := (Finset.mem_filter.mp hh).2.1
      have h2 : h.2.2 = b₂ := (Finset.mem_filter.mp hh).2.2
      have h_in_enc : wz1TripleCoordinate h ∈ H_enc := Finset.mem_image_of_mem _ h_in_H
      have h_ag : ∀ i ∈ I, (wz1TripleCoordinate h) i = edge i := by
        intro i hi
        have h_i1 : i = 1 ∨ i = 2 := by simp [I] at hi <;> tauto
        rcases h_i1 with (rfl | rfl)
        · dsimp only [edge, wz1TripleCoordinate]; rw [h1, hb1]
        · dsimp only [edge, wz1TripleCoordinate]; rw [h2, hb2]
      exact ⟨h_in_enc, h_ag⟩
  rw [h_fiber_set_eq] at h2
  have h_card1 : (fiber_H.image wz1TripleCoordinate).card = fiber_H.card :=
    Finset.card_image_of_injective _ h_inj1
  rw [h_card1] at h2
  have h_inj2 : Set.InjOn (fun h : Point2 × Point2 × Point2 => h.1) (fiber_H : Set _) := by
    intro h1 hh1 h2 hh2 h_eq
    have h11 : h1.2.1 = b₁ := (Finset.mem_filter.mp hh1).2.1
    have h12 : h1.2.2 = b₂ := (Finset.mem_filter.mp hh1).2.2
    have h21 : h2.2.1 = b₁ := (Finset.mem_filter.mp hh2).2.1
    have h22 : h2.2.2 = b₂ := (Finset.mem_filter.mp hh2).2.2
    have h23 : h1.2.1 = h2.2.1 := by rw [h11, h21]
    have h24 : h1.2.2 = h2.2.2 := by rw [h12, h22]
    exact Prod.ext h_eq (Prod.ext h23 h24)
  have h_card2 : fiber_img.card = fiber_H.card := by
    dsimp only [fiber_img]
    rw [Finset.card_image_of_injOn h_inj2]
  have h_final : (ENNReal.ofReal (2 * c) * (F.card : ENNReal)) ≤ (fiber_H.card : ENNReal) := h2
  have h_final2 : (ENNReal.ofReal (2 * c) * (F.card : ENNReal)) ≤ (fiber_img.card : ENNReal) := by
    rw [h_card2]
    exact h_final
  have h_out : (fiber_img.card : ℝ) ≥ (2 * c) * (F.card : ℝ) := by
    have h_conv : (ENNReal.ofReal (2 * c) * (F.card : ENNReal)) ≤ (fiber_img.card : ENNReal) := h_final2
    have h9 : ((fiber_img.card : ENNReal)).toReal ≥ (ENNReal.ofReal (2 * c) * (F.card : ENNReal)).toReal := ENNReal.toReal_mono (by simp) h_conv
    have h10 : ((fiber_img.card : ENNReal)).toReal = (fiber_img.card : ℝ) := by simp
    have h11 : (ENNReal.ofReal (2 * c) * (F.card : ENNReal)).toReal = (2 * c) * (F.card : ℝ) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] <;> simp <;> ring
    rw [h10, h11] at h9
    exact h9
  exact h_out

/-- Extract projection size from uniform triple density. -/
lemma density_projection_bound
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)} {c : ℝ} (hc : 0 ≤ c)
    (h_dense : WZ1UniformTripleDensity (ENNReal.ofReal (2 * c)) F G₁ G₂ H) :
    ((H.image (fun h => (h.2.1, h.2.2))).card : ENNReal) ≥
    ENNReal.ofReal (2 * c) * (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
  let A := wz1TripleVertexClasses F G₁ G₂
  let H_enc := wz1EncodeTriples H
  have h1 : WZ1UniformHypergraphDensity (ENNReal.ofReal (2 * c)) A H_enc := h_dense.2
  have hne : H.Nonempty := h_dense.1
  rcases hne with ⟨h0, hh0⟩
  let edge : Fin 3 → Point2 := wz1TripleCoordinate h0
  have hedge_in : edge ∈ H_enc := Finset.mem_image_of_mem _ hh0
  let I : Finset (Fin 3) := ∅
  have h2 := h1.2 edge hedge_in I
  have h3 : wz1VertexCardProduct A (Finset.univ \ I) =
      (F.card : ENNReal) * (G₁.card : ENNReal) * (G₂.card : ENNReal) := by
    have h_univ : Finset.univ \ I = (Finset.univ : Finset (Fin 3)) := by
      ext x; simp [I]
    rw [h_univ]
    have h : wz1VertexCardProduct A (Finset.univ : Finset (Fin 3)) =
        (A 0).card * (A 1).card * (A 2).card := by
      simp [wz1VertexCardProduct, Fin.prod_univ_succ] <;> ring
    rw [h]
    have hA0 : (A 0).card = (F.card : ENNReal) := by simp [A, wz1TripleVertexClasses] <;> rfl
    have hA1 : (A 1).card = (G₁.card : ENNReal) := by simp [A, wz1TripleVertexClasses] <;> rfl
    have hA2 : (A 2).card = (G₂.card : ENNReal) := by simp [A, wz1TripleVertexClasses] <;> rfl
    rw [hA0, hA1, hA2] <;> ring
  rw [h3] at h2
  have h5 : wz1HypergraphFiber H_enc I edge = H_enc := by
    ext x
    simp [wz1HypergraphFiber, I]
  rw [h5] at h2
  have h_inj : Function.Injective wz1TripleCoordinate := by
    intro a b h
    have h0 : a.1 = b.1 := by simpa [wz1TripleCoordinate] using congr_fun h 0
    have h1 : a.2.1 = b.2.1 := by simpa [wz1TripleCoordinate] using congr_fun h 1
    have h2 : a.2.2 = b.2.2 := by simpa [wz1TripleCoordinate] using congr_fun h 2
    exact Prod.ext h0 (Prod.ext h1 h2)
  have hH_enc_card : (H_enc.card : ENNReal) = (H.card : ENNReal) := by
    have h : H_enc.card = H.card := by
      dsimp only [H_enc, wz1EncodeTriples]
      rw [Finset.card_image_of_injective _ h_inj]
    exact_mod_cast h
  rw [hH_enc_card] at h2
  let piH := H.image (fun h : Point2 × Point2 × Point2 => (h.2.1, h.2.2))
  let f : (Point2 × Point2 × Point2) → (Point2 × Point2) := fun h => (h.2.1, h.2.2)
  have h_maps : Set.MapsTo f (H : Set _) (piH : Set _) := by
    intro x hx
    exact Finset.mem_image_of_mem f hx
  have h_sum : (H.card : ENNReal) = ∑ p ∈ piH, ((H.filter (fun h => f h = p)).card : ENNReal) := by
    have h : H.card = ∑ p ∈ piH, (H.filter (fun h => f h = p)).card :=
      Finset.card_eq_sum_card_fiberwise h_maps
    exact_mod_cast h
  have h7 : ∀ p ∈ piH, ((H.filter (fun h => f h = p)).card : ENNReal) ≤ (F.card : ENNReal) := by
    intro p _
    let fiber_H := H.filter (fun h => f h = p)
    let fiber_img := fiber_H.image (fun h => h.1)
    have h8 : fiber_img ⊆ F := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨h, hh, rfl⟩
      have h9 : h ∈ H := (Finset.mem_filter.mp hh).1
      have h10 : h.1 ∈ F := (h_dense.2.1 (wz1TripleCoordinate h) (Finset.mem_image_of_mem _ h9)) 0
      simpa [wz1TripleCoordinate] using h10
    have h_inj_fiber : Set.InjOn (fun h : Point2 × Point2 × Point2 => h.1) (fiber_H : Set _) := by
      intro h1 hh1 h2 hh2 h_eq
      have h11 : f h1 = p := (Finset.mem_filter.mp hh1).2
      have h22 : f h2 = p := (Finset.mem_filter.mp hh2).2
      have h_eq2 : f h1 = f h2 := h11.trans h22.symm
      have h_eq3 : (h1.2.1, h1.2.2) = (h2.2.1, h2.2.2) := by
        simpa [f] using h_eq2
      have h12 : h1.2.1 = h2.2.1 := by
        exact (Prod.ext_iff.mp h_eq3).1
      have h13 : h1.2.2 = h2.2.2 := by
        exact (Prod.ext_iff.mp h_eq3).2
      exact Prod.ext h_eq (Prod.ext h12 h13)
    have h12 : fiber_img.card = fiber_H.card :=
      Finset.card_image_of_injOn h_inj_fiber
    have h11 : (fiber_img.card : ENNReal) ≤ (F.card : ENNReal) := by
      have h111 : fiber_img.card ≤ F.card := Finset.card_le_card h8
      exact_mod_cast h111
    rw [h12] at *
    <;> exact h11
  have h_sum_le : (∑ p ∈ piH, ((H.filter (fun h => f h = p)).card : ENNReal)) ≤
      ∑ p ∈ piH, (F.card : ENNReal) := Finset.sum_le_sum h7
  have h_sum_const : (∑ p ∈ piH, (F.card : ENNReal)) = (piH.card : ENNReal) * (F.card : ENNReal) := by
    simp [Finset.sum_const] <;> ring
  have h6 : (H.card : ENNReal) ≤ (piH.card : ENNReal) * (F.card : ENNReal) := by
    have h_step1 : (H.card : ENNReal) ≤ ∑ p ∈ piH, (F.card : ENNReal) := by
      rw [h_sum]
      exact h_sum_le
    have h_step2 : (H.card : ENNReal) ≤ (piH.card : ENNReal) * (F.card : ENNReal) := by
      rw [h_sum_const] at h_step1
      exact h_step1
    exact h_step2
  have hneF : F.Nonempty := by
    have h9 : h0.1 ∈ F := (h_dense.2.1 edge hedge_in) 0
    exact ⟨h0.1, h9⟩
  have hF_pos : (F.card : ENNReal) ≠ 0 := by
    exact_mod_cast hneF.card_pos.ne'
  have h91 : ENNReal.ofReal (2 * c) * ((F.card : ENNReal) * (G₁.card : ENNReal) * (G₂.card : ENNReal)) ≤
      (piH.card : ENNReal) * (F.card : ENNReal) :=
    le_trans h2 h6
  set a : ENNReal := (F.card : ENNReal) with ha_def
  have ha_ne_zero : a ≠ 0 := hF_pos
  have ha_ne_top : a ≠ ⊤ := by simp [a, ENNReal.natCast_ne_top]
  set b : ENNReal := ENNReal.ofReal (2 * c) * ((G₁.card : ENNReal) * (G₂.card : ENNReal)) with hb_def
  set c' : ENNReal := (piH.card : ENNReal) with hc_def
  have h_main : a * b ≤ a * c' := by
    simpa [a, b, c', mul_assoc, mul_comm, mul_left_comm] using h91
  have h_cancel : b ≤ c' := by
    have h1 : a⁻¹ * (a * b) ≤ a⁻¹ * (a * c') := mul_le_mul_right h_main a⁻¹
    have h2 : a⁻¹ * (a * b) = b := by
      have h21 : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha_ne_zero ha_ne_top
      rw [←mul_assoc, h21, one_mul]
    have h3 : a⁻¹ * (a * c') = c' := by
      have h31 : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha_ne_zero ha_ne_top
      rw [←mul_assoc, h31, one_mul]
    rw [h2, h3] at h1
    exact h1
  have h4 : b ≤ c' := h_cancel
  simpa [b, c', mul_assoc] using h4

/-- Frostman α=1 gives lower bound |F| ≥ 1/(K·δ). -/
lemma frostman_card_lower_bound
    {F : DiscreteSet 2} {δ K : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ 1) (hK : 1 ≤ K)
    (hneF : F.Nonempty)
    (hF_frost : F.IsFrostman δ 1 (ENNReal.ofReal K)) :
    (F.card : ℝ) ≥ 1 / (K * δ) := by
  rcases hneF with ⟨x, hx⟩
  let S := F.filter (fun y => dist y x ≤ δ)
  have h21 : dist x x ≤ δ := by
    have h : dist x x = 0 := dist_self x
    rw [h]
    <;> linarith
  have h2 : x ∈ S := Finset.mem_filter.mpr ⟨hx, h21⟩
  have h3 : 0 < S.card := Finset.card_pos.mpr ⟨x, h2⟩
  have h1 : (S.card : ENNReal) ≥ 1 := by exact_mod_cast h3
  have h41 : F.ballCount x δ = (S.card : ENNReal) := by rfl
  have h_frost' : F.ballCount x δ ≤
      ENNReal.ofReal K * Kakeya.realRpowENN δ 1 * F.enncard :=
    hF_frost x δ (le_refl δ) hδ0
  rw [h41] at h_frost'
  have h_rpow : Kakeya.realRpowENN δ 1 = ENNReal.ofReal δ := by
    simp [Kakeya.realRpowENN] <;> norm_num
  rw [h_rpow] at h_frost'
  have h_enncard : F.enncard = (F.card : ENNReal) := by
    exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp rfl
  rw [h_enncard] at h_frost'
  have h4 : (S.card : ENNReal) ≤ ENNReal.ofReal K * ENNReal.ofReal δ * (F.card : ENNReal) := h_frost'
  have h_fin : (ENNReal.ofReal K * ENNReal.ofReal δ * (F.card : ENNReal)) ≠ ⊤ := by
    simp [ENNReal.mul_ne_top]
  have h_toReal : ((S.card : ENNReal)).toReal ≤
      (ENNReal.ofReal K * ENNReal.ofReal δ * (F.card : ENNReal)).toReal :=
    ENNReal.toReal_mono h_fin h4
  have h6 : (ENNReal.ofReal K * ENNReal.ofReal δ * (F.card : ENNReal)).toReal =
      K * δ * (F.card : ℝ) := by
    have h_a : (ENNReal.ofReal K * ENNReal.ofReal δ).toReal = K * δ := by
      rw [ENNReal.toReal_mul]
      rw [ENNReal.toReal_ofReal (show 0 ≤ K from by linarith)]
      rw [ENNReal.toReal_ofReal (show 0 ≤ δ from by linarith)]
      <;> ring
    have h_b : ((ENNReal.ofReal K * ENNReal.ofReal δ) * (F.card : ENNReal)).toReal =
        (ENNReal.ofReal K * ENNReal.ofReal δ).toReal * (F.card : ℝ) := by
      rw [ENNReal.toReal_mul]
      have hcard : (F.card : ENNReal).toReal = (F.card : ℝ) := by simp
      rw [hcard] <;> ring
    have h_assoc : (ENNReal.ofReal K * ENNReal.ofReal δ * (F.card : ENNReal)) =
        (ENNReal.ofReal K * ENNReal.ofReal δ) * (F.card : ENNReal) := by ring
    rw [h_assoc, h_b, h_a] <;> ring
  have h7 : ((S.card : ENNReal)).toReal = (S.card : ℝ) := by simp
  have h_toReal' : (S.card : ℝ) ≤ K * δ * (F.card : ℝ) := by
    rw [h7, h6] at h_toReal
    exact h_toReal
  have h8 : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h3
  have h9 : (1 : ℝ) ≤ K * δ * (F.card : ℝ) := by linarith
  have h10 : 0 < K * δ := by positivity
  have h11 : (F.card : ℝ) ≥ 1 / (K * δ) := by
    calc (F.card : ℝ)
      = (K * δ * (F.card : ℝ)) / (K * δ) := by field_simp [h10.ne'] <;> ring
    _ ≥ 1 / (K * δ) := by gcongr
  exact h11

/-- Standalone algebra for the final energy-to-covering constant simplification. -/
lemma wz1_h8_algebra (c C K Fcard δ γ : ℝ)
    (hcpos : 0 < c) (hCpos : 0 < C) (hKpos : 0 < K) (hFpos : 0 < Fcard)
    (hδpos : 0 < δ) (hγpos : 0 < γ) (hγltone : γ < 1) :
    ((2 * c * Fcard)^2) / ((2 * C * K^2 * Fcard^2 / c) * (2 * δ)^γ) =
    (2^(1-γ) * c^3 / (C * K^2)) * δ^(-γ) := by
  have h2pow : (2 * δ)^γ = (2 : ℝ)^γ * δ^γ := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
  have h2pow' : (2 : ℝ) * (2 : ℝ)^γ = (2 : ℝ)^(1+γ) := by
    have h_eq1 : (1 + γ : ℝ) = (1 : ℝ) + γ := by ring
    have h2 : (2 : ℝ)^((1 : ℝ) + γ) = (2 : ℝ)^(1 : ℝ) * (2 : ℝ)^γ :=
      Real.rpow_add (by norm_num) (1 : ℝ) γ
    have h3 : (2 : ℝ)^(1 : ℝ) = (2 : ℝ) := by simp
    calc
      (2 : ℝ) * (2 : ℝ)^γ
        = (2 : ℝ)^(1 : ℝ) * (2 : ℝ)^γ := by rw [h3]
    _ = (2 : ℝ)^((1 : ℝ) + γ) := h2.symm
    _ = (2 : ℝ)^(1+γ) := by rw [h_eq1]
  have h4div : (4 : ℝ) / (2 : ℝ)^(1+γ) = (2 : ℝ)^(1-γ) := by
    have h14 : (4 : ℝ) = (2 : ℝ)^(2 : ℝ) := by norm_num
    rw [h14]
    have h15 : (2 : ℝ)^(2 : ℝ) / (2 : ℝ)^(1+γ) = (2 : ℝ)^((2 : ℝ) - (1+γ)) := by
      rw [←Real.rpow_sub (by norm_num)] <;> ring
    rw [h15]
    have h16 : (2 : ℝ) - (1+γ) = 1-γ := by ring
    rw [h16]
  have hδneg : δ^(-γ) = (δ^γ)⁻¹ := by
    rw [Real.rpow_neg (by linarith)] <;> ring
  set D := (2 : ℝ)^(1+γ) * C * K^2 * Fcard^2 * δ^γ with hD
  have hD_ne : D ≠ 0 := by positivity
  have hc_ne : c ≠ 0 := hcpos.ne'
  have hF2_ne : Fcard^2 ≠ 0 := by positivity
  have h_denom : (2 * C * K^2 * Fcard^2 / c) * (2 * δ)^γ = D / c := by
    rw [h2pow]
    have h1 : (2 * C * K^2 * Fcard^2 / c) * ((2 : ℝ)^γ * δ^γ) =
        ((2 * C * K^2 * Fcard^2) * ((2 : ℝ)^γ * δ^γ)) / c := by
      field_simp [hc_ne] <;> ring
    rw [h1]
    have h2 : (2 * C * K^2 * Fcard^2) * ((2 : ℝ)^γ * δ^γ) =
        ((2 : ℝ) * (2 : ℝ)^γ) * (C * K^2 * Fcard^2 * δ^γ) := by ring
    rw [h2, h2pow']
    have h3 : (2 : ℝ)^(1+γ) * (C * K^2 * Fcard^2 * δ^γ) = D := by
      simp only [hD] <;> ring
    rw [h3]
  have h_main : (4 * c^2 * Fcard^2) / (D / c) = (4 * c^3 * Fcard^2) / D := by
    field_simp [hc_ne, hD_ne] <;> ring
  have h_cancel : (4 * c^3 * Fcard^2) / D = (4 * c^3) / ((2 : ℝ)^(1+γ) * C * K^2 * δ^γ) := by
    have hD' : D = ((2 : ℝ)^(1+γ) * C * K^2 * δ^γ) * Fcard^2 := by
      simp only [hD] <;> ring
    rw [hD']
    field_simp [hF2_ne] <;> ring
  have h_final : (4 * c^3) / ((2 : ℝ)^(1+γ) * C * K^2 * δ^γ) =
      (4 / (2 : ℝ)^(1+γ)) * (c^3 / (C * K^2)) * (δ^γ)⁻¹ := by
    have h21γ_ne : (2 : ℝ)^(1+γ) ≠ 0 := by positivity
    have hCK_ne : C * K^2 ≠ 0 := by positivity
    have hδγ_ne : δ^γ ≠ 0 := by positivity
    field_simp [h21γ_ne, hCK_ne, hδγ_ne] <;> ring
  calc
    ((2 * c * Fcard)^2) / ((2 * C * K^2 * Fcard^2 / c) * (2 * δ)^γ)
      = (4 * c^2 * Fcard^2) / ((2 * C * K^2 * Fcard^2 / c) * (2 * δ)^γ) := by ring
    _ = (4 * c^2 * Fcard^2) / (D / c) := by rw [h_denom]
    _ = (4 * c^3 * Fcard^2) / D := h_main
    _ = (4 * c^3) / ((2 : ℝ)^(1+γ) * C * K^2 * δ^γ) := h_cancel
    _ = (4 / (2 : ℝ)^(1+γ)) * (c^3 / (C * K^2)) * (δ^γ)⁻¹ := h_final
    _ = (2^(1-γ) * c^3 / (C * K^2)) * δ^(-γ) := by
      rw [h4div, hδneg] <;> ring

/-- Final algebra inequality for WZ1 Lemma 40. -/
lemma wz1_final_algebra (c C K Fcard δ γ A E_bound fiber_card : ℝ)
    (hcpos : 0 < c) (hcle_one : c ≤ 1) (hCpos : 0 < C) (hKpos : 0 < K)
    (hFpos : 0 < Fcard) (hδpos : 0 < δ) (hγpos : 0 < γ) (hγltone : γ < 1)
    (hA_def : A = C * (2 : ℝ)^γ)
    (hE_bound_def : E_bound = 2 * C * K^2 * Fcard^2 / c)
    (hfiber_ge : fiber_card ≥ 2 * c * Fcard) :
    fiber_card^2 / (E_bound * (2 * δ)^γ) ≥ (c^5 / (A * K^2)) * δ^(-γ) := by
  have h1 : fiber_card^2 ≥ (2 * c * Fcard)^2 := by gcongr
  have h2 : c^3 ≥ c^5 := by
    have h21 : 0 ≤ c := by linarith
    have h22 : c^2 ≤ 1 := by
      calc c^2
        = c * c := by ring
      _ ≤ 1 * c := by gcongr <;> linarith
      _ ≤ 1 := by linarith
    have h23 : c^5 ≤ c^3 := by
      calc c^5
        = c^3 * c^2 := by ring
      _ ≤ c^3 * 1 := by gcongr
      _ = c^3 := by ring
    exact h23
  have h25 : 2 * c^3 ≥ c^5 := by
    have h26 : 0 ≤ c^3 := by positivity
    linarith [h2]
  have h33 : (2 : ℝ)^(1-γ) * (2 : ℝ)^γ = (2 : ℝ) := by
    rw [←Real.rpow_add (by norm_num)] <;> ring_nf <;> norm_num
  have h_pos1 : 0 < C * K^2 := by positivity
  have h_pos2 : 0 < C * (2 : ℝ)^γ * K^2 := by positivity
  have h_ineq : (2 : ℝ)^(1-γ) * c^3 * (C * (2 : ℝ)^γ * K^2) ≥ c^5 * (C * K^2) := by
    calc
      (2 : ℝ)^(1-γ) * c^3 * (C * (2 : ℝ)^γ * K^2)
        = c^3 * (C * K^2) * ((2 : ℝ)^(1-γ) * (2 : ℝ)^γ) := by ring
      _ = c^3 * (C * K^2) * (2 : ℝ) := by rw [h33] <;> ring
      _ = (2 : ℝ) * c^3 * (C * K^2) := by ring
      _ ≥ c^5 * (C * K^2) := by
        exact mul_le_mul_of_nonneg_right h25 (by positivity)
  have h3 : (2 : ℝ)^(1-γ) * c^3 / (C * K^2) ≥ c^5 / (A * K^2) := by
    rw [hA_def]
    have h_goal : (2 : ℝ)^(1-γ) * c^3 / (C * K^2) ≥ c^5 / (C * (2 : ℝ)^γ * K^2) := by
      calc
        (2 : ℝ)^(1-γ) * c^3 / (C * K^2)
          = ((2 : ℝ)^(1-γ) * c^3 * (C * (2 : ℝ)^γ * K^2)) / ((C * K^2) * (C * (2 : ℝ)^γ * K^2)) := by
            field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
        _ ≥ (c^5 * (C * K^2)) / ((C * K^2) * (C * (2 : ℝ)^γ * K^2)) := by
            gcongr
        _ = c^5 / (C * (2 : ℝ)^γ * K^2) := by
            field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    exact h_goal
  have h4 : ((2 * c * Fcard)^2) / (E_bound * (2 * δ)^γ) =
      (2^(1-γ) * c^3 / (C * K^2)) * δ^(-γ) := by
    rw [hE_bound_def]
    exact wz1_h8_algebra c C K Fcard δ γ hcpos hCpos hKpos hFpos hδpos hγpos hγltone
  have h5 : 0 ≤ δ^(-γ) := by positivity
  calc
    fiber_card^2 / (E_bound * (2 * δ)^γ)
      ≥ ((2 * c * Fcard)^2) / (E_bound * (2 * δ)^γ) := by
        have hE_pos : 0 < E_bound := by
          rw [hE_bound_def] <;> positivity
        have hdenom_pos : 0 < E_bound * (2 * δ)^γ := by
          exact mul_pos hE_pos (by positivity)
        have h1_sq : (2 * c * Fcard)^2 ≤ fiber_card^2 := by gcongr
        exact div_le_div_of_nonneg_right h1_sq hdenom_pos.le
    _ = (2^(1-γ) * c^3 / (C * K^2)) * δ^(-γ) := h4
    _ ≥ (c^5 / (A * K^2)) * δ^(-γ) := by
      exact mul_le_mul_of_nonneg_right h3 h5

/-- General lemma: extend a double sum over `S × S` to `F × F` using indicator. -/
lemma sum_extend_subset {α : Type*} [DecidableEq α] {F S : Finset α} (h_sub : S ⊆ F) {g : α → α → ℝ} :
    (∑ x ∈ S, ∑ y ∈ S, g x y) =
    ∑ x ∈ F, ∑ y ∈ F, (if x ∈ S ∧ y ∈ S then g x y else 0) := by
  have h_filter1 : F.filter (fun x : α => x ∈ S) = S := by
    ext z; simp [Finset.mem_filter, h_sub] <;> tauto
  have h1 : ∑ x ∈ S, ∑ y ∈ S, g x y =
      ∑ x ∈ F, (if x ∈ S then ∑ y ∈ S, g x y else 0) := by
    have h_sum : ∑ x ∈ F.filter (fun x : α => x ∈ S), (∑ y ∈ S, g x y) =
        ∑ x ∈ F, (if x ∈ S then ∑ y ∈ S, g x y else 0) := by
      rw [Finset.sum_filter] <;> rfl
    rw [h_filter1] at h_sum
    exact h_sum
  rw [h1]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxs : x ∈ S
  · rw [if_pos hxs]
    have h_filter2 : F.filter (fun y : α => y ∈ S) = S := by
      ext z; simp [Finset.mem_filter, h_sub] <;> tauto
    have h2 : ∑ y ∈ S, g x y = ∑ y ∈ F, (if y ∈ S then g x y else 0) := by
      have h_sum : ∑ y ∈ F.filter (fun y : α => y ∈ S), g x y =
          ∑ y ∈ F, (if y ∈ S then g x y else 0) := by
        rw [Finset.sum_filter] <;> rfl
      rw [h_filter2] at h_sum
      exact h_sum
    rw [h2]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hys : y ∈ S
    · rw [if_pos hys, if_pos ⟨hxs, hys⟩]
    · rw [if_neg hys, if_neg (fun h => hys h.2)]
  · rw [if_neg hxs]
    symm
    apply Finset.sum_eq_zero
    intro y _
    have h_contra : ¬(x ∈ S ∧ y ∈ S) := by tauto
    rw [if_neg h_contra]


lemma energy_combine_algebra
    {F G₁ G₂ : Finset Point2}
    {C_ang_unnorm K_frost0 K C_total : ℝ}
    (hK_one : 1 ≤ K)
    (hK_frost0_pos : 0 < K_frost0)
    (hC_ang_unnorm_nonneg : 0 ≤ C_ang_unnorm)
    (hC_total_def : C_total = 1 + C_ang_unnorm * (2 + 2 * K_frost0))
    (diag_sum off_sum : ℝ)
    (h_diag : diag_sum ≤ K * (F.card : ℝ)^2 * (G₁.card : ℝ) * (G₂.card : ℝ))
    (h_off : off_sum ≤ C_ang_unnorm * K * (G₁.card : ℝ) * (G₂.card : ℝ) *
                 ((F.card : ℝ)^2 + (1 + 2 * K_frost0) * K * (F.card : ℝ)^2)) :
    diag_sum + off_sum ≤ C_total * K^2 * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ)^2 := by
  set X : ℝ := (F.card : ℝ)^2 * (G₁.card : ℝ) * (G₂.card : ℝ) with hX
  have hX_nonneg : 0 ≤ X := by positivity
  have h1 : diag_sum ≤ K * X := by
    have h_eq : K * (F.card : ℝ)^2 * (G₁.card : ℝ) * (G₂.card : ℝ) = K * X := by
      simp [hX] <;> ring
    rw [h_eq] at h_diag
    exact h_diag
  have h2 : off_sum ≤ C_ang_unnorm * K * X * (1 + (1 + 2 * K_frost0) * K) := by
    have h_eq : C_ang_unnorm * K * (G₁.card : ℝ) * (G₂.card : ℝ) *
               ((F.card : ℝ)^2 + (1 + 2 * K_frost0) * K * (F.card : ℝ)^2) =
             C_ang_unnorm * K * X * (1 + (1 + 2 * K_frost0) * K) := by
      simp [hX] <;> ring
    rw [h_eq] at h_off
    exact h_off
  have hK2 : K ≤ K^2 := by nlinarith
  have h3 : K * X ≤ K^2 * X := mul_le_mul_of_nonneg_right hK2 hX_nonneg
  have h4 : K * (1 + (1 + 2 * K_frost0) * K) ≤ K^2 * (2 + 2 * K_frost0) := by
    have h5 : 0 ≤ K := by linarith
    nlinarith
  have h6 : 0 ≤ C_ang_unnorm * X := by positivity
  have h7 : C_ang_unnorm * K * X * (1 + (1 + 2 * K_frost0) * K) ≤
           C_ang_unnorm * K^2 * X * (2 + 2 * K_frost0) := by
    calc
      C_ang_unnorm * K * X * (1 + (1 + 2 * K_frost0) * K)
        = (C_ang_unnorm * X) * (K * (1 + (1 + 2 * K_frost0) * K)) := by ring
      _ ≤ (C_ang_unnorm * X) * (K^2 * (2 + 2 * K_frost0)) := mul_le_mul_of_nonneg_left h4 h6
      _ = C_ang_unnorm * K^2 * X * (2 + 2 * K_frost0) := by ring
  have h8 : diag_sum + off_sum ≤ K^2 * X + C_ang_unnorm * K^2 * X * (2 + 2 * K_frost0) := by
    linarith [h1, h2, h3, h7]
  have h9 : K^2 * X + C_ang_unnorm * K^2 * X * (2 + 2 * K_frost0) =
           (1 + C_ang_unnorm * (2 + 2 * K_frost0)) * K^2 * X := by ring
  have h10 : (1 + C_ang_unnorm * (2 + 2 * K_frost0)) * K^2 * X =
           C_total * K^2 * X := by
    rw [hC_total_def] <;> ring
  calc diag_sum + off_sum
    ≤ K^2 * X + C_ang_unnorm * K^2 * X * (2 + 2 * K_frost0) := h8
  _ = (1 + C_ang_unnorm * (2 + 2 * K_frost0)) * K^2 * X := h9
  _ = C_total * K^2 * X := h10
  _ = C_total * K^2 * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ)^2 := by
    simp [hX] <;> ring
  _ = C_total * K^2 * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ)^2 := by
    simp [hX] <;> ring

lemma wz1_off_diagonal_point_energy
    {G₁ G₂ : Finset Point2} {E : Finset (Point2 × Point2)}
    {δ γ K C_ang_unnorm : ℝ}
    (hδ : 0 < δ)
    (Q_xy : Point2 → Point2 → Finset (Point2 × Point2))
    (g : Point2 → Point2 → Point2 × Point2 → ℝ)
    (h_g : ∀ x y p, g x y p =
      (max (|inner ℝ (x - y) (p.1 - p.2)|) δ)^(-γ))
    (hQ_sub : ∀ x y, Q_xy x y ⊆ E)
    (h_factor_combined : ∀ (d : ℝ), 0 < d → ∀ (a : ℝ), 0 ≤ a →
      (max (d * a) δ)^(-γ) ≤ (1 + d^(-γ)) * (max a δ)^(-γ))
    (h_decompose : ∀ (v : Point2), ‖v‖ = 1 →
      ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) ≤
        (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ))
    (x y : Point2) (hne : x ≠ y) :
    ∑ p ∈ Q_xy x y, g x y p ≤
      (1 + ‖x - y‖^(-γ)) * (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ) := by
  set d : ℝ := ‖x - y‖ with hd_def
  have hd_pos : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set v : Point2 := d⁻¹ • (x - y) with hv_def
  have hv_unit : ‖v‖ = 1 := by
    rw [hv_def]
    have h1 : ‖(d⁻¹ : ℝ) • (x - y)‖ = |(d⁻¹ : ℝ)| * ‖x - y‖ := norm_smul _ _
    rw [h1]
    have h2 : |(d⁻¹ : ℝ)| = d⁻¹ := by rw [abs_of_pos (inv_pos.mpr hd_pos)]
    have h3 : ‖x - y‖ = d := hd_def.symm
    rw [h2, h3]
    field_simp [hd_pos.ne'] <;> ring
  have h_inner : ∀ p : Point2 × Point2,
      |inner ℝ (x - y) (p.1 - p.2)| = d * |inner ℝ v (p.1 - p.2)| := by
    intro p
    have h2 : inner ℝ v (p.1 - p.2) = d⁻¹ * inner ℝ (x - y) (p.1 - p.2) := by
      rw [hv_def, inner_smul_left] <;> rfl
    have h1 : inner ℝ (x - y) (p.1 - p.2) = d * inner ℝ v (p.1 - p.2) := by
      calc inner ℝ (x - y) (p.1 - p.2)
        = d * (d⁻¹ * inner ℝ (x - y) (p.1 - p.2)) := by
            field_simp [hd_pos.ne'] <;> ring
        _ = d * inner ℝ v (p.1 - p.2) := by rw [h2]
    rw [h1, abs_mul, abs_of_pos hd_pos] <;> ring
  have h6 : ∑ p ∈ Q_xy x y, g x y p ≤
      ∑ p ∈ Q_xy x y,
        (1 + d^(-γ)) * (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) := by
    apply Finset.sum_le_sum
    intro p _
    rw [h_g x y p, h_inner p]
    exact h_factor_combined d hd_pos (|inner ℝ v (p.1 - p.2)|) (by positivity)
  have h8 : ∑ p ∈ Q_xy x y,
      (1 + d^(-γ)) * (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) =
      (1 + d^(-γ)) *
        ∑ p ∈ Q_xy x y, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) := by
    rw [Finset.mul_sum] <;> ring
  rw [h8] at h6
  have h9 : ∑ p ∈ Q_xy x y, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) ≤
      ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (hQ_sub x y)
    intro p _ _
    positivity
  have h10 : ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) ≤
      (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ) :=
    h_decompose v hv_unit
  have h11 : 0 ≤ 1 + d^(-γ) := by positivity
  calc
    ∑ p ∈ Q_xy x y, g x y p
      ≤ (1 + d^(-γ)) *
          ∑ p ∈ Q_xy x y, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) := h6
    _ ≤ (1 + d^(-γ)) *
          ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) := by gcongr
    _ ≤ (1 + d^(-γ)) *
          ((G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ)) := by gcongr
    _ = (1 + d^(-γ)) * (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ) := by
      ring

/-- Sum the pointwise off-diagonal energy bound over all ordered pairs. -/
lemma wz1_off_diagonal_total_energy
    {F G₁ G₂ : Finset Point2}
    {delta gamma K C_ang K_frost : ℝ}
    (Q_xy : Point2 → Point2 → Finset (Point2 × Point2))
    (g : Point2 → Point2 → Point2 × Point2 → ℝ)
    (hF_sep : DiscreteSet.IsDeltaSeparated F delta)
    (hC_ang_nonneg : 0 ≤ C_ang)
    (hK_nonneg : 0 ≤ K)
    (h_reg_energy :
      ∑ x ∈ F, ∑ y ∈ F, (max (dist x y) delta)^(-gamma) ≤
        (1 + 2 * K_frost) * K * (F.card : ℝ)^2)
    (h_off_diag_point : ∀ (x y : Point2), x ≠ y →
      ∑ point ∈ Q_xy x y, g x y point ≤
        (1 + ‖x - y‖^(-gamma)) *
          (G₁.card : ℝ) * C_ang * K * (G₂.card : ℝ)) :
    ∑ x ∈ F, ∑ y ∈ F,
        (if x ≠ y then ∑ point ∈ Q_xy x y, g x y point else 0) ≤
      C_ang * K * (G₁.card : ℝ) * (G₂.card : ℝ) *
        ((F.card : ℝ)^2 +
          (1 + 2 * K_frost) * K * (F.card : ℝ)^2) := by
  let offDiagonal : Finset (Point2 × Point2) :=
    (F ×ˢ F).filter (fun pair => pair.1 ≠ pair.2)
  have hoff_eq :
      ∑ x ∈ F, ∑ y ∈ F,
          (if x ≠ y then ∑ point ∈ Q_xy x y, g x y point else 0) =
        ∑ pair ∈ offDiagonal,
          ∑ point ∈ Q_xy pair.1 pair.2, g pair.1 pair.2 point := by
    calc
      ∑ x ∈ F, ∑ y ∈ F,
          (if x ≠ y then ∑ point ∈ Q_xy x y, g x y point else 0)
          = ∑ pair ∈ F ×ˢ F,
              (if pair.1 ≠ pair.2 then
                ∑ point ∈ Q_xy pair.1 pair.2, g pair.1 pair.2 point
              else 0) := by
                rw [Finset.sum_product]
      _ = ∑ pair ∈ offDiagonal,
            ∑ point ∈ Q_xy pair.1 pair.2, g pair.1 pair.2 point := by
              rw [← Finset.sum_filter]
  rw [hoff_eq]
  have hpointwise :
      ∑ pair ∈ offDiagonal,
          ∑ point ∈ Q_xy pair.1 pair.2, g pair.1 pair.2 point ≤
        ∑ pair ∈ offDiagonal,
          (1 + ‖pair.1 - pair.2‖^(-gamma)) *
            (G₁.card : ℝ) * C_ang * K * (G₂.card : ℝ) := by
    apply Finset.sum_le_sum
    intro pair hpair
    exact h_off_diag_point pair.1 pair.2 (Finset.mem_filter.mp hpair).2
  apply hpointwise.trans
  let coefficient : ℝ :=
    (G₁.card : ℝ) * C_ang * K * (G₂.card : ℝ)
  have hsum_factor :
      ∑ pair ∈ offDiagonal,
          (1 + ‖pair.1 - pair.2‖^(-gamma)) *
            (G₁.card : ℝ) * C_ang * K * (G₂.card : ℝ) =
        coefficient *
          ∑ pair ∈ offDiagonal, (1 + ‖pair.1 - pair.2‖^(-gamma)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pair hpair
    dsimp only [coefficient]
    ring
  rw [hsum_factor]
  have hsum_add :
      ∑ pair ∈ offDiagonal, (1 + ‖pair.1 - pair.2‖^(-gamma)) =
        (offDiagonal.card : ℝ) +
          ∑ pair ∈ offDiagonal, ‖pair.1 - pair.2‖^(-gamma) := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum_add]
  have hcard :
      (offDiagonal.card : ℝ) ≤ (F.card : ℝ)^2 := by
    have hoff_subset : offDiagonal ⊆ F ×ˢ F :=
      Finset.filter_subset _ _
    have hcard_nat := Finset.card_le_card hoff_subset
    rw [Finset.card_product] at hcard_nat
    have hcard_real :
        (offDiagonal.card : ℝ) ≤ (F.card : ℝ) * (F.card : ℝ) := by
      exact_mod_cast hcard_nat
    simpa [pow_two] using hcard_real
  have hnorm_energy :
      ∑ pair ∈ offDiagonal, ‖pair.1 - pair.2‖^(-gamma) ≤
        ∑ x ∈ F, ∑ y ∈ F,
          (max (dist x y) delta)^(-gamma) := by
    have hoff_subset : offDiagonal ⊆ F ×ˢ F :=
      Finset.filter_subset _ _
    have hpairwise : ∀ pair ∈ offDiagonal,
        ‖pair.1 - pair.2‖^(-gamma) ≤
          (max (dist pair.1 pair.2) delta)^(-gamma) := by
      intro pair hpair
      have hpair_data := Finset.mem_filter.mp hpair
      have hmembers := Finset.mem_product.mp hpair_data.1
      have hsep := hF_sep hmembers.1 hmembers.2 hpair_data.2
      have hmax :
          max (dist pair.1 pair.2) delta = dist pair.1 pair.2 :=
        max_eq_left hsep
      have hnorm :
          ‖pair.1 - pair.2‖ = dist pair.1 pair.2 := by
        rw [dist_eq_norm]
      rw [hnorm, hmax]
    calc
      ∑ pair ∈ offDiagonal, ‖pair.1 - pair.2‖^(-gamma)
          ≤ ∑ pair ∈ offDiagonal,
              (max (dist pair.1 pair.2) delta)^(-gamma) :=
            Finset.sum_le_sum hpairwise
      _ ≤ ∑ pair ∈ F ×ˢ F,
              (max (dist pair.1 pair.2) delta)^(-gamma) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hoff_subset
              (fun pair hpair hnotmem => by positivity)
      _ = ∑ x ∈ F, ∑ y ∈ F,
              (max (dist x y) delta)^(-gamma) := by
            rw [Finset.sum_product]
  have hsum_bound :
      (offDiagonal.card : ℝ) +
          ∑ pair ∈ offDiagonal, ‖pair.1 - pair.2‖^(-gamma) ≤
        (F.card : ℝ)^2 +
          (1 + 2 * K_frost) * K * (F.card : ℝ)^2 := by
    exact add_le_add hcard (hnorm_energy.trans h_reg_energy)
  have hcoefficient_nonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  calc
    coefficient *
        ((offDiagonal.card : ℝ) +
          ∑ pair ∈ offDiagonal, ‖pair.1 - pair.2‖^(-gamma))
        ≤ coefficient *
            ((F.card : ℝ)^2 +
              (1 + 2 * K_frost) * K * (F.card : ℝ)^2) :=
          mul_le_mul_of_nonneg_left hsum_bound hcoefficient_nonneg
    _ = C_ang * K * (G₁.card : ℝ) * (G₂.card : ℝ) *
          ((F.card : ℝ)^2 +
            (1 + 2 * K_frost) * K * (F.card : ℝ)^2) := by
          dsimp only [coefficient]
          ring

/-- Bound the diagonal contribution to the total projection energy. -/
lemma wz1_diagonal_energy_bound
    {F G₁ G₂ : Finset Point2}
    {Q : Finset (Point2 × Point2)}
    {delta gamma K : ℝ}
    (Q_xy : Point2 → Point2 → Finset (Point2 × Point2))
    (g : Point2 → Point2 → Point2 × Point2 → ℝ)
    (hdelta : 0 < delta)
    (hdiag :
      ∀ x ∈ F, ∀ p ∈ Q_xy x x, g x x p = delta ^ (-gamma))
    (hQxy : ∀ x, Q_xy x x ⊆ Q)
    (hQ_sub : Q ⊆ G₁ ×ˢ G₂)
    (hdelta_energy :
      delta ^ (-gamma) ≤ K * (F.card : ℝ)) :
    ∑ x ∈ F, ∑ p ∈ Q_xy x x, g x x p ≤
      K * (F.card : ℝ) ^ 2 *
        (G₁.card : ℝ) * (G₂.card : ℝ) := by
  have hsum_eq :
      ∑ x ∈ F, ∑ p ∈ Q_xy x x, g x x p =
        delta ^ (-gamma) * ∑ x ∈ F, ((Q_xy x x).card : ℝ) := by
    calc
      ∑ x ∈ F, ∑ p ∈ Q_xy x x, g x x p
          = ∑ x ∈ F, ((Q_xy x x).card : ℝ) * delta ^ (-gamma) := by
            apply Finset.sum_congr rfl
            intro x hx
            calc
              ∑ p ∈ Q_xy x x, g x x p
                  = ∑ p ∈ Q_xy x x, delta ^ (-gamma) := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    exact hdiag x hx p hp
              _ = ((Q_xy x x).card : ℝ) * delta ^ (-gamma) := by
                    simp [Finset.sum_const]
      _ = delta ^ (-gamma) *
          ∑ x ∈ F, ((Q_xy x x).card : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hcount :
      ∑ x ∈ F, ((Q_xy x x).card : ℝ) ≤
        (F.card : ℝ) * (Q.card : ℝ) := by
    calc
      ∑ x ∈ F, ((Q_xy x x).card : ℝ)
          ≤ ∑ x ∈ F, (Q.card : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            exact_mod_cast Finset.card_le_card (hQxy x)
      _ = (F.card : ℝ) * (Q.card : ℝ) := by
            simp [Finset.sum_const]
  have hQ_card :
      (Q.card : ℝ) ≤ (G₁.card : ℝ) * (G₂.card : ℝ) := by
    have h := Finset.card_le_card hQ_sub
    rw [Finset.card_product] at h
    exact_mod_cast h
  have hpow_nonneg : 0 ≤ delta ^ (-gamma) := by
    positivity
  rw [hsum_eq]
  calc
    delta ^ (-gamma) * ∑ x ∈ F, ((Q_xy x x).card : ℝ)
        ≤ delta ^ (-gamma) * ((F.card : ℝ) * (Q.card : ℝ)) := by
          gcongr
    _ ≤ delta ^ (-gamma) *
        ((F.card : ℝ) * ((G₁.card : ℝ) * (G₂.card : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hQ_card (Nat.cast_nonneg F.card))
            hpow_nonneg
    _ ≤ (K * (F.card : ℝ)) *
        ((F.card : ℝ) * ((G₁.card : ℝ) * (G₂.card : ℝ))) := by
          gcongr
    _ = K * (F.card : ℝ) ^ 2 *
        (G₁.card : ℝ) * (G₂.card : ℝ) := by
          ring

/-- Split a finite double sum into its diagonal and off-diagonal parts. -/
lemma wz1_sum_split_diagonal
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (F : Finset α) (term : α → α → β) :
    ∑ x ∈ F, ∑ y ∈ F, term x y =
      (∑ x ∈ F, term x x) +
        ∑ x ∈ F, ∑ y ∈ F, (if x ≠ y then term x y else 0) := by
  have hrow : ∀ x ∈ F,
      ∑ y ∈ F, term x y =
        term x x + ∑ y ∈ F, (if x ≠ y then term x y else 0) := by
    intro x hx
    calc
      ∑ y ∈ F, term x y
          = ∑ y ∈ F,
              ((if x = y then term x y else 0) +
                (if x ≠ y then term x y else 0)) := by
                apply Finset.sum_congr rfl
                intro y hy
                by_cases h : x = y <;> simp [h]
      _ = (∑ y ∈ F, if x = y then term x y else 0) +
            ∑ y ∈ F, (if x ≠ y then term x y else 0) := by
              rw [Finset.sum_add_distrib]
      _ = term x x +
            ∑ y ∈ F, (if x ≠ y then term x y else 0) := by
              congr 1
              have hsingle :
                  (∑ y ∈ F, if x = y then term x y else 0) =
                    (if x = x then term x x else 0) := by
                apply Finset.sum_eq_single_of_mem x hx
                intro y hy hne
                have hxy : x ≠ y := fun h => hne h.symm
                simp [hxy]
              simpa using hsingle
  calc
    ∑ x ∈ F, ∑ y ∈ F, term x y
        = ∑ x ∈ F,
            (term x x +
              ∑ y ∈ F, (if x ≠ y then term x y else 0)) := by
                apply Finset.sum_congr rfl
                intro x hx
                exact hrow x hx
    _ = (∑ x ∈ F, term x x) +
          ∑ x ∈ F, ∑ y ∈ F,
            (if x ≠ y then term x y else 0) := by
            rw [Finset.sum_add_distrib]

/-- Transfer diagonal and off-diagonal bounds through exact energy rewrites. -/
lemma wz1_combine_split_energy
    {F G₁ G₂ : Finset Point2}
    {C_ang_unnorm K_frost0 K C_total total middle diag off : ℝ}
    (hK_one : 1 ≤ K)
    (hK_frost0_pos : 0 < K_frost0)
    (hC_ang_unnorm_nonneg : 0 ≤ C_ang_unnorm)
    (hC_total_def : C_total = 1 + C_ang_unnorm * (2 + 2 * K_frost0))
    (hinterchange : total = middle)
    (hsplit : middle = diag + off)
    (hdiag : diag ≤ K * (F.card : ℝ)^2 * (G₁.card : ℝ) * (G₂.card : ℝ))
    (hoff : off ≤ C_ang_unnorm * K * (G₁.card : ℝ) * (G₂.card : ℝ) *
      ((F.card : ℝ)^2 + (1 + 2 * K_frost0) * K * (F.card : ℝ)^2)) :
    total ≤ C_total * K^2 * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ)^2 := by
  rw [hinterchange, hsplit]
  exact energy_combine_algebra hK_one hK_frost0_pos hC_ang_unnorm_nonneg
    hC_total_def diag off hdiag hoff

/-- Divide a total-energy estimate by a dense product and cancel its factors. -/
lemma wz1_average_energy_bound
    {total q coefficient density left right scale : ℝ}
    (hq_pos : 0 < q)
    (hdensity_pos : 0 < density)
    (hleft_pos : 0 < left)
    (hright_pos : 0 < right)
    (hcoefficient_nonneg : 0 ≤ coefficient)
    (hscale_nonneg : 0 ≤ scale)
    (hsize : density * left * right ≤ q)
    (htotal : total ≤ coefficient * left * right * scale) :
    total / q ≤ coefficient * scale / density := by
  have hnumerator_nonneg :
      0 ≤ coefficient * left * right * scale := by
    positivity
  calc
    total / q
        ≤ (coefficient * left * right * scale) / q :=
          div_le_div_of_nonneg_right htotal hq_pos.le
    _ ≤ (coefficient * left * right * scale) /
          (density * left * right) := by
          exact div_le_div_of_nonneg_left hnumerator_nonneg
            (by positivity) hsize
    _ = coefficient * scale / density := by
          field_simp [hdensity_pos.ne', hleft_pos.ne', hright_pos.ne']
          <;> ring

/-- A nonempty finite family has an entry at most twice its arithmetic mean. -/
lemma wz1_exists_le_twice_average
    {α : Type*} [DecidableEq α]
    (Q : Finset α) (energy : α → ℝ)
    (hQ_nonempty : Q.Nonempty)
    (henergy_nonneg : ∀ point ∈ Q, 0 ≤ energy point) :
    ∃ point ∈ Q,
      energy point ≤ 2 * ((∑ candidate ∈ Q, energy candidate) / (Q.card : ℝ)) := by
  let average : ℝ := (∑ candidate ∈ Q, energy candidate) / (Q.card : ℝ)
  have hQ_pos : 0 < (Q.card : ℝ) := by
    exact_mod_cast hQ_nonempty.card_pos
  have havg_nonneg : 0 ≤ average := by
    dsimp only [average]
    exact div_nonneg
      (Finset.sum_nonneg fun point hpoint => henergy_nonneg point hpoint)
      hQ_pos.le
  have hexists : ∃ point ∈ Q, energy point ≤ average := by
    by_contra h
    push Not at h
    have hsum :
        ∑ point ∈ Q, average < ∑ point ∈ Q, energy point := by
      exact Finset.sum_lt_sum_of_nonempty hQ_nonempty
        (fun point hpoint => h point hpoint)
    have hsum_average :
        ∑ point ∈ Q, average = (Q.card : ℝ) * average := by
      simp [Finset.sum_const]
    have hcard_average :
        (Q.card : ℝ) * average = ∑ point ∈ Q, energy point := by
      dsimp only [average]
      field_simp [hQ_pos.ne']
    rw [hsum_average, hcard_average] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨point, hpoint, hpoint_average⟩ := hexists
  exact ⟨point, hpoint, hpoint_average.trans (by linarith)⟩

/-- The regularized projection energy of a finite set is nonnegative. -/
lemma wz1_projection_energy_nonneg
    (A : Finset Point2) (direction : Point2)
    {delta gamma : ℝ} (hdelta : 0 < delta) :
    0 ≤ ∑ x ∈ A, ∑ y ∈ A,
      (max (dist (inner ℝ x direction) (inner ℝ y direction)) delta) ^ (-gamma) := by
  exact Finset.sum_nonneg fun x hx =>
    Finset.sum_nonneg fun y hy => by positivity

/-- Propagate a pointwise twice-average bound through an average estimate. -/
lemma wz1_le_twice_of_le_twice_of_le
    {energy average bound : ℝ}
    (henergy : energy ≤ 2 * average) (haverage : average ≤ bound) :
    energy ≤ 2 * bound :=
  henergy.trans (mul_le_mul_of_nonneg_left haverage (by norm_num))

/-- Membership in a projected triple fiber retains the original triple. -/
lemma wz1_triple_mem_of_mem_projected_fiber
    (H : Finset (Point2 × Point2 × Point2))
    (pair : Point2 × Point2) (point : Point2)
    (hpoint :
      point ∈
        (H.filter (fun triple =>
          triple.2.1 = pair.1 ∧ triple.2.2 = pair.2)).image
          (fun triple => triple.1)) :
    (point, pair.1, pair.2) ∈ H := by
  rcases Finset.mem_image.mp hpoint with ⟨triple, htriple, hfirst⟩
  have htriple_H : triple ∈ H := (Finset.mem_filter.mp htriple).1
  have hpair :
      triple.2.1 = pair.1 ∧ triple.2.2 = pair.2 :=
    (Finset.mem_filter.mp htriple).2
  have htriple_eq : triple = (point, pair.1, pair.2) := by
    exact Prod.ext hfirst (Prod.ext hpair.1 hpair.2)
  simpa [htriple_eq] using htriple_H

/-- The dot-product image of a projected triple fiber lies in the full image. -/
lemma wz1_projected_fiber_dot_image_subset
    (H : Finset (Point2 × Point2 × Point2))
    (pair : Point2 × Point2) :
    (fun point : Point2 => inner ℝ point (pair.1 - pair.2)) ''
        (((H.filter (fun triple =>
          triple.2.1 = pair.1 ∧ triple.2.2 = pair.2)).image
          (fun triple => triple.1) : Finset Point2) : Set Point2) ⊆
      wz1DotDifferenceSet H := by
  intro value hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  have htriple :=
    wz1_triple_mem_of_mem_projected_fiber H pair point hpoint
  exact Finset.mem_image.mpr
    ⟨(point, pair.1, pair.2), htriple, rfl⟩

def WZ1ThinTubesLargeDotProductAt (ε : ℝ) : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∀ c K : ℝ, 0 ≤ c → c < 1 → 1 ≤ K →
          ∀ F G₁ G₂ : DiscreteSet 2,
            F.Nonempty → G₁.Nonempty → G₂.Nonempty →
            F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
            F.IsDeltaSeparated δ →
            G₁.IsDeltaSeparated δ →
            G₂.IsDeltaSeparated δ →
            F.IsFrostman δ 1 (ENNReal.ofReal K) →
            G₁.IsFrostman δ 1 (ENNReal.ofReal K) →
            G₂.IsFrostman δ 1 (ENNReal.ofReal K) →
            WZ1StandardSeparation F G₁ G₂ →
            HasDiscreteThinTubes δ 1 K c G₁ G₂ →
            ∀ H : Finset (Point2 × Point2 × Point2),
              WZ1UniformTripleDensity
                (ENNReal.ofReal (2 * c)) F G₁ G₂ H →
                ENNReal.ofReal
                    ((c ^ 5 / (A * K ^ 2)) *
                      Real.rpow δ (ε - 1)) ≤
                  (↑(Metric.externalCoveringNumber
                    (Real.toNNReal δ)
                    (wz1DotDifferenceSet H)) : ENNReal)

lemma wz1_thin_tubes_large_dot_product_at_of_one_le
    (ε : ℝ) (h_eps : 1 ≤ ε) :
    WZ1ThinTubesLargeDotProductAt ε := by
  refine' ⟨1, by norm_num, 1, by norm_num, by norm_num, _⟩
  intro δ hδ hδ0 c K hc hc1 hK F G₁ G₂ hneF hneG1 hneG2
    hF_ball hG1_ball hG2_ball hF_sep hG1_sep hG2_sep
    hF_frost hG1_frost hG2_frost h_std h_thin_tubes H h_dense
  have h1 : 0 ≤ ε - 1 := by linarith
  have h2 : Real.rpow δ (ε - 1) ≤ 1 := by
    apply Real.rpow_le_one
    <;> linarith
  have h3 : (c ^ 5 / K ^ 2) * Real.rpow δ (ε - 1) ≤ 1 := by
    have h4 : 0 ≤ c := by linarith
    have h5 : c < 1 := hc1
    have h6 : c ^ 5 ≤ 1 := by
      calc c ^ 5 ≤ 1 ^ 5 := by gcongr <;> linarith
      _ = 1 := by norm_num
    have h7 : 1 ≤ K ^ 2 := by nlinarith
    have h8 : c ^ 5 ≤ K ^ 2 := by nlinarith
    have h9 : c ^ 5 / K ^ 2 ≤ 1 := by
      apply (div_le_one (show 0 < K ^ 2 from by positivity)).mpr
      exact h8
    have h10 : 0 ≤ Real.rpow δ (ε - 1) := Real.rpow_nonneg (by linarith) (ε - 1)
    have h11 : Real.rpow δ (ε - 1) ≤ 1 := h2
    have h12 : 0 ≤ c ^ 5 / K ^ 2 := by positivity
    nlinarith
  have hHne : H.Nonempty := by
    have h : WZ1UniformTripleDensity (ENNReal.ofReal (2 * c)) F G₁ G₂ H := h_dense
    simpa [WZ1UniformTripleDensity] using h.1
  have hne_set : (wz1DotDifferenceSet H).Nonempty := by
    rcases hHne with ⟨h, hh⟩
    have h_in : inner ℝ h.1 (h.2.1 - h.2.2) ∈ (wz1DotDifferenceSet H) := by
      simp only [wz1DotDifferenceSet]
      exact Finset.mem_image_of_mem _ hh
    exact ⟨_, h_in⟩
  have h4 : 1 ≤ Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H) := by
    have hne : (wz1DotDifferenceSet H) ≠ ∅ := hne_set.ne_empty
    have h5 : Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H) ≠ 0 :=
      mt (Metric.externalCoveringNumber_eq_zero.mp) hne
    exact Order.one_le_iff_ne_zero.mpr h5
  have h_pos : 0 ≤ (c ^ 5 / K ^ 2) * Real.rpow δ (ε - 1) := by
    apply mul_nonneg
    · positivity
    · exact Real.rpow_nonneg (by linarith) _
  have h_ofReal : ENNReal.ofReal ((c ^ 5 / K ^ 2) * Real.rpow δ (ε - 1)) ≤ ENNReal.ofReal (1 : ℝ) :=
    ENNReal.ofReal_le_ofReal h3
  have h5 : ENNReal.ofReal ((c ^ 5 / K ^ 2) * Real.rpow δ (ε - 1)) ≤ (1 : ENNReal) := by
    rw [ENNReal.ofReal_one] at h_ofReal
    exact h_ofReal
  have h7 : (1 : ENNReal) ≤ ↑(Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H)) := by
    exact_mod_cast h4
  have h_goal : ENNReal.ofReal ((c ^ 5 / K ^ 2) * Real.rpow δ (ε - 1)) ≤
      ↑(Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H)) :=
    le_trans h5 h7
  simpa using h_goal

lemma wz1_thin_tubes_large_dot_product_at_of_lt_one
    (ε : ℝ) (hε : 0 < ε) (h_eps_lt_one : ε < 1) :
    WZ1ThinTubesLargeDotProductAt ε := by
    set γ : ℝ := 1 - ε with hγ_def
    have hγ_pos : 0 < γ := by linarith
    have hγ_lt_one : γ < 1 := by linarith
    set C_ang : ℝ := angularSumConst γ with hC_ang_def
    set K_frost0 : ℝ := kaufman_K_frost0 1 γ with hK_frost0_def
    set C_total : ℝ := totalEnergyConst γ with hC_total_def
    set A : ℝ := C_total * (2 : ℝ)^γ with hA_def
    have h1_pos : 0 < (2 : ℝ)^(1 - γ) - 1 := by
      have h2 : 1 < (2 : ℝ)^(1 - γ) := Real.one_lt_rpow (by norm_num) (by linarith)
      linarith
    have hC_ang_pos : 0 < C_ang := by
      dsimp only [C_ang, angularSumConst]
      have h1 : 0 < (2 : ℝ)^(1 + γ) := by positivity
      have h2 : (2 : ℝ)^(γ - 1) < 1 := by
        have h3 : γ - 1 < 0 := by linarith
        have h4 : (2 : ℝ)^(γ - 1) < (2 : ℝ)^(0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h3
        simpa using h4
      have h3 : 0 < 1 - (2 : ℝ)^(γ - 1) := by linarith
      have h4 : 0 < (2 : ℝ)^(1 + γ) / (1 - (2 : ℝ)^(γ - 1)) := div_pos h1 h3
      linarith
    have hK_frost0_pos : 0 < K_frost0 := by
      dsimp only [K_frost0, kaufman_K_frost0]; positivity
    have hC_total_pos : 0 < C_total := by
      rw [hC_total_def]
      dsimp only [totalEnergyConst]
      have h_pos : 0 < (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * (2 + 2 * kaufman_K_frost0 1 γ) := by
        positivity
      linarith
    have hC_total_ge_one : 1 ≤ C_total := by
      rw [hC_total_def]
      dsimp only [totalEnergyConst]
      have h_pos : 0 ≤ (2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)) * (2 + 2 * kaufman_K_frost0 1 γ) := by
        positivity
      linarith
    have h2_pow_ge_one : 1 ≤ (2 : ℝ)^γ := Real.one_le_rpow (by norm_num) (by linarith)
    have hA_ge_one : 1 ≤ A := by
      rw [hA_def]
      nlinarith [hC_total_pos, hC_total_ge_one, h2_pow_ge_one]
    refine' ⟨A, hA_ge_one, 1, by norm_num, by norm_num, _⟩
    intro δ hδ hδ0 c K hc hc1 hK F G₁ G₂ hneF hneG1 hneG2
      hF_ball hG1_ball hG2_ball hF_sep hG1_sep hG2_sep
      hF_frost hG1_frost hG2_frost h_std h_thin_tubes H h_dense
    by_cases h_c0 : c = 0
    · rw [h_c0]; simp
    · have hc_pos : 0 < c :=
        lt_of_le_of_ne hc (Ne.symm h_c0)
      rcases h_thin_tubes with ⟨hβ, hK', hc_range, E, hE_sub, hE_mass, h_thin⟩
      have hK_one : 1 ≤ K := hK'
      let piH : Finset (Point2 × Point2) := H.image (fun h => (h.2.1, h.2.2))
      have h_vertex : ∀ (t : Point2 × Point2 × Point2), t ∈ H → t.1 ∈ F ∧ t.2.1 ∈ G₁ ∧ t.2.2 ∈ G₂ :=
        density_vertex_containment h_dense
      have hpiH_sub : piH ⊆ G₁ ×ˢ G₂ := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
        have h := h_vertex t ht
        exact Finset.mem_product.mpr ⟨h.2.1, h.2.2⟩
      have h_piH_size_enn : (piH.card : ENNReal) ≥
          ENNReal.ofReal (2 * c) * (G₁.card : ENNReal) * (G₂.card : ENNReal) :=
        density_projection_bound hc h_dense
      have hE_size_real : (E.card : ℝ) ≥ (1 - c) * (G₁.card : ℝ) * (G₂.card : ℝ) := by
        have h4 : (1 - ENNReal.ofReal c) = ENNReal.ofReal (1 - c) := by
          have h51 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
          rw [h51]
          have h5 : ENNReal.ofReal (1 - c) = ENNReal.ofReal (1 : ℝ) - ENNReal.ofReal c := by
            rw [ENNReal.ofReal_sub (1 : ℝ) (show 0 ≤ c from by linarith)] <;> norm_num
          exact h5.symm
        have hE_mass' : ENNReal.ofReal (1 - c) * (G₁.card : ENNReal) * (G₂.card : ENNReal) ≤ (E.card : ENNReal) := by
          rw [←h4]
          exact hE_mass
        have h_fin1 : (E.card : ENNReal) ≠ ⊤ := by simp
        have hE_real := ENNReal.toReal_mono h_fin1 hE_mass'
        have h_left : (ENNReal.ofReal (1 - c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)).toReal =
            (1 - c) * (G₁.card : ℝ) * (G₂.card : ℝ) := by
          have h1 : (ENNReal.ofReal (1 - c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)).toReal =
              (ENNReal.ofReal (1 - c) * (G₁.card : ENNReal)).toReal * (G₂.card : ℝ) := by
            rw [ENNReal.toReal_mul] <;> simp
          rw [h1]
          have h2 : (ENNReal.ofReal (1 - c) * (G₁.card : ENNReal)).toReal =
              (1 - c) * (G₁.card : ℝ) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ 1 - c by linarith)] <;> simp <;> ring
          rw [h2] <;> ring
        have h_right : (E.card : ENNReal).toReal = (E.card : ℝ) := by simp
        rw [h_left, h_right] at hE_real
        exact hE_real
      have hpiH_size_real : (piH.card : ℝ) ≥ (2 * c) * (G₁.card : ℝ) * (G₂.card : ℝ) := by
        have h_fin2 : (piH.card : ENNReal) ≠ ⊤ := by simp
        have h2 := ENNReal.toReal_mono h_fin2 h_piH_size_enn
        have h_left2 : (ENNReal.ofReal (2 * c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)).toReal =
            (2 * c) * (G₁.card : ℝ) * (G₂.card : ℝ) := by
          have h1 : (ENNReal.ofReal (2 * c) * (G₁.card : ENNReal) * (G₂.card : ENNReal)).toReal =
              (ENNReal.ofReal (2 * c) * (G₁.card : ENNReal)).toReal * (G₂.card : ℝ) := by
            rw [ENNReal.toReal_mul] <;> simp
          rw [h1]
          have h2 : (ENNReal.ofReal (2 * c) * (G₁.card : ENNReal)).toReal =
              (2 * c) * (G₁.card : ℝ) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ 2 * c by linarith)] <;> simp <;> ring
          rw [h2] <;> ring
        have h_right2 : (piH.card : ENNReal).toReal = (piH.card : ℝ) := by simp
        rw [h_left2, h_right2] at h2
        exact h2
      let Q : Finset (Point2 × Point2) := E.filter (fun p => p ∈ piH)
      have hQ_sub_E : Q ⊆ E := filter_subset _ _
      have hQ_sub_prod : Q ⊆ G₁ ×ˢ G₂ := by
        intro p hp; have h : p ∈ E := hQ_sub_E hp; exact hE_sub h
      have hQ_size_real : (Q.card : ℝ) ≥ c * (G₁.card : ℝ) * (G₂.card : ℝ) := by
        let E_neg := E.filter (fun p => p ∉ piH)
        have h1 : (Q.card : ℝ) + (E_neg.card : ℝ) = (E.card : ℝ) := by
          have hQ_eq : Q = E.filter (fun p => p ∈ piH) := by rfl
          have hE_neg_eq : E_neg = E.filter (fun p => p ∉ piH) := by rfl
          rw [hQ_eq, hE_neg_eq]
          have h_disj : Disjoint (E.filter (fun p => p ∈ piH)) (E.filter (fun p => p ∉ piH)) := by
            apply Finset.disjoint_left.mpr
            intro x h1 h2
            have h3 : x ∈ piH := (Finset.mem_filter.mp h1).2
            have h4 : x ∉ piH := (Finset.mem_filter.mp h2).2
            exact h4 h3
          have h_union : (E.filter (fun p => p ∈ piH)) ∪ (E.filter (fun p => p ∉ piH)) = E := by
            ext x
            simp only [Finset.mem_union, Finset.mem_filter]
            <;> tauto
          have h : (E.filter (fun p => p ∈ piH)).card + (E.filter (fun p => p ∉ piH)).card = E.card := by
            rw [←Finset.card_union_of_disjoint h_disj, h_union]
          exact_mod_cast h
        have h2 : E_neg ⊆ (G₁ ×ˢ G₂) \ piH := by
          intro p hp
          have h3 : p ∈ E := (Finset.mem_filter.mp hp).1
          have h4 : p ∉ piH := (Finset.mem_filter.mp hp).2
          have h5 : p ∈ G₁ ×ˢ G₂ := hE_sub h3
          exact Finset.mem_sdiff.mpr ⟨h5, h4⟩
        have h3 : (E_neg.card : ℝ) ≤ ((G₁ ×ˢ G₂) \ piH).card := by
          exact_mod_cast Finset.card_le_card h2
        have h4 : ((G₁ ×ˢ G₂) \ piH).card = (G₁.card : ℝ) * (G₂.card : ℝ) - (piH.card : ℝ) := by
          have h5 : piH ⊆ G₁ ×ˢ G₂ := hpiH_sub
          have h6 : ((G₁ ×ˢ G₂) \ piH).card = (G₁ ×ˢ G₂).card - piH.card :=
            Finset.card_sdiff_of_subset h5
          have h7 : piH.card ≤ (G₁ ×ˢ G₂).card := Finset.card_le_card h5
          have h8 : (((G₁ ×ˢ G₂) \ piH).card : ℝ) = ((G₁ ×ˢ G₂).card : ℝ) - (piH.card : ℝ) := by
            rw [h6, Nat.cast_sub h7]
            <;> rfl
          rw [h8, Finset.card_product] <;> norm_cast <;> ring
        have h5 : (Q.card : ℝ) ≥ (E.card : ℝ) + (piH.card : ℝ) - (G₁.card : ℝ) * (G₂.card : ℝ) := by
          linarith
        have h6 : (E.card : ℝ) + (piH.card : ℝ) - (G₁.card : ℝ) * (G₂.card : ℝ) ≥
            c * (G₁.card : ℝ) * (G₂.card : ℝ) := by
          have h7 : (E.card : ℝ) ≥ (1 - c) * (G₁.card : ℝ) * (G₂.card : ℝ) := hE_size_real
          have h8 : (piH.card : ℝ) ≥ (2 * c) * (G₁.card : ℝ) * (G₂.card : ℝ) := hpiH_size_real
          nlinarith
        linarith
      have hQ_nonempty : Q.Nonempty := by
        have hpos : 0 < c * (G₁.card : ℝ) * (G₂.card : ℝ) := by positivity
        have h : 0 < (Q.card : ℝ) := by linarith
        exact Finset.card_pos.mp (by exact_mod_cast h)
      let fiber : Point2 × Point2 → Finset Point2 := fun p =>
        (H.filter (fun h => h.2.1 = p.1 ∧ h.2.2 = p.2)).image (fun h => h.1)
      have h_fiber_def : ∀ pair : Point2 × Point2,
          fiber pair =
            (H.filter (fun triple =>
              triple.2.1 = pair.1 ∧ triple.2.2 = pair.2)).image
              (fun triple => triple.1) := by
        intro pair
        rfl
      have h_fiber_sub_F : ∀ p ∈ Q, fiber p ⊆ F := by
        intro p _ x hx
        rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
        have h_in_H : t ∈ H := (Finset.mem_filter.mp ht).1
        exact (h_vertex t h_in_H).1
      have h_fiber_size : ∀ p ∈ Q, (fiber p).card ≥ (2 * c) * (F.card : ℝ) := by
        intro p hp
        have h_p_in_piH : p ∈ piH := (Finset.mem_filter.mp hp).2
        exact density_fiber_bound hc h_dense h_p_in_piH
      have h_fiber_nonempty : ∀ p ∈ Q, (fiber p).Nonempty := by
        intro p hp
        have hpos : 0 < (2 * c) * (F.card : ℝ) := by positivity
        have h : 0 < (fiber p).card := by
          have h' := h_fiber_size p hp
          exact_mod_cast (hpos.trans_le h')
        exact Finset.card_pos.mp h
      have hF_lower : (F.card : ℝ) ≥ 1 / (K * δ) :=
        frostman_card_lower_bound hδ hδ0 hK_one hneF hF_frost
      have hδ_neg_γ_le : δ^(-γ) ≤ K * (F.card : ℝ) := by
        have h1 : (F.card : ℝ) ≥ 1 / (K * δ) := hF_lower
        have h2 : K * (F.card : ℝ) ≥ 1 / δ := by
          have h3 : 0 < K * δ := by positivity
          calc K * (F.card : ℝ)
            ≥ K * (1 / (K * δ)) := by gcongr
          _ = 1 / δ := by
            field_simp [h3.ne'] <;> ring
        have h4 : δ^(-γ) ≤ 1 / δ := by
          have h5 : 0 < δ := hδ
          have h6 : δ ≤ δ ^ γ := by
            have h61 : δ ^ (1 : ℝ) ≤ δ ^ γ :=
              Real.rpow_le_rpow_of_exponent_ge' (by linarith) (by linarith) (by linarith) (by linarith)
            have h62 : δ ^ (1 : ℝ) = δ := by simp
            rw [h62] at h61
            exact h61
          have h7 : 0 < δ ^ γ := by positivity
          have h_neg : δ ^ (-γ) = (δ ^ γ)⁻¹ := by
            rw [Real.rpow_neg (by linarith)] <;> ring
          rw [h_neg]
          have h_inv : (δ ^ γ)⁻¹ ≤ δ⁻¹ := by
            gcongr
          simpa [one_div] using h_inv
        linarith
      let E_pair : Point2 × Point2 → ℝ := fun p =>
        ∑ x ∈ fiber p, ∑ y ∈ fiber p,
          (max (dist (inner ℝ x (p.1 - p.2)) (inner ℝ y (p.1 - p.2))) δ)^(-γ)
      have hE_pair_def : ∀ pair : Point2 × Point2,
          E_pair pair =
            ∑ x ∈ fiber pair, ∑ y ∈ fiber pair,
              (max
                (dist (inner ℝ x (pair.1 - pair.2))
                  (inner ℝ y (pair.1 - pair.2))) δ)^(-γ) := by
        intro pair
        rfl
      have hE_rewrite : ∀ p ∈ Q, E_pair p =
          ∑ x ∈ fiber p, ∑ y ∈ fiber p,
            (max (|inner ℝ (x - y) (p.1 - p.2)|) δ)^(-γ) := by
        intro p _
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        have h : dist (inner ℝ x (p.1 - p.2)) (inner ℝ y (p.1 - p.2)) =
            |inner ℝ (x - y) (p.1 - p.2)| := by
          have h5 : inner ℝ x (p.1 - p.2) - inner ℝ y (p.1 - p.2) =
              inner ℝ (x - y) (p.1 - p.2) := by rw [inner_sub_left]
          simp [dist_eq_norm, Real.norm_eq_abs, h5]
        rw [h]
      have h_total_energy : ∑ p ∈ Q, E_pair p ≤
          C_total * K^2 * (G₁.card : ℝ) * (G₂.card : ℝ) * (F.card : ℝ)^2 := by
        try { clear piH hpiH_sub h_piH_size_enn hE_size_real hpiH_size_real }
        try { clear hQ_size_real hQ_nonempty h_fiber_size h_fiber_nonempty hF_lower }
        try { clear h_vertex h_dense hc hc_pos h_c0 }
        try { clear hneG1 hneG2 hG1_sep hG2_sep hG1_frost hG2_frost h_std }
        try { clear hβ hK' hc_range hE_mass h_thin hQ_sub_E }
        try { clear hneF hF_ball hG1_ball hG2_ball }
        try { clear hC_ang_pos hC_total_pos hC_total_ge_one h2_pow_ge_one hA_ge_one }
        let g : Point2 → Point2 → Point2 × Point2 → ℝ := fun x y p =>
          (max (|inner ℝ (x - y) (p.1 - p.2)|) δ)^(-γ)
        let Q_xy : Point2 → Point2 → Finset (Point2 × Point2) := fun x y =>
          Q.filter (fun p => x ∈ fiber p ∧ y ∈ fiber p)
        have h_factor_combined : ∀ (d : ℝ), 0 < d → ∀ (a : ℝ), 0 ≤ a →
            (max (d * a) δ)^(-γ) ≤ (1 + d^(-γ)) * (max a δ)^(-γ) := by
          intro d hd a ha
          by_cases h_d_le_one : d ≤ 1
          · -- d ≤ 1
            have h1 : max (d * a) δ ≥ d * max a δ := by
              by_cases h : a ≥ δ
              · have h2 : max a δ = a := by rw [max_eq_left] <;> linarith
                have h_goal : d * max a δ ≤ max (d * a) δ := by
                  rw [h2]
                  exact le_max_left _ _
                exact h_goal
              · have h2 : a < δ := by linarith
                have h3 : max a δ = δ := by rw [max_eq_right] <;> linarith
                have h4 : d * δ ≤ δ := by nlinarith
                have h5 : d * max a δ = d * δ := by rw [h3]
                have h6 : d * δ ≤ max (d * a) δ := h4.trans (le_max_right _ _)
                rw [h5]
                exact h6
            have h_pos2 : 0 < d * max a δ := by positivity
            have h5 : (d * max a δ)^γ ≤ (max (d * a) δ)^γ := Real.rpow_le_rpow (by positivity) h1 (by linarith)
            have h_rpow : (max (d * a) δ)^(-γ) ≤ (d * max a δ)^(-γ) := by
              have h6 : (max (d * a) δ)^(-γ) = ((max (d * a) δ)^γ)⁻¹ := by
                rw [Real.rpow_neg (by positivity)] <;> ring
              have h7 : (d * max a δ)^(-γ) = ((d * max a δ)^γ)⁻¹ := by
                rw [Real.rpow_neg (by positivity)] <;> ring
              rw [h6, h7]
              have h_pos3 : 0 < (max (d * a) δ)^γ := by positivity
              have h_pos2_pow : 0 < (d * max a δ)^γ := by positivity
              simpa [one_div] using one_div_le_one_div_of_le h_pos2_pow h5
            have h_mul : (d * max a δ)^(-γ) = d^(-γ) * (max a δ)^(-γ) := by
              rw [Real.mul_rpow (by positivity) (by positivity)] <;> ring
            rw [h_mul] at h_rpow
            have h_nonneg : 0 ≤ (max a δ)^(-γ) := by positivity
            have h8 : d^(-γ) * (max a δ)^(-γ) ≤ (1 + d^(-γ)) * (max a δ)^(-γ) := by
              have h9 : d^(-γ) ≤ 1 + d^(-γ) := by linarith
              exact mul_le_mul_of_nonneg_right h9 h_nonneg
            exact h_rpow.trans h8
          · -- d > 1
            have h_d_gt_one : 1 < d := by linarith
            have h1 : max a δ ≤ max (d * a) δ := by
              have h2 : a ≤ d * a := by nlinarith
              exact max_le_max h2 (by linarith)
            have h_pos1_pow : 0 < (max a δ)^γ := by positivity
            have h4 : (max a δ)^γ ≤ (max (d * a) δ)^γ := Real.rpow_le_rpow (by positivity) h1 (by linarith)
            have h3 : (max (d * a) δ)^(-γ) ≤ (max a δ)^(-γ) := by
              have h5 : (max (d * a) δ)^(-γ) = ((max (d * a) δ)^γ)⁻¹ := by
                rw [Real.rpow_neg (by positivity)] <;> ring
              have h6 : (max a δ)^(-γ) = ((max a δ)^γ)⁻¹ := by
                rw [Real.rpow_neg (by positivity)] <;> ring
              rw [h5, h6]
              have h_pos3 : 0 < (max (d * a) δ)^γ := by positivity
              simpa [one_div] using one_div_le_one_div_of_le h_pos1_pow h4
            have h_nonneg : 0 ≤ (max a δ)^(-γ) := by positivity
            have h7 : (max a δ)^(-γ) ≤ (1 + d^(-γ)) * (max a δ)^(-γ) := by
              have h8 : 0 ≤ d^(-γ) := by positivity
              have h9 : (max a δ)^(-γ) ≤ (max a δ)^(-γ) + d^(-γ) * (max a δ)^(-γ) := by
                apply le_add_of_nonneg_right; positivity
              have h10 : (max a δ)^(-γ) + d^(-γ) * (max a δ)^(-γ) = (1 + d^(-γ)) * (max a δ)^(-γ) := by ring
              rw [h10] at h9
              exact h9
            exact h3.trans h7
        have h_reg_energy : ∑ x ∈ F, ∑ y ∈ F, (max (dist x y) δ)^(-γ) ≤
            (1 + 2 * K_frost0) * K * (F.card : ℝ)^2 := by
          have hFrost_energy : ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) ≤
              K_frost0 * (1 + K) * (F.card : ℝ)^2 := by
            have h := frostman_energy_bound hδ hδ0 (by norm_num) hγ_pos hγ_lt_one (show 0 ≤ K from by linarith) hF_frost hF_sep hF_ball
            have h_eq : ((2 : ℝ)^(1 : ℝ) / ((2 : ℝ)^((1 : ℝ)-γ) - 1) + 3 * (2 : ℝ)^γ) * (1 + K) * (F.card : ℝ)^2 =
                K_frost0 * (1 + K) * (F.card : ℝ)^2 := by
              congr 1 <;> simp [K_frost0, kaufman_K_frost0] <;> ring
            rw [h_eq] at h; exact h
          let S_diag : Finset (Point2 × Point2) := (F ×ˢ F).filter (fun p => p.1 = p.2)
          let S_off : Finset (Point2 × Point2) := (F ×ˢ F).filter (fun p => p.1 ≠ p.2)
          have h_part : (F ×ˢ F) = S_diag ∪ S_off := by
            ext ⟨x, y⟩; simp [S_diag, S_off] <;> by_cases h : x = y <;> simp [h] <;> tauto
          have h_disj : Disjoint S_diag S_off := by
            simp [S_diag, S_off, Finset.disjoint_left] <;> tauto
          have h_diag_eq : S_diag = F.image (fun x => (x, x)) := by
            ext ⟨x, y⟩
            simp only [S_diag, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
            constructor
            · rintro ⟨⟨hx, _⟩, rfl⟩
              exact ⟨x, hx, by simp⟩
            · rintro ⟨z, hz, h⟩
              have hz' : z = x ∧ z = y := by simpa [Prod.ext_iff] using h
              exact ⟨⟨hz'.1 ▸ hz, hz'.2 ▸ hz⟩, hz'.1.symm.trans hz'.2⟩
          have h_off_term : ∀ p ∈ S_off, (max (dist p.1 p.2) δ)^(-γ) = (dist p.1 p.2)^(-γ) := by
            intro p hp
            have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
            have h1 : p.1 ∈ F := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
            have h2 : p.2 ∈ F := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
            have h_sep : δ ≤ dist p.1 p.2 := hF_sep h1 h2 hne
            have h_max : max (dist p.1 p.2) δ = dist p.1 p.2 := by rw [max_eq_left] <;> linarith
            exact congr_arg (fun x : ℝ => x^(-γ)) h_max
          have h_diag_term : ∀ p ∈ S_diag, (max (dist p.1 p.2) δ)^(-γ) = δ^(-γ) := by
            intro p hp
            have h_eq : p.1 = p.2 := (Finset.mem_filter.mp hp).2
            have h_dist : dist p.1 p.2 = 0 := by rw [h_eq] <;> simp
            have h_max : max (dist p.1 p.2) δ = δ := by
              rw [h_dist]
              have h_nonneg : (0 : ℝ) ≤ δ := by linarith
              exact max_eq_right h_nonneg
            exact congr_arg (fun x : ℝ => x^(-γ)) h_max
          have h_sum1 : ∑ p ∈ F ×ˢ F, (max (dist p.1 p.2) δ)^(-γ) =
              ∑ p ∈ S_diag, (max (dist p.1 p.2) δ)^(-γ) + ∑ p ∈ S_off, (max (dist p.1 p.2) δ)^(-γ) := by
            rw [h_part, Finset.sum_union h_disj]
          have h_diag_sum2 : ∑ p ∈ S_diag, (max (dist p.1 p.2) δ)^(-γ) = (F.card : ℝ) * δ^(-γ) := by
            have h1 : ∑ p ∈ S_diag, (max (dist p.1 p.2) δ)^(-γ) = ∑ p ∈ S_diag, δ^(-γ) := by
              apply Finset.sum_congr rfl
              intro p hp
              exact h_diag_term p hp
            rw [h1, h_diag_eq]
            have h_inj : Set.InjOn (fun x : Point2 => (x, x)) (F : Set Point2) := by
              intro x _ y _ h; simpa using h
            rw [Finset.sum_image h_inj, Finset.sum_const] <;> ring
          have h_off_sum2 : ∑ p ∈ S_off, (max (dist p.1 p.2) δ)^(-γ) ≤ ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) := by
            have h1 : ∑ p ∈ S_off, (max (dist p.1 p.2) δ)^(-γ) = ∑ p ∈ S_off, (dist p.1 p.2)^(-γ) := by
              apply Finset.sum_congr rfl; intro p hp; exact h_off_term p hp
            rw [h1]
            have h2 : ∑ x ∈ F, ∑ y ∈ F, (dist x y)^(-γ) = ∑ p ∈ F ×ˢ F, (dist p.1 p.2)^(-γ) := by
              rw [Finset.sum_product] <;> rfl
            rw [h2]
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro p _ _; positivity
          have h_main : ∑ p ∈ F ×ˢ F, (max (dist p.1 p.2) δ)^(-γ) ≤
              (F.card : ℝ) * δ^(-γ) + K_frost0 * (1 + K) * (F.card : ℝ)^2 := by
            rw [h_sum1, h_diag_sum2]; linarith [h_off_sum2, hFrost_energy]
          have h_final : (F.card : ℝ) * δ^(-γ) + K_frost0 * (1 + K) * (F.card : ℝ)^2 ≤
              (1 + 2 * K_frost0) * K * (F.card : ℝ)^2 := by
            have h21 : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
            have h2 : (F.card : ℝ) * δ^(-γ) ≤ K * (F.card : ℝ)^2 := by
              calc (F.card : ℝ) * δ^(-γ)
                ≤ (F.card : ℝ) * (K * (F.card : ℝ)) := mul_le_mul_of_nonneg_left hδ_neg_γ_le h21
              _ = K * (F.card : ℝ)^2 := by ring
            have h31 : 0 ≤ K_frost0 := hK_frost0_pos.le
            have h32 : 0 ≤ (F.card : ℝ)^2 := sq_nonneg _
            have h33 : 1 + K ≤ 2 * K := by linarith [hK_one]
            have h34 : K_frost0 * (1 + K) ≤ K_frost0 * (2 * K) := mul_le_mul_of_nonneg_left h33 h31
            have h3 : K_frost0 * (1 + K) * (F.card : ℝ)^2 ≤ 2 * K * K_frost0 * (F.card : ℝ)^2 := by
              have h35 : K_frost0 * (1 + K) * (F.card : ℝ)^2 ≤ K_frost0 * (2 * K) * (F.card : ℝ)^2 :=
                mul_le_mul_of_nonneg_right h34 h32
              have h36 : K_frost0 * (2 * K) * (F.card : ℝ)^2 = 2 * K * K_frost0 * (F.card : ℝ)^2 := by ring
              rw [h36] at h35
              exact h35
            calc
              (F.card : ℝ) * δ^(-γ) + K_frost0 * (1 + K) * (F.card : ℝ)^2
                ≤ K * (F.card : ℝ)^2 + 2 * K * K_frost0 * (F.card : ℝ)^2 := add_le_add h2 h3
              _ = (1 + 2 * K_frost0) * K * (F.card : ℝ)^2 := by ring
          have h5 : ∑ x ∈ F, ∑ y ∈ F, (max (dist x y) δ)^(-γ) = ∑ p ∈ F ×ˢ F, (max (dist p.1 p.2) δ)^(-γ) := by
            rw [Finset.sum_product] <;> rfl
          rw [h5]; exact h_main.trans h_final
        have h_extend : ∀ (p : Point2 × Point2), p ∈ Q →
            (∑ x ∈ fiber p, ∑ y ∈ fiber p, g x y p) =
            ∑ x ∈ F, ∑ y ∈ F, (if x ∈ fiber p ∧ y ∈ fiber p then g x y p else 0) := by
          intro p hp
          have h_sub : fiber p ⊆ F := h_fiber_sub_F p hp
          exact sum_extend_subset h_sub
        have h_interchange : ∑ p ∈ Q, E_pair p =
            ∑ x ∈ F, ∑ y ∈ F, ∑ p ∈ Q_xy x y, g x y p := by
          have h1 : ∑ p ∈ Q, E_pair p =
              ∑ p ∈ Q, ∑ x ∈ F, ∑ y ∈ F, (if x ∈ fiber p ∧ y ∈ fiber p then g x y p else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hE : E_pair p = ∑ x ∈ fiber p, ∑ y ∈ fiber p, g x y p := by
              rw [hE_rewrite p hp] <;> rfl
            rw [hE]; exact h_extend p hp
          rw [h1]
          have h_comm : ∑ p ∈ Q, ∑ x ∈ F, ∑ y ∈ F, (if x ∈ fiber p ∧ y ∈ fiber p then g x y p else 0) =
              ∑ x ∈ F, ∑ y ∈ F, ∑ p ∈ Q, (if x ∈ fiber p ∧ y ∈ fiber p then g x y p else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_comm]
          rw [h_comm]
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          have h3 : ∑ p ∈ Q, (if x ∈ fiber p ∧ y ∈ fiber p then g x y p else 0) =
              ∑ p ∈ Q_xy x y, g x y p := by
            rw [←Finset.sum_filter] <;> rfl
          exact h3
        have h_thin_unnorm : ∀ (b₁ : Point2), b₁ ∈ G₁ →
            ∀ (ℓ : AffineSubspace ℝ Point2), b₁ ∈ (ℓ : Set Point2) →
            Module.finrank ℝ ℓ.direction = 1 →
            ∀ (r : ℝ), δ ≤ r → r ≤ 1 →
              ((G₂.filter (fun b₂ => b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E)).card : ENNReal) ≤
              ENNReal.ofReal (K * r) * (G₂.card : ENNReal) := by
          intro b1 hb1 ℓ hb1inℓ hfin r hrδ _
          have h := h_thin b1 hb1 ℓ hb1inℓ hfin r hrδ
          have h5 : (K * r ^ (1 : ℝ)) = K * r := by
            have h6 : r ^ (1 : ℝ) = r := by simp
            rw [h6] <;> ring
          rw [h5] at h; exact h
        let C_ang_unnorm : ℝ := 2 + 8 * (4 : ℝ)^(1-γ) / ((2 : ℝ)^(1-γ) - 1)
        have hC_ang_unnorm_nonneg : 0 ≤ C_ang_unnorm := by
          dsimp only [C_ang_unnorm]
          positivity
        have h_ang_sum : ∀ (b₁ : Point2), b₁ ∈ G₁ → ∀ (v : Point2), ‖v‖ = 1 →
            ∑ b₂ ∈ (G₂.filter (fun b₂ => (b₁, b₂) ∈ E)),
              (max (|inner ℝ v (b₁ - b₂)|) δ)^(-γ) ≤
            C_ang_unnorm * K * (G₂.card : ℝ) := by
          intro b1 hb1 v hv
          have h_abs_eq : ∀ b₂ : Point2, |inner ℝ (b₂ - b1) v| = |inner ℝ v (b1 - b₂)| := by
            intro b2
            have h1 : inner ℝ (b2 - b1) v = inner ℝ v (b2 - b1) :=
              real_inner_comm v (b2 - b1)
            have h2 : inner ℝ v (b2 - b1) = -inner ℝ v (b1 - b2) := by
              have h21 : b2 - b1 = -(b1 - b2) := by abel
              rw [h21, inner_neg_right]
            rw [h1, h2, abs_neg]
          have h := thin_tubes_angular_sum_unnormalized hδ hδ0 hK_one hγ_pos hγ_lt_one b1 v hv E hE_sub h_thin_unnorm hG1_ball hG2_ball hb1
          have h' : ∑ b₂ ∈ (G₂.filter (fun b₂ => (b1, b₂) ∈ E)),
                (max (|inner ℝ (b₂ - b1) v|) δ)^(-γ) =
              ∑ b₂ ∈ (G₂.filter (fun b₂ => (b1, b₂) ∈ E)),
                (max (|inner ℝ v (b1 - b₂)|) δ)^(-γ) := by
            apply Finset.sum_congr rfl
            intro b2 _
            rw [h_abs_eq b2]
          rw [h'] at h; exact h
        have h_decompose : ∀ (v : Point2), ‖v‖ = 1 →
            ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) ≤
            (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ) := by
          intro v hv
          have h1 : ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) =
              ∑ b1 ∈ G₁, ∑ b2 ∈ (G₂.filter (fun b2 => (b1, b2) ∈ E)),
                (max (|inner ℝ v (b1 - b2)|) δ)^(-γ) := by
            have h2 : ∑ p ∈ G₁ ×ˢ G₂, (if p ∈ E then (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) else 0) =
                ∑ p ∈ E, (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) := by
              have h_filter : (G₁ ×ˢ G₂).filter (fun p => p ∈ E) = E := by
                ext x; simp [Finset.mem_filter, hE_sub] <;> tauto
              rw [←Finset.sum_filter, h_filter]
            have h3 : ∑ p ∈ G₁ ×ˢ G₂, (if p ∈ E then (max (|inner ℝ v (p.1 - p.2)|) δ)^(-γ) else 0) =
                ∑ b1 ∈ G₁, ∑ b2 ∈ G₂, (if (b1, b2) ∈ E then (max (|inner ℝ v (b1 - b2)|) δ)^(-γ) else 0) := by
              rw [Finset.sum_product] <;> rfl
            rw [←h2, h3]
            apply Finset.sum_congr rfl
            intro b1 _
            have h4 : ∑ b2 ∈ G₂, (if (b1, b2) ∈ E then (max (|inner ℝ v (b1 - b2)|) δ)^(-γ) else 0) =
                ∑ b2 ∈ (G₂.filter (fun b2 => (b1, b2) ∈ E)), (max (|inner ℝ v (b1 - b2)|) δ)^(-γ) := by
              rw [←Finset.sum_filter] <;> rfl
            exact h4
          rw [h1]
          have h5 : ∑ b1 ∈ G₁, ∑ b2 ∈ (G₂.filter (fun b2 => (b1, b2) ∈ E)),
                (max (|inner ℝ v (b1 - b2)|) δ)^(-γ) ≤
              ∑ b1 ∈ G₁, (C_ang_unnorm * K * (G₂.card : ℝ)) := by
            apply Finset.sum_le_sum
            intro b1 hb1
            exact h_ang_sum b1 hb1 v hv
          have h6 : ∑ b1 ∈ G₁, (C_ang_unnorm * K * (G₂.card : ℝ)) =
              (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ) := by
            rw [Finset.sum_const] <;> ring
          exact le_trans h5 (by rw [h6])
        try { clear h_ang_sum hE_sub h_thin_unnorm }
        have h_off_diag_point : ∀ (x y : Point2), x ≠ y →
            ∑ p ∈ Q_xy x y, g x y p ≤
            (1 + ‖x - y‖^(-γ)) * (G₁.card : ℝ) * C_ang_unnorm * K * (G₂.card : ℝ) := by
          intro x y hne
          exact wz1_off_diagonal_point_energy
            (G₁ := G₁) (G₂ := G₂) (E := E)
            hδ Q_xy g (fun _ _ _ => rfl)
            (fun first second point hpoint =>
              hQ_sub_E (Finset.mem_filter.mp hpoint).1)
            h_factor_combined h_decompose x y hne
        have h_diag_sum : ∑ x ∈ F, ∑ p ∈ Q_xy x x, g x x p ≤
            K * (F.card : ℝ)^2 * (G₁.card : ℝ) * (G₂.card : ℝ) := by
          exact wz1_diagonal_energy_bound
            (Q := Q) Q_xy g hδ
            (by
              intro x hx p hp
              simp [g, max_eq_right hδ.le])
            (fun x => Finset.filter_subset _ _)
            hQ_sub_prod hδ_neg_γ_le
        have h_off_total : ∑ x ∈ F, ∑ y ∈ F, (if x ≠ y then ∑ p ∈ Q_xy x y, g x y p else 0) ≤
            C_ang_unnorm * K * (G₁.card : ℝ) * (G₂.card : ℝ) *
              ((F.card : ℝ)^2 + (1 + 2 * K_frost0) * K * (F.card : ℝ)^2) := by
          exact wz1_off_diagonal_total_energy
            Q_xy g hF_sep hC_ang_unnorm_nonneg
            (by linarith) h_reg_energy h_off_diag_point
        have h_split : ∑ x ∈ F, ∑ y ∈ F, ∑ p ∈ Q_xy x y, g x y p =
            (∑ x ∈ F, ∑ p ∈ Q_xy x x, g x x p) +
            ∑ x ∈ F, ∑ y ∈ F, (if x ≠ y then ∑ p ∈ Q_xy x y, g x y p else 0) :=
          wz1_sum_split_diagonal F
            (fun x y => ∑ p ∈ Q_xy x y, g x y p)
        have hC_total_def2 : C_total = 1 + C_ang_unnorm * (2 + 2 * K_frost0) := by
          dsimp only [C_total, totalEnergyConst] <;> ring
        exact wz1_combine_split_energy
          hK_one hK_frost0_pos hC_ang_unnorm_nonneg hC_total_def2
          h_interchange h_split h_diag_sum h_off_total
      have hQ_pos : 0 < (Q.card : ℝ) := by exact_mod_cast hQ_nonempty.card_pos
      let E_avg : ℝ := (∑ p ∈ Q, E_pair p) / (Q.card : ℝ)
      have hE_avg_def : E_avg = (∑ p ∈ Q, E_pair p) / (Q.card : ℝ) := by rfl
      have hE_avg_bound : E_avg ≤
          C_total * K^2 * (F.card : ℝ)^2 / c := by
        have hG1_pos : 0 < (G₁.card : ℝ) := by exact_mod_cast hneG1.card_pos
        have hG2_pos : 0 < (G₂.card : ℝ) := by exact_mod_cast hneG2.card_pos
        rw [hE_avg_def]
        exact wz1_average_energy_bound
          hQ_pos hc_pos hG1_pos hG2_pos
          (mul_nonneg hC_total_pos.le (sq_nonneg K))
          (sq_nonneg (F.card : ℝ))
          hQ_size_real h_total_energy
      have h_markov : ∃ p ∈ Q, E_pair p ≤ 2 * E_avg := by
        have henergy_nonneg : ∀ point ∈ Q, 0 ≤ E_pair point := by
          intro point hpoint
          dsimp only [E_pair]
          exact wz1_projection_energy_nonneg
            (fiber point) (point.1 - point.2) hδ
        obtain ⟨point, hpoint, hpoint_energy⟩ :=
          wz1_exists_le_twice_average Q E_pair hQ_nonempty henergy_nonneg
        refine ⟨point, hpoint, ?_⟩
        rw [hE_avg_def]
        exact hpoint_energy
      rcases h_markov with ⟨p, hp_in_Q, hE_good⟩
      have h_fiber_size_p : (fiber p).card ≥ (2 * c) * (F.card : ℝ) :=
        h_fiber_size p hp_in_Q
      have h_fiber_nonempty_p : (fiber p).Nonempty := h_fiber_nonempty p hp_in_Q
      set E_bound : ℝ :=
        2 * (C_total * K^2 * (F.card : ℝ)^2 / c) with hE_bound_def
      have hE_bound_pos : 0 ≤ E_bound := by
        rw [hE_bound_def]
        exact mul_nonneg (by norm_num)
          (div_nonneg
            (mul_nonneg
              (mul_nonneg hC_total_pos.le (sq_nonneg K))
              (sq_nonneg (F.card : ℝ)))
            hc_pos.le)
      have hE_good2 : E_pair p ≤ E_bound := by
        rw [hE_bound_def]
        exact wz1_le_twice_of_le_twice_of_le hE_good hE_avg_bound
      have h_image_sub :
          (fun x : Point2 => inner ℝ x (p.1 - p.2)) ''
              (fiber p : Set Point2) ⊆
            wz1DotDifferenceSet H := by
        rw [h_fiber_def p]
        exact wz1_projected_fiber_dot_image_subset H p
      have h_f_energy : ∑ x ∈ fiber p, ∑ y ∈ fiber p,
          (max
            (dist (inner ℝ x (p.1 - p.2))
              (inner ℝ y (p.1 - p.2))) δ)^(-γ) ≤ E_bound := by
        rw [← hE_pair_def p]
        exact hE_good2
      have h_covering : Metric.externalCoveringNumber (Real.toNNReal δ)
          ((fun x : Point2 => inner ℝ x (p.1 - p.2)) ''
            (fiber p : Set Point2)) ≥
          ENNReal.ofReal (((fiber p).card : ℝ)^2 / (E_bound * (2 * δ)^γ)) :=
        projected_energy_to_covering
          (A := fiber p)
          (f := fun x : Point2 => inner ℝ x (p.1 - p.2))
          (δ := δ) (γ := γ) (E := E_bound)
          hδ hγ_pos hE_bound_pos h_f_energy
      have h_covering2 : Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H) ≥
          Metric.externalCoveringNumber (Real.toNNReal δ)
            ((fun x : Point2 => inner ℝ x (p.1 - p.2)) ''
              (fiber p : Set Point2)) :=
        Metric.externalCoveringNumber_mono_set h_image_sub
      have h_final1 : ((fiber p).card : ℝ)^2 / (E_bound * (2 * δ)^γ) ≥
          (c ^ 5 / (A * K ^ 2)) * Real.rpow δ (ε - 1) := by
        have h5 : Real.rpow δ (ε - 1) = δ^(-γ) := by
          have h6 : ε - 1 = -γ := by linarith
          rw [h6] <;> rfl
        rw [h5]
        have h1 : ((fiber p).card : ℝ) ≥ (2 * c) * (F.card : ℝ) := h_fiber_size_p
        have h2 : 0 < (F.card : ℝ) := by exact_mod_cast hneF.card_pos
        have h3 : 0 < c := hc_pos
        have h4 : 0 < K := by linarith
        have h9 : c ≤ 1 := by linarith
        have h13 : A = C_total * (2 : ℝ)^γ := by simp [hA_def]
        have hE_bound_def' :
            E_bound = 2 * C_total * K^2 * (F.card : ℝ)^2 / c := by
          rw [hE_bound_def]
          ring
        exact wz1_final_algebra c C_total K (F.card : ℝ) δ γ A E_bound
          ((fiber p).card : ℝ) h3 h9 hC_total_pos h4 h2 hδ hγ_pos hγ_lt_one
          h13 hE_bound_def' h1
      have h_main : Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H) ≥
          ENNReal.ofReal ((c ^ 5 / (A * K ^ 2)) * Real.rpow δ (ε - 1)) := by
        have h_trans : (Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H) : ENNReal) ≥
            ENNReal.ofReal (((fiber p).card : ℝ)^2 / (E_bound * (2 * δ)^γ)) := by
          calc
            (Metric.externalCoveringNumber (Real.toNNReal δ) (wz1DotDifferenceSet H) : ENNReal)
              ≥ (Metric.externalCoveringNumber (Real.toNNReal δ)
                  ((fun x : Point2 => inner ℝ x (p.1 - p.2)) ''
                    (fiber p : Set Point2)) : ENNReal) := by
                exact_mod_cast h_covering2
            _ ≥ ENNReal.ofReal (((fiber p).card : ℝ)^2 / (E_bound * (2 * δ)^γ)) := h_covering
        exact le_trans (ENNReal.ofReal_le_ofReal h_final1) h_trans
      exact h_main

theorem wz1_thin_tubes_large_dot_product :
    WZ1ThinTubesLargeDotProductStatement := by
  intro ε hε
  change WZ1ThinTubesLargeDotProductAt ε
  by_cases h_eps : 1 ≤ ε
  · exact wz1_thin_tubes_large_dot_product_at_of_one_le ε h_eps
  · exact wz1_thin_tubes_large_dot_product_at_of_lt_one ε hε (lt_of_not_ge h_eps)

end Kakeya.Assouad
