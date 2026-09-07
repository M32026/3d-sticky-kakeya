import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ExternalCoveringNumberIsometry

/-!
# Transport and normalize AD

Transport scalar-projection AD through the anchored unit rescaling, normalize
the transported normal, and weaken the AD base scale to `rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

lemma externalCoveringNumber_dilation_eq {a : ℝ} (ha : 0 < a)
    {ε : NNReal} {A : Set ℝ} :
    externalCoveringNumber ⟨a * ε, by positivity⟩ ((fun x => a * x) '' A) =
    externalCoveringNumber ε A := by
  let f : ℝ → ℝ := fun x => a * x
  let g : ℝ → ℝ := fun y => y / a
  have h_a_nn : 0 ≤ a := by linarith
  have h_inv_nn : 0 ≤ 1 / a := by positivity
  have hf_lip : LipschitzWith (Real.toNNReal a) f := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have h : |a * x - a * y| = a * |x - y| := by
      have h1 : a * x - a * y = a * (x - y) := by ring
      rw [h1, abs_mul, abs_of_pos ha]
    simpa [f, dist_eq_norm] using le_of_eq h
  have hg_lip : LipschitzWith (Real.toNNReal (1 / a)) g := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have h : |x / a - y / a| = (1 / a) * |x - y| := by
      have h1 : x / a - y / a = (1 / a) * (x - y) := by ring
      rw [h1, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / a by positivity)]
    simpa [g, dist_eq_norm] using le_of_eq h
  have hgf : ∀ x, g (f x) = x := by
    intro x
    have h : g (f x) = (a * x) / a := by simp [f, g]
    rw [h]
    field_simp [ha.ne']
  have h_coe_a : (Real.toNNReal a : ℝ) = a := by
    have h3 : (Real.toNNReal a : ℝ) = max a 0 := by simp [Real.toNNReal]
    rw [h3, max_eq_left h_a_nn]
  have h_coe_inv : (Real.toNNReal (1 / a) : ℝ) = 1 / a := by
    have h3 : (Real.toNNReal (1 / a) : ℝ) = max (1 / a) 0 := by
      simp [Real.toNNReal]
    rw [h3, max_eq_left h_inv_nn]
  have h_radius1 : Real.toNNReal a * ε = ⟨a * ε, by positivity⟩ := by
    have h_main : ((Real.toNNReal a * ε : NNReal) : ℝ) =
        a * (ε : ℝ) := by
      rw [NNReal.coe_mul, h_coe_a]
    let target : NNReal := ⟨a * ε, by positivity⟩
    have h4 : (target : ℝ) = a * ε := Subtype.coe_mk (a * ε) (by positivity)
    have h5 : ((Real.toNNReal a * ε : NNReal) : ℝ) = (target : ℝ) := by
      rw [h_main, h4]
    exact NNReal.coe_injective h5
  have h_radius2 :
      Real.toNNReal (1 / a) * ⟨a * ε, by positivity⟩ = ε := by
    let target : NNReal := ⟨a * ε, by positivity⟩
    have h4 : (target : ℝ) = a * ε := Subtype.coe_mk (a * ε) (by positivity)
    have h_main :
        ((Real.toNNReal (1 / a) * target : NNReal) : ℝ) = (ε : ℝ) := by
      rw [NNReal.coe_mul, h_coe_inv, h4]
      field_simp [ha.ne']
    exact NNReal.coe_injective h_main
  have h1 : externalCoveringNumber ⟨a * ε, by positivity⟩ (f '' A) ≤
      externalCoveringNumber ε A := by
    simp only [externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hcover : IsCover (Real.toNNReal a * ε) (f '' A) (f '' C) :=
      hC.image_lipschitz hf_lip
    rw [h_radius1] at hcover
    exact iInf_le_of_le (f '' C)
      (iInf_le_of_le hcover (encard_image_le f C))
  have h2 : externalCoveringNumber ε A ≤
      externalCoveringNumber ⟨a * ε, by positivity⟩ (f '' A) := by
    simp only [externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hcover :
        IsCover
          (Real.toNNReal (1 / a) * ⟨a * ε, by positivity⟩)
          (g '' (f '' A)) (g '' C) :=
      hC.image_lipschitz hg_lip
    rw [h_radius2] at hcover
    have h_image : g '' (f '' A) = A := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨x, hx, rfl⟩
        have h4 : g (f x) = x := hgf x
        rw [h4]
        exact hx
      · intro hy
        refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
        exact hgf y
    rw [h_image] at hcover
    exact iInf_le_of_le (g '' C)
      (iInf_le_of_le hcover (encard_image_le g C))
  exact le_antisymm h1 h2

private lemma dilation_inter_closedBall
    {a : ℝ} (ha : 0 < a) {S : Set ℝ} {x r : ℝ} :
    (fun u : ℝ => a * u) '' (S ∩ Metric.closedBall x r) =
    ((fun u : ℝ => a * u) '' S) ∩ Metric.closedBall (a * x) (a * r) := by
  have h_inj : Function.Injective (fun u : ℝ => a * u) := by
    intro u v h
    apply mul_left_cancel₀ ha.ne'
    exact h
  rw [Set.image_inter h_inj]
  have h2 :
      (fun u : ℝ => a * u) '' Metric.closedBall x r =
        Metric.closedBall (a * x) (a * r) := by
    ext y
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h3 : dist z x ≤ r := hz
      have h4 : dist (a * z) (a * x) ≤ a * r := by
        have h5 : dist (a * z) (a * x) = a * dist z x := by
          calc
            dist (a * z) (a * x) = |a * z - a * x| := by
              simp [dist_eq_norm, Real.norm_eq_abs]
            _ = |a * (z - x)| := by
              rw [show a * z - a * x = a * (z - x) by ring]
            _ = a * |z - x| := by rw [abs_mul, abs_of_pos ha]
            _ = a * dist z x := by
              simp [dist_eq_norm, Real.norm_eq_abs]
        rw [h5]
        gcongr
      exact h4
    · intro hz
      have h_goal1 : dist (y / a) x ≤ r := by
        have h4 : dist (y / a) x = dist y (a * x) / a := by
          calc
            dist (y / a) x = |y / a - x| := by
              simp [dist_eq_norm, Real.norm_eq_abs]
            _ = |(y - a * x) / a| := by
              have h_eq : y / a - x = (y - a * x) / a := by
                field_simp [ha.ne']
              rw [h_eq]
            _ = |y - a * x| / a := by rw [abs_div, abs_of_pos ha]
            _ = dist y (a * x) / a := by
              have h_dist : dist y (a * x) = |y - a * x| := by
                simp [dist_eq_norm, Real.norm_eq_abs]
              rw [h_dist]
        rw [h4]
        have h5 : dist y (a * x) ≤ a * r := hz
        calc
          dist y (a * x) / a ≤ (a * r) / a := by gcongr
          _ = r := by field_simp [ha.ne']
      have h_goal2 : a * (y / a) = y := by
        field_simp [ha.ne']
      exact ⟨y / a, h_goal1, h_goal2⟩
  rw [h2]

/-- AD is preserved under dilation by `a ≥ 1`, with base scale scaled by `a`. -/
lemma IsADSet1.dilation_ge_one
    {E : Set ℝ} {δ α : ℝ} {C : ENNReal} {a : ℝ}
    (ha : 1 ≤ a)
    (hE : IsADSet1 E δ α C)
    (hbound : (fun x : ℝ => a * x) '' E ⊆ Set.Icc (-4 : ℝ) 4)
    (hδ_a : a * δ ≤ 1)
    (hδ_pos : 0 < δ) (hα_pos : 0 < α) (hα_one : α ≤ 1)
    (hC : 1 ≤ C) :
    IsADSet1 ((fun x : ℝ => a * x) '' E) (a * δ) α C := by
  rcases hE with ⟨_, _, _, _, _, hcover⟩
  have ha_pos : 0 < a := by linarith
  refine ⟨by positivity, hα_pos, hα_one, hC, hbound, ?_⟩
  intro rho' hrho' hdelta'_rho hrho'_one x' r' hrho'_r hr'_one
  set rho : ℝ := rho' / a with hrho_def
  set x : ℝ := x' / a with hx_def
  set r : ℝ := r' / a with hr_def
  have hδ_rho : δ ≤ rho := by
    have h : a * δ ≤ rho' := hdelta'_rho
    calc
      δ = (a * δ) / a := by field_simp [ha_pos.ne']
      _ ≤ rho' / a := by gcongr
  have hrho_one : rho ≤ 1 := by
    have h : rho' / a ≤ rho' := by
      have h3 : rho' / a ≤ rho' / 1 := by gcongr
      simpa using h3
    exact h.trans hrho'_one
  have hrho_r : rho ≤ r := by
    dsimp only [rho, r]
    gcongr
  have hr_one : r ≤ 1 := by
    have h : r' / a ≤ r' := by
      have h3 : r' / a ≤ r' / 1 := by
        gcongr
        linarith
      simpa using h3
    exact h.trans hr'_one
  have h_image_inter :
      (fun x : ℝ => a * x) '' (E ∩ Metric.closedBall x r) =
        ((fun x : ℝ => a * x) '' E) ∩ Metric.closedBall x' r' := by
    have h1 : a * x = x' := by
      simp [hx_def]
      field_simp [ha_pos.ne']
    have h2 : a * r = r' := by
      simp [hr_def]
      field_simp [ha_pos.ne']
    rw [dilation_inter_closedBall ha_pos, h1, h2]
  have h_rho'_eq : a * rho = rho' := by
    simp [hrho_def]
    field_simp [ha_pos.ne']
  have hrho_nonneg : 0 ≤ rho := by positivity
  let eps_nn : NNReal := ⟨rho, hrho_nonneg⟩
  let a_eps_nn : NNReal := ⟨a * (eps_nn : ℝ), by positivity⟩
  have h6 : a_eps_nn = ⟨rho', hrho'⟩ := by
    apply NNReal.coe_injective
    have h_coe : (a_eps_nn : ℝ) = a * (eps_nn : ℝ) := by rfl
    rw [h_coe]
    have h_eps : (eps_nn : ℝ) = rho := by rfl
    rw [h_eps, h_rho'_eq]
    rfl
  have h7 :
      Metric.externalCoveringNumber a_eps_nn
          ((fun x : ℝ => a * x) '' (E ∩ Metric.closedBall x r)) =
        Metric.externalCoveringNumber eps_nn
          (E ∩ Metric.closedBall x r) :=
    externalCoveringNumber_dilation_eq (a := a) (ha := ha_pos)
      (ε := eps_nn)
  have h_dil :
      Metric.externalCoveringNumber ⟨rho', hrho'⟩
          (((fun x : ℝ => a * x) '' E) ∩ Metric.closedBall x' r') =
        Metric.externalCoveringNumber eps_nn
          (E ∩ Metric.closedBall x r) := by
    rw [h6] at h7
    rw [h_image_inter] at h7
    exact h7
  rw [h_dil]
  have h_ratio : r / rho = r' / rho' := by
    simp only [hr_def, hrho_def]
    field_simp [ha_pos.ne']
  have hresult :=
    hcover rho (by positivity) hδ_rho hrho_one x r hrho_r hr_one
  rw [h_ratio] at hresult
  exact hresult

/-- Coarsen the base scale of `IsADSet1`. -/
lemma IsADSet1.coarsen_scale
    {E : Set ℝ} {δ δ' α : ℝ} {C : ENNReal}
    (hE : IsADSet1 E δ α C)
    (hδ'_pos : 0 < δ') (h : δ ≤ δ') (_hδ'_one : δ' ≤ 1) :
    IsADSet1 E δ' α C := by
  rcases hE with ⟨_hδ, hα, hα_one, hC, hbound, hcover⟩
  refine ⟨hδ'_pos, hα, hα_one, hC, hbound, ?_⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  have hδ_rho : δ ≤ rho := le_trans h hdelta_rho
  exact hcover rho hrho hδ_rho hrho_one x r hrho_r hr_one

/-- Scalar projection under anchored unit rescaling is a translation. -/
lemma scalarProjection_anchored_transport
    {delta : ℝ} {anchor : Kakeya.DeltaTube delta}
    {rho : ℝ} {hrho : 0 < rho}
    {E : Set Point3} {v : Point3} :
    scalarProjection (wz1AnchoredUnitRescalingNormalLinear anchor rho v)
        (wz1AnchoredUnitRescalingMap anchor rho hrho '' E) =
    (fun x : ℝ =>
      x - inner ℝ
        (anchor.base + (1 / 2 : ℝ) • anchor.direction) v) ''
      scalarProjection v E := by
  let center : Point3 :=
    anchor.base + (1 / 2 : ℝ) • anchor.direction
  let L := wz1AnchoredUnitRescalingLinear anchor rho
  let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
  let Φ := wz1AnchoredUnitRescalingMap anchor rho hrho
  have hΦ_eq : ∀ p : Point3, Φ p = L (p - center) := by
    intro p
    rfl
  have hinner :
      ∀ p : Point3,
        inner ℝ (Φ p) Nv = inner ℝ p v - inner ℝ center v := by
    intro p
    have h1 : Φ p = L (p - center) := hΦ_eq p
    rw [h1]
    have h2 : L (p - center) = L p - L center := map_sub L p center
    rw [h2, inner_sub_left]
    have h4 : inner ℝ (L p) Nv = inner ℝ p v :=
      inner_wz1AnchoredUnitRescalingLinear_normal anchor rho hrho p v
    have h5 : inner ℝ (L center) Nv = inner ℝ center v :=
      inner_wz1AnchoredUnitRescalingLinear_normal
        anchor rho hrho center v
    rw [h4, h5]
  ext y
  simp only [scalarProjection, Set.mem_image]
  constructor
  · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨inner ℝ p v, ⟨p, hp, rfl⟩, ?_⟩
    simpa [center, Nv, Φ] using (hinner p).symm
  · rintro ⟨u, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨Φ p, ⟨p, hp, rfl⟩, ?_⟩
    simpa [center, Nv, Φ] using hinner p

/-- Transport scalar-projection AD through anchored unit rescaling, normalize
the normal, and weaken the base scale to `rho`. -/
lemma transport_and_normalize_ad
    {E : Set Point3} {v : Point3}
    {rho sourceDelta sigma : ℝ} {C : ENNReal}
    (hrho : 0 < rho)
    (anchor : Kakeya.DeltaTube sourceDelta)
    (hAD : IsADSet1 (scalarProjection v E) (rho ^ 2) (1 - sigma) C)
    (h_image_ball :
      (wz1AnchoredUnitRescalingMap anchor rho hrho '' E) ⊆
        Metric.closedBall 0 1)
    (hNv_le_one :
      ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖ ≤ 1)
    (hNv_ge_rho :
      rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖)
    (hsigma_pos : 0 < sigma) (hsigma_one : sigma < 1)
    (hC : 1 ≤ C) :
    let Nv :=
      wz1AnchoredUnitRescalingNormalLinear anchor rho v
    let n := (1 / ‖Nv‖) • Nv
    IsADSet1
      (scalarProjection n
        (wz1AnchoredUnitRescalingMap anchor rho hrho '' E))
      rho (1 - sigma) C := by
  let Nv := wz1AnchoredUnitRescalingNormalLinear anchor rho v
  let n : Point3 := (1 / ‖Nv‖) • Nv
  let Φ := wz1AnchoredUnitRescalingMap anchor rho hrho
  have hNv_pos : 0 < ‖Nv‖ := by
    by_contra h
    have h' : ‖Nv‖ = 0 := by linarith
    have h'' : Nv = 0 := by simpa [norm_eq_zero] using h'
    have h3 :
        ‖(wz1AnchoredUnitRescalingNormalLinear anchor rho) v‖ = 0 := by
      simpa [Nv] using congr_arg norm h''
    rw [h3] at hNv_ge_rho
    linarith
  have hNv_ge_rho' : rho ≤ ‖Nv‖ := by simpa [Nv] using hNv_ge_rho
  have hNv_le_one' : ‖Nv‖ ≤ 1 := by simpa [Nv] using hNv_le_one
  set a : ℝ := 1 / ‖Nv‖ with ha_def
  have ha_ge_one : 1 ≤ a := by
    rw [ha_def, one_le_div (by positivity)]
    exact hNv_le_one'
  have ha_pos : 0 < a := by positivity
  let S := scalarProjection v E
  let S_trans := scalarProjection Nv (Φ '' E)
  have h_trans_eq :
      S_trans =
        (fun x : ℝ =>
          x - inner ℝ
            (anchor.base + (1 / 2 : ℝ) • anchor.direction) v) '' S :=
    scalarProjection_anchored_transport
      (anchor := anchor) (rho := rho) (hrho := hrho)
      (E := E) (v := v)
  have hbound_trans : S_trans ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    have h2 : |inner ℝ q Nv| ≤ ‖q‖ * ‖Nv‖ :=
      abs_real_inner_le_norm q Nv
    have h3 : ‖q‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using h_image_ball hq
    have h4 : |inner ℝ q Nv| ≤ 1 := by
      calc
        |inner ℝ q Nv| ≤ ‖q‖ * ‖Nv‖ := h2
        _ ≤ 1 * ‖Nv‖ := by gcongr
        _ ≤ 1 := by linarith
    exact abs_le.mp (h4.trans (by norm_num))
  have hAD_trans : IsADSet1 S_trans (rho ^ 2) (1 - sigma) C := by
    rcases hAD with ⟨hδ, hα, hα_one, hC', _hbound_src, hcover⟩
    let c :=
      inner ℝ (anchor.base + (1 / 2 : ℝ) • anchor.direction) v
    have h_eq : S_trans = (fun x : ℝ => x - c) '' S := h_trans_eq
    have h_main :
        IsADSet1 ((fun x : ℝ => x - c) '' S)
          (rho ^ 2) (1 - sigma) C := by
      refine ⟨hδ, hα, hα_one, hC', ?_, ?_⟩
      · rw [←h_eq]
        exact hbound_trans
      · intro rho' hrho' hdelta_rho hrho_one x r hrho_r hr_one
        let x' := x + c
        have h_ball :
            (fun t : ℝ => t - c) '' (S ∩ Metric.closedBall x' r) =
              ((fun t : ℝ => t - c) '' S) ∩
                Metric.closedBall x r := by
          have h_inj : Function.Injective (fun t : ℝ => t - c) := by
            intro u v h
            simpa using h
          rw [Set.image_inter h_inj]
          have h_ball2 :
              (fun t : ℝ => t - c) '' Metric.closedBall x' r =
                Metric.closedBall x r := by
            ext z
            simp only [Set.mem_image, Metric.mem_closedBall]
            constructor
            · rintro ⟨y, hy, rfl⟩
              have h9 : dist (y - c) x = dist y x' := by
                have h10 : (y - c) - x = y - (x + c) := by ring
                simp [dist_eq_norm, Real.norm_eq_abs, x', h10]
              rw [h9]
              exact hy
            · intro hz
              have h_goal1 : dist (z + c) x' ≤ r := by
                have h9 : dist (z + c) x' = dist z x := by
                  have h10 : (z + c) - (x + c) = z - x := by ring
                  simp [dist_eq_norm, Real.norm_eq_abs, x', h10]
                rw [h9]
                exact hz
              have h_goal2 : (z + c) - c = z := by ring
              exact ⟨z + c, h_goal1, h_goal2⟩
          rw [h_ball2]
        have h_trans_cover :
            Metric.externalCoveringNumber ⟨rho', hrho'⟩
                (((fun t : ℝ => t - c) '' S) ∩
                  Metric.closedBall x r) =
              Metric.externalCoveringNumber ⟨rho', hrho'⟩
                (S ∩ Metric.closedBall x' r) := by
          rw [←h_ball]
          exact
            translation_externalCoveringNumber c
              (S ∩ Metric.closedBall x' r) ⟨rho', hrho'⟩
        rw [h_trans_cover]
        exact hcover rho' hrho' hdelta_rho hrho_one x' r hrho_r hr_one
    rw [h_eq]
    exact h_main
  let S_norm := scalarProjection n (Φ '' E)
  have h_norm_eq : S_norm = (fun x : ℝ => a * x) '' S_trans := by
    ext y
    simp only [S_norm, scalarProjection, Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h1 :
          inner ℝ p n = (1 / ‖Nv‖) * inner ℝ p Nv := by
        simp [n, inner_smul_right]
      refine ⟨inner ℝ p Nv, ⟨p, hp, rfl⟩, ?_⟩
      rw [h1, ha_def]
    · rintro ⟨u, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p, hp, ?_⟩
      have h1 :
          inner ℝ p n = (1 / ‖Nv‖) * inner ℝ p Nv := by
        simp [n, inner_smul_right]
      rw [h1, ha_def]
  have hbound_norm : S_norm ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    have h2 : |inner ℝ q n| ≤ ‖q‖ * ‖n‖ :=
      abs_real_inner_le_norm q n
    have h3 : ‖n‖ = 1 := by
      have h4 : ‖n‖ = |(1 / ‖Nv‖)| * ‖Nv‖ := by
        simpa [n] using norm_smul (1 / ‖Nv‖) Nv
      rw [h4]
      have h5 : |(1 / ‖Nv‖)| = 1 / ‖Nv‖ := by
        rw [abs_of_pos]
        positivity
      rw [h5]
      field_simp [hNv_pos.ne']
    have h4 : ‖q‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using h_image_ball hq
    rw [h3] at h2
    have h5 : |inner ℝ q n| ≤ 1 := by linarith
    exact abs_le.mp (h5.trans (by norm_num))
  have hbound_dil :
      (fun x : ℝ => a * x) '' S_trans ⊆ Set.Icc (-4 : ℝ) 4 := by
    rw [←h_norm_eq]
    exact hbound_norm
  have hδ2_pos : 0 < rho ^ 2 := by positivity
  have hα_pos : 0 < 1 - sigma := by linarith
  have hα_one : 1 - sigma ≤ 1 := by linarith
  have h_new_scale_le_one : a * rho ^ 2 ≤ 1 := by
    have h1 : a ≤ 1 / rho := by
      rw [ha_def]
      gcongr
    calc
      a * rho ^ 2 ≤ (1 / rho) * rho ^ 2 := by gcongr
      _ = rho := by field_simp [hrho.ne']
      _ ≤ 1 := by nlinarith
  have hAD_dil :
      IsADSet1 S_norm (a * rho ^ 2) (1 - sigma) C := by
    have h :
        IsADSet1 ((fun x : ℝ => a * x) '' S_trans)
          (a * rho ^ 2) (1 - sigma) C :=
      hAD_trans.dilation_ge_one ha_ge_one hbound_dil
        h_new_scale_le_one hδ2_pos hα_pos hα_one hC
    exact h_norm_eq ▸ h
  have h_scale_le : a * rho ^ 2 ≤ rho := by
    have h1 : a ≤ 1 / rho := by
      rw [ha_def]
      gcongr
    calc
      a * rho ^ 2 ≤ (1 / rho) * rho ^ 2 := by gcongr
      _ = rho := by field_simp [hrho.ne']
  exact hAD_dil.coarsen_scale hrho h_scale_le (by nlinarith)

end Kakeya.Assouad
